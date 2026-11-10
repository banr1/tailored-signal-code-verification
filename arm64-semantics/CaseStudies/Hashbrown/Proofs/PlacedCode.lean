/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Spec
public import CaseStudies.Hashbrown.Generated.HashbrownPlacedObj
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.Placed.Transfer
public import ProofLib.Placed.Multi
public import ProofLib.SepLogic

/-!
# Multi-Block Placed Code and Read-Only Data

Placement-generic `HbPlaced` bundle, `WordTree`-backed instruction fetch and `fnOff` reflection
across all 13 blocks of `hashbrownLib`, and read-only static empty-table `.rodata` extraction
(`hbRodata`).
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open CaseStudies.Hashbrown

/-! ## Placed Program Bundle -/

def mplAsPl (mpl : Obj.MultiPlacement) : Obj.Placement :=
  hashbrownLib.blockPlacement mpl 0

def hbLib0  : Obj.PlacedLib := hashbrownLib.blockLib 0
def hbLib1  : Obj.PlacedLib := hashbrownLib.blockLib 1
def hbLib2  : Obj.PlacedLib := hashbrownLib.blockLib 2
def hbLib3  : Obj.PlacedLib := hashbrownLib.blockLib 3
def hbLib4  : Obj.PlacedLib := hashbrownLib.blockLib 4
def hbLib5  : Obj.PlacedLib := hashbrownLib.blockLib 5
def hbLib6  : Obj.PlacedLib := hashbrownLib.blockLib 6
def hbLib7  : Obj.PlacedLib := hashbrownLib.blockLib 7
def hbLib8  : Obj.PlacedLib := hashbrownLib.blockLib 8
def hbLib9  : Obj.PlacedLib := hashbrownLib.blockLib 9
def hbLib10 : Obj.PlacedLib := hashbrownLib.blockLib 10
def hbLib11 : Obj.PlacedLib := hashbrownLib.blockLib 11
def hbLib12 : Obj.PlacedLib := hashbrownLib.blockLib 12

@[simp] theorem hashbrownLib_blocks_length : hashbrownLib.blocks.length = 13 := rfl

structure HbPlaced where
  mpl : Obj.MultiPlacement
  mplPlaceable : hashbrownLib.Placeable mpl

def HbPlaced.pl   (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 0
def HbPlaced.pl1  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 1
def HbPlaced.pl2  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 2
def HbPlaced.pl3  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 3
def HbPlaced.pl4  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 4
def HbPlaced.pl5  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 5
def HbPlaced.pl6  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 6
def HbPlaced.pl7  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 7
def HbPlaced.pl8  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 8
def HbPlaced.pl9  (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 9
def HbPlaced.pl10 (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 10
def HbPlaced.pl11 (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 11
def HbPlaced.pl12 (P : HbPlaced) : Obj.Placement := hashbrownLib.blockPlacement P.mpl 12

@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl1_ρ  (P : HbPlaced) : P.pl1.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl2_ρ  (P : HbPlaced) : P.pl2.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl3_ρ  (P : HbPlaced) : P.pl3.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl4_ρ  (P : HbPlaced) : P.pl4.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl5_ρ  (P : HbPlaced) : P.pl5.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl6_ρ  (P : HbPlaced) : P.pl6.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl7_ρ  (P : HbPlaced) : P.pl7.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl8_ρ  (P : HbPlaced) : P.pl8.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl9_ρ  (P : HbPlaced) : P.pl9.ρ  = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl10_ρ (P : HbPlaced) : P.pl10.ρ = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl11_ρ (P : HbPlaced) : P.pl11.ρ = P.pl.ρ := rfl
@[simp, arm64_norm, wp_norm] theorem HbPlaced.pl12_ρ (P : HbPlaced) : P.pl12.ρ = P.pl.ρ := rfl

theorem HbPlaced.placeable  (P : HbPlaced) : hbLib0.Placeable P.pl   := hashbrownLib.placeable_blockLib (i := 0)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable1 (P : HbPlaced) : hbLib1.Placeable P.pl1  := hashbrownLib.placeable_blockLib (i := 1)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable2 (P : HbPlaced) : hbLib2.Placeable P.pl2  := hashbrownLib.placeable_blockLib (i := 2)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable3 (P : HbPlaced) : hbLib3.Placeable P.pl3  := hashbrownLib.placeable_blockLib (i := 3)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable4 (P : HbPlaced) : hbLib4.Placeable P.pl4  := hashbrownLib.placeable_blockLib (i := 4)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable5 (P : HbPlaced) : hbLib5.Placeable P.pl5  := hashbrownLib.placeable_blockLib (i := 5)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable6 (P : HbPlaced) : hbLib6.Placeable P.pl6  := hashbrownLib.placeable_blockLib (i := 6)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable7 (P : HbPlaced) : hbLib7.Placeable P.pl7  := hashbrownLib.placeable_blockLib (i := 7)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable8 (P : HbPlaced) : hbLib8.Placeable P.pl8  := hashbrownLib.placeable_blockLib (i := 8)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable9 (P : HbPlaced) : hbLib9.Placeable P.pl9  := hashbrownLib.placeable_blockLib (i := 9)  (by decide) P.mplPlaceable
theorem HbPlaced.placeable10 (P : HbPlaced) : hbLib10.Placeable P.pl10 := hashbrownLib.placeable_blockLib (i := 10) (by decide) P.mplPlaceable
theorem HbPlaced.placeable11 (P : HbPlaced) : hbLib11.Placeable P.pl11 := hashbrownLib.placeable_blockLib (i := 11) (by decide) P.mplPlaceable
theorem HbPlaced.placeable12 (P : HbPlaced) : hbLib12.Placeable P.pl12 := hashbrownLib.placeable_blockLib (i := 12) (by decide) P.mplPlaceable

noncomputable def hbProg   (P : HbPlaced) : Program := hbLib0.program P.pl
noncomputable def hbProg1  (P : HbPlaced) : Program := hbLib1.program P.pl1
noncomputable def hbProg2  (P : HbPlaced) : Program := hbLib2.program P.pl2
noncomputable def hbProg3  (P : HbPlaced) : Program := hbLib3.program P.pl3
noncomputable def hbProg4  (P : HbPlaced) : Program := hbLib4.program P.pl4
noncomputable def hbProg5  (P : HbPlaced) : Program := hbLib5.program P.pl5
noncomputable def hbProg6  (P : HbPlaced) : Program := hbLib6.program P.pl6
noncomputable def hbProg7  (P : HbPlaced) : Program := hbLib7.program P.pl7
noncomputable def hbProg8  (P : HbPlaced) : Program := hbLib8.program P.pl8
noncomputable def hbProg9  (P : HbPlaced) : Program := hbLib9.program P.pl9
noncomputable def hbProg10 (P : HbPlaced) : Program := hbLib10.program P.pl10
noncomputable def hbProg11 (P : HbPlaced) : Program := hbLib11.program P.pl11
noncomputable def hbProg12 (P : HbPlaced) : Program := hbLib12.program P.pl12

private theorem program_rebase_aux (b : BitVec 64) (c : List (BitVec 8))
    (syms st : List (String × Nat))
    (X O : String → Option (State → State)) :
    Program.rebase { base := b, code := c, symbols := syms, stubs := st } b X O =
      { base := b, code := c, symbols := syms, stubs := st, externs := X, overrides := O } := rfl

/-- Rewrites `((hashbrownLib.blockLib i).program (hashbrownLib.blockPlacement P.mpl i)).rebase ...`
    to `hashbrownLib.blockProgram P.mpl i X O`. Omitted from `@[simp]` so `simp` and `arm64_norm`
    keep the `.rebase b X` shape expected by `wp_entry`, `wp_steps`, `sym_block`, and
    `*_pairStep_0x*`. -/
theorem hbBlockProg_rebase (P : HbPlaced) (i : Nat)
    (X : String → Option (State → State) := fun _ => none)
    (O : String → Option (State → State) := fun _ => none) :
    ((hashbrownLib.blockLib i).program (hashbrownLib.blockPlacement P.mpl i)).rebase
        (hashbrownLib.blockPlacement P.mpl i).base X O =
      hashbrownLib.blockProgram P.mpl i X O :=
  let lib := hashbrownLib.blockLib i
  let pl := hashbrownLib.blockPlacement P.mpl i
  program_rebase_aux pl.base (lib.text.patched pl) lib.text.symbols
    (lib.text.externs.map fun e => (e, (pl.ρ e - pl.base).toNat)) X O

theorem hbProg_rebase   (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg P).rebase P.pl.base X O     = hashbrownLib.blockProgram P.mpl 0 X O  := hbBlockProg_rebase P 0 X O
theorem hbProg1_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg1 P).rebase P.pl1.base X O   = hashbrownLib.blockProgram P.mpl 1 X O  := hbBlockProg_rebase P 1 X O
theorem hbProg2_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg2 P).rebase P.pl2.base X O   = hashbrownLib.blockProgram P.mpl 2 X O  := hbBlockProg_rebase P 2 X O
theorem hbProg3_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg3 P).rebase P.pl3.base X O   = hashbrownLib.blockProgram P.mpl 3 X O  := hbBlockProg_rebase P 3 X O
theorem hbProg4_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg4 P).rebase P.pl4.base X O   = hashbrownLib.blockProgram P.mpl 4 X O  := hbBlockProg_rebase P 4 X O
theorem hbProg5_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg5 P).rebase P.pl5.base X O   = hashbrownLib.blockProgram P.mpl 5 X O  := hbBlockProg_rebase P 5 X O
theorem hbProg6_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg6 P).rebase P.pl6.base X O   = hashbrownLib.blockProgram P.mpl 6 X O  := hbBlockProg_rebase P 6 X O
theorem hbProg7_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg7 P).rebase P.pl7.base X O   = hashbrownLib.blockProgram P.mpl 7 X O  := hbBlockProg_rebase P 7 X O
theorem hbProg8_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg8 P).rebase P.pl8.base X O   = hashbrownLib.blockProgram P.mpl 8 X O  := hbBlockProg_rebase P 8 X O
theorem hbProg9_rebase  (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg9 P).rebase P.pl9.base X O   = hashbrownLib.blockProgram P.mpl 9 X O  := hbBlockProg_rebase P 9 X O
theorem hbProg10_rebase (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg10 P).rebase P.pl10.base X O = hashbrownLib.blockProgram P.mpl 10 X O := hbBlockProg_rebase P 10 X O
theorem hbProg11_rebase (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg11 P).rebase P.pl11.base X O = hashbrownLib.blockProgram P.mpl 11 X O := hbBlockProg_rebase P 11 X O
theorem hbProg12_rebase (P : HbPlaced) (X O : String → Option (State → State) := fun _ => none) :
    (hbProg12 P).rebase P.pl12.base X O = hashbrownLib.blockProgram P.mpl 12 X O := hbBlockProg_rebase P 12 X O

theorem mplAsPl_eq (mpl : Obj.MultiPlacement) :
    mplAsPl mpl = hashbrownLib.blockPlacement mpl 0 := rfl

theorem hbPl_eq_mplAsPl (P : HbPlaced) : P.pl = mplAsPl P.mpl := rfl

theorem hbPl0_eq  (P : HbPlaced) : P.pl   = hashbrownLib.blockPlacement P.mpl 0  := rfl
theorem hbPl1_eq  (P : HbPlaced) : P.pl1  = hashbrownLib.blockPlacement P.mpl 1  := rfl
theorem hbPl2_eq  (P : HbPlaced) : P.pl2  = hashbrownLib.blockPlacement P.mpl 2  := rfl
theorem hbPl3_eq  (P : HbPlaced) : P.pl3  = hashbrownLib.blockPlacement P.mpl 3  := rfl
theorem hbPl4_eq  (P : HbPlaced) : P.pl4  = hashbrownLib.blockPlacement P.mpl 4  := rfl
theorem hbPl5_eq  (P : HbPlaced) : P.pl5  = hashbrownLib.blockPlacement P.mpl 5  := rfl
theorem hbPl6_eq  (P : HbPlaced) : P.pl6  = hashbrownLib.blockPlacement P.mpl 6  := rfl
theorem hbPl7_eq  (P : HbPlaced) : P.pl7  = hashbrownLib.blockPlacement P.mpl 7  := rfl
theorem hbPl8_eq  (P : HbPlaced) : P.pl8  = hashbrownLib.blockPlacement P.mpl 8  := rfl
theorem hbPl9_eq  (P : HbPlaced) : P.pl9  = hashbrownLib.blockPlacement P.mpl 9  := rfl
theorem hbPl10_eq (P : HbPlaced) : P.pl10 = hashbrownLib.blockPlacement P.mpl 10 := rfl
theorem hbPl11_eq (P : HbPlaced) : P.pl11 = hashbrownLib.blockPlacement P.mpl 11 := rfl
theorem hbPl12_eq (P : HbPlaced) : P.pl12 = hashbrownLib.blockPlacement P.mpl 12 := rfl

abbrev hbReserveRehashSym : String :=
  "<hashbrown::raw::RawTable<(u64, u64)>>::reserve_rehash::<hashbrown::map::make_hasher<u64, u64, hashbrown_verified::FxBuildHasher>::{closure#0}>"

abbrev hbCapOverflowSym : String :=
  "<hashbrown::raw::Fallibility>::capacity_overflow"

abbrev hbFallibilityAllocErrSym : String :=
  "<hashbrown::raw::Fallibility>::alloc_err"

set_option maxRecDepth 200000 in
@[simp, arm64_norm, wp_norm] theorem hbPl_ρ_reserveRehash (P : HbPlaced) :
    P.pl.ρ hbReserveRehashSym = P.pl.base := by
  have h : Obj.lookupBlockSym hbReserveRehashSym hashbrownLib.blocks = some (0, 0) := by decide
  simp [HbPlaced.pl, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]

set_option maxRecDepth 200000 in
@[simp, arm64_norm, wp_norm] theorem hbPl_ρ_capOverflow (P : HbPlaced) :
    P.pl.ρ hbCapOverflowSym = P.pl11.base := by
  have h : Obj.lookupBlockSym hbCapOverflowSym hashbrownLib.blocks = some (11, 0) := by decide
  simp [HbPlaced.pl, HbPlaced.pl11, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]

set_option maxRecDepth 200000 in
@[simp, arm64_norm, wp_norm] theorem hbPl_ρ_allocErr (P : HbPlaced) :
    P.pl.ρ hbFallibilityAllocErrSym = P.pl12.base := by
  have h : Obj.lookupBlockSym hbFallibilityAllocErrSym hashbrownLib.blocks = some (12, 0) := by decide
  simp [HbPlaced.pl, HbPlaced.pl12, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, h]

theorem hbMultiSubroutineOk_of_withCL {α : Type} (fnName : String) (i : Nat) {off : Nat}
    {progOf : HbPlaced → Program} {plOf : HbPlaced → Obj.Placement}
    (hreb : ∀ P : HbPlaced, ∀ X, (progOf P).rebase (plOf P).base X = hashbrownLib.blockProgram P.mpl i X)
    (spec : Obj.MultiPlacement → Spec α)
    (X : String → Option (State → State) := fun _ => none)
    (hexp : fnName ∈ hashbrownLib.exports := by decide)
    (hlookMulti : Obj.lookupBlockSym fnName hashbrownLib.blocks = some (i, off) := by decide)
    (hlookBlk : Obj.lookup fnName (hashbrownLib.blockLib i).text.symbols = some off := by decide)
    (hok : ∀ P : HbPlaced,
      let prog := (progOf P).rebase (plOf P).base X
      subroutine_ok prog (prog.fnAddr fnName)
        (hashbrownLib.withCodeLoaded P.mpl (spec P.mpl))) :
    hashbrownLib.subroutineOk fnName spec X := by
  refine ⟨hexp, i, off, hlookMulti, fun mpl hMpl => ?_⟩
  have h := hok ⟨mpl, hMpl⟩
  dsimp only at h
  rw [hreb ⟨mpl, hMpl⟩ X] at h
  have hfn : (hashbrownLib.blockProgram mpl i X).fnAddr fnName =
      hashbrownLib.fnAddr mpl fnName := by
    unfold MultiPlacedLib.blockProgram
    rw [(PlacedLib.fnAddr_program (lib := hashbrownLib.blockLib i)
      (pl := hashbrownLib.blockPlacement mpl i) (X := X) hlookBlk).1]
    simp [PlacedLib.fnAddr, MultiPlacedLib.fnAddr, MultiPlacedLib.blockPlacement, hlookBlk, hlookMulti]
  rwa [hfn] at h

theorem hbMultiSubroutineOk_of_plain {α : Type} (fnName : String) (i : Nat) {off : Nat}
    {progOf : HbPlaced → Program} {plOf : HbPlaced → Obj.Placement}
    (hreb : ∀ P : HbPlaced, ∀ X, (progOf P).rebase (plOf P).base X = hashbrownLib.blockProgram P.mpl i X)
    (spec : Obj.MultiPlacement → Spec α)
    (X : String → Option (State → State) := fun _ => none)
    (hexp : fnName ∈ hashbrownLib.exports := by decide)
    (hlookMulti : Obj.lookupBlockSym fnName hashbrownLib.blocks = some (i, off) := by decide)
    (hlookBlk : Obj.lookup fnName (hashbrownLib.blockLib i).text.symbols = some off := by decide)
    (hok : ∀ P : HbPlaced,
      let prog := (progOf P).rebase (plOf P).base X
      subroutine_ok prog (prog.fnAddr fnName) (spec P.mpl)) :
    hashbrownLib.subroutineOk fnName spec X := by
  refine hbMultiSubroutineOk_of_withCL fnName i hreb spec X hexp hlookMulti hlookBlk fun P => ?_
  refine subroutine_ok_mono_entails (hok P) (fun _ _ => ?_) (fun _ _ _ => Entails.refl _)
  dsimp only [MultiPlacedLib.withCodeLoaded]
  rw [sepConj_comm]
  exact Entails.pure_left fun _ => Entails.refl _

@[simp] theorem hbProg_base   (P : HbPlaced) : (hbProg P).base   = P.pl.base   := rfl
@[simp] theorem hbProg1_base  (P : HbPlaced) : (hbProg1 P).base  = P.pl1.base  := rfl
@[simp] theorem hbProg2_base  (P : HbPlaced) : (hbProg2 P).base  = P.pl2.base  := rfl
@[simp] theorem hbProg3_base  (P : HbPlaced) : (hbProg3 P).base  = P.pl3.base  := rfl
@[simp] theorem hbProg4_base  (P : HbPlaced) : (hbProg4 P).base  = P.pl4.base  := rfl
@[simp] theorem hbProg5_base  (P : HbPlaced) : (hbProg5 P).base  = P.pl5.base  := rfl
@[simp] theorem hbProg6_base  (P : HbPlaced) : (hbProg6 P).base  = P.pl6.base  := rfl
@[simp] theorem hbProg7_base  (P : HbPlaced) : (hbProg7 P).base  = P.pl7.base  := rfl
@[simp] theorem hbProg8_base  (P : HbPlaced) : (hbProg8 P).base  = P.pl8.base  := rfl
@[simp] theorem hbProg9_base  (P : HbPlaced) : (hbProg9 P).base  = P.pl9.base  := rfl
@[simp] theorem hbProg10_base (P : HbPlaced) : (hbProg10 P).base = P.pl10.base := rfl
@[simp] theorem hbProg11_base (P : HbPlaced) : (hbProg11 P).base = P.pl11.base := rfl
@[simp] theorem hbProg12_base (P : HbPlaced) : (hbProg12 P).base = P.pl12.base := rfl

section Reflection
set_option maxRecDepth 200000

-- Block 0: `reserve_rehash` (1136 B = 284 words)
def hbRawProg0 : Program := { code := hashbrownPlacedCode0, symbols := hbLib0.text.symbols }
def hbTree0 : WordTree := word_tree_of% hbRawProg0
theorem hbCode0_eq : hbLib0.text.code = hbTree0.toBytes := rfl
theorem hbTree0_size : hbTree0.checkSize? = some 284 := rfl
def hbCharSyms0 : List (List Char × Nat) := sym_chars_of% hbRawProg0
theorem hbSyms0_eq : hbLib0.text.symbols = toStringSymbols hbCharSyms0 := rfl
theorem hbSyms0_fresh : allFreshCharSymbols hbCharSyms0 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg hbLib0 hbTree0 hbCode0_eq hbTree0_size
  via_placement HbPlaced.pl HbPlaced.placeable [0 → 0x46c]
gen_placed_fnOffs hbProg hbLib0 hbCharSyms0 hbSyms0_eq hbSyms0_fresh

-- Block 1: `hashbrown_clear` (96 B = 24 words)
def hbRawProg1 : Program := { code := hashbrownPlacedCode1, symbols := hbLib1.text.symbols }
def hbTree1 : WordTree := word_tree_of% hbRawProg1
theorem hbCode1_eq : hbLib1.text.code = hbTree1.toBytes := rfl
theorem hbTree1_size : hbTree1.checkSize? = some 24 := rfl
def hbCharSyms1 : List (List Char × Nat) := sym_chars_of% hbRawProg1
theorem hbSyms1_eq : hbLib1.text.symbols = toStringSymbols hbCharSyms1 := rfl
theorem hbSyms1_fresh : allFreshCharSymbols hbCharSyms1 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg1 hbLib1 hbTree1 hbCode1_eq hbTree1_size
  via_placement HbPlaced.pl1 HbPlaced.placeable1 [0 → 0x5c]
gen_placed_fnOffs hbProg1 hbLib1 hbCharSyms1 hbSyms1_eq hbSyms1_fresh

-- Block 2: `hashbrown_contains_key` (164 B = 41 words)
def hbRawProg2 : Program := { code := hashbrownPlacedCode2, symbols := hbLib2.text.symbols }
def hbTree2 : WordTree := word_tree_of% hbRawProg2
theorem hbCode2_eq : hbLib2.text.code = hbTree2.toBytes := rfl
theorem hbTree2_size : hbTree2.checkSize? = some 41 := rfl
def hbCharSyms2 : List (List Char × Nat) := sym_chars_of% hbRawProg2
theorem hbSyms2_eq : hbLib2.text.symbols = toStringSymbols hbCharSyms2 := rfl
theorem hbSyms2_fresh : allFreshCharSymbols hbCharSyms2 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg2 hbLib2 hbTree2 hbCode2_eq hbTree2_size
  via_placement HbPlaced.pl2 HbPlaced.placeable2 [0 → 0xa0]
gen_placed_fnOffs hbProg2 hbLib2 hbCharSyms2 hbSyms2_eq hbSyms2_fresh

-- Block 3: `hashbrown_drop` (44 B = 11 words)
def hbRawProg3 : Program := { code := hashbrownPlacedCode3, symbols := hbLib3.text.symbols }
def hbTree3 : WordTree := word_tree_of% hbRawProg3
theorem hbCode3_eq : hbLib3.text.code = hbTree3.toBytes := rfl
theorem hbTree3_size : hbTree3.checkSize? = some 11 := rfl
def hbCharSyms3 : List (List Char × Nat) := sym_chars_of% hbRawProg3
theorem hbSyms3_eq : hbLib3.text.symbols = toStringSymbols hbCharSyms3 := rfl
theorem hbSyms3_fresh : allFreshCharSymbols hbCharSyms3 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg3 hbLib3 hbTree3 hbCode3_eq hbTree3_size
  via_placement HbPlaced.pl3 HbPlaced.placeable3 [0 → 0x28]
gen_placed_fnOffs hbProg3 hbLib3 hbCharSyms3 hbSyms3_eq hbSyms3_fresh

-- Block 4: `hashbrown_get` (168 B = 42 words)
def hbRawProg4 : Program := { code := hashbrownPlacedCode4, symbols := hbLib4.text.symbols }
def hbTree4 : WordTree := word_tree_of% hbRawProg4
theorem hbCode4_eq : hbLib4.text.code = hbTree4.toBytes := rfl
theorem hbTree4_size : hbTree4.checkSize? = some 42 := rfl
def hbCharSyms4 : List (List Char × Nat) := sym_chars_of% hbRawProg4
theorem hbSyms4_eq : hbLib4.text.symbols = toStringSymbols hbCharSyms4 := rfl
theorem hbSyms4_fresh : allFreshCharSymbols hbCharSyms4 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg4 hbLib4 hbTree4 hbCode4_eq hbTree4_size
  via_placement HbPlaced.pl4 HbPlaced.placeable4 [0 → 0xa4]
gen_placed_fnOffs hbProg4 hbLib4 hbCharSyms4 hbSyms4_eq hbSyms4_fresh

-- Block 5: `hashbrown_insert` (388 B = 97 words)
def hbRawProg5 : Program := { code := hashbrownPlacedCode5, symbols := hbLib5.text.symbols }
def hbTree5 : WordTree := word_tree_of% hbRawProg5
theorem hbCode5_eq : hbLib5.text.code = hbTree5.toBytes := rfl
theorem hbTree5_size : hbTree5.checkSize? = some 97 := rfl
def hbCharSyms5 : List (List Char × Nat) := sym_chars_of% hbRawProg5
theorem hbSyms5_eq : hbLib5.text.symbols = toStringSymbols hbCharSyms5 := rfl
theorem hbSyms5_fresh : allFreshCharSymbols hbCharSyms5 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg5 hbLib5 hbTree5 hbCode5_eq hbTree5_size
  via_placement HbPlaced.pl5 HbPlaced.placeable5 [0 → 0x180]
gen_placed_fnOffs hbProg5 hbLib5 hbCharSyms5 hbSyms5_eq hbSyms5_fresh

-- Block 6: `hashbrown_is_empty` (16 B = 4 words)
def hbRawProg6 : Program := { code := hashbrownPlacedCode6, symbols := hbLib6.text.symbols }
def hbTree6 : WordTree := word_tree_of% hbRawProg6
theorem hbCode6_eq : hbLib6.text.code = hbTree6.toBytes := rfl
theorem hbTree6_size : hbTree6.checkSize? = some 4 := rfl
def hbCharSyms6 : List (List Char × Nat) := sym_chars_of% hbRawProg6
theorem hbSyms6_eq : hbLib6.text.symbols = toStringSymbols hbCharSyms6 := rfl
theorem hbSyms6_fresh : allFreshCharSymbols hbCharSyms6 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg6 hbLib6 hbTree6 hbCode6_eq hbTree6_size
  via_placement HbPlaced.pl6 HbPlaced.placeable6 [0 → 0xc]
gen_placed_fnOffs hbProg6 hbLib6 hbCharSyms6 hbSyms6_eq hbSyms6_fresh

-- Block 7: `hashbrown_len` (8 B = 2 words)
def hbRawProg7 : Program := { code := hashbrownPlacedCode7, symbols := hbLib7.text.symbols }
def hbTree7 : WordTree := word_tree_of% hbRawProg7
theorem hbCode7_eq : hbLib7.text.code = hbTree7.toBytes := rfl
theorem hbTree7_size : hbTree7.checkSize? = some 2 := rfl
def hbCharSyms7 : List (List Char × Nat) := sym_chars_of% hbRawProg7
theorem hbSyms7_eq : hbLib7.text.symbols = toStringSymbols hbCharSyms7 := rfl
theorem hbSyms7_fresh : allFreshCharSymbols hbCharSyms7 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg7 hbLib7 hbTree7 hbCode7_eq hbTree7_size
  via_placement HbPlaced.pl7 HbPlaced.placeable7 [0 → 0x4]
gen_placed_fnOffs hbProg7 hbLib7 hbCharSyms7 hbSyms7_eq hbSyms7_fresh

-- Block 8: `hashbrown_new` (20 B = 5 words)
def hbRawProg8 : Program := { code := hashbrownPlacedCode8, symbols := hbLib8.text.symbols }
def hbTree8 : WordTree := word_tree_of% hbRawProg8
theorem hbCode8_eq : hbLib8.text.code = hbTree8.toBytes := rfl
theorem hbTree8_size : hbTree8.checkSize? = some 5 := rfl
def hbCharSyms8 : List (List Char × Nat) := sym_chars_of% hbRawProg8
theorem hbSyms8_eq : hbLib8.text.symbols = toStringSymbols hbCharSyms8 := rfl
theorem hbSyms8_fresh : allFreshCharSymbols hbCharSyms8 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg8 hbLib8 hbTree8 hbCode8_eq hbTree8_size
  via_placement HbPlaced.pl8 HbPlaced.placeable8 [0 → 0x10]
gen_placed_fnOffs hbProg8 hbLib8 hbCharSyms8 hbSyms8_eq hbSyms8_fresh

-- Block 9: `hashbrown_remove` (272 B = 68 words)
def hbRawProg9 : Program := { code := hashbrownPlacedCode9, symbols := hbLib9.text.symbols }
def hbTree9 : WordTree := word_tree_of% hbRawProg9
theorem hbCode9_eq : hbLib9.text.code = hbTree9.toBytes := rfl
theorem hbTree9_size : hbTree9.checkSize? = some 68 := rfl
def hbCharSyms9 : List (List Char × Nat) := sym_chars_of% hbRawProg9
theorem hbSyms9_eq : hbLib9.text.symbols = toStringSymbols hbCharSyms9 := rfl
theorem hbSyms9_fresh : allFreshCharSymbols hbCharSyms9 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg9 hbLib9 hbTree9 hbCode9_eq hbTree9_size
  via_placement HbPlaced.pl9 HbPlaced.placeable9 [0 → 0x10c]
gen_placed_fnOffs hbProg9 hbLib9 hbCharSyms9 hbSyms9_eq hbSyms9_fresh

-- Block 10: `hashbrown_with_capacity` (320 B = 80 words)
def hbRawProg10 : Program := { code := hashbrownPlacedCode10, symbols := hbLib10.text.symbols }
def hbTree10 : WordTree := word_tree_of% hbRawProg10
theorem hbCode10_eq : hbLib10.text.code = hbTree10.toBytes := rfl
theorem hbTree10_size : hbTree10.checkSize? = some 80 := rfl
def hbCharSyms10 : List (List Char × Nat) := sym_chars_of% hbRawProg10
theorem hbSyms10_eq : hbLib10.text.symbols = toStringSymbols hbCharSyms10 := rfl
theorem hbSyms10_fresh : allFreshCharSymbols hbCharSyms10 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg10 hbLib10 hbTree10 hbCode10_eq hbTree10_size
  via_placement HbPlaced.pl10 HbPlaced.placeable10 [0 → 0x13c]
gen_placed_fnOffs hbProg10 hbLib10 hbCharSyms10 hbSyms10_eq hbSyms10_fresh

-- Block 11: `<Fallibility>::capacity_overflow` (44 B = 11 words)
def hbRawProg11 : Program := { code := hashbrownPlacedCode11, symbols := hbLib11.text.symbols }
def hbTree11 : WordTree := word_tree_of% hbRawProg11
theorem hbCode11_eq : hbLib11.text.code = hbTree11.toBytes := rfl
theorem hbTree11_size : hbTree11.checkSize? = some 11 := rfl
def hbCharSyms11 : List (List Char × Nat) := sym_chars_of% hbRawProg11
theorem hbSyms11_eq : hbLib11.text.symbols = toStringSymbols hbCharSyms11 := rfl
theorem hbSyms11_fresh : allFreshCharSymbols hbCharSyms11 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg11 hbLib11 hbTree11 hbCode11_eq hbTree11_size
  via_placement HbPlaced.pl11 HbPlaced.placeable11 [0 → 0x28]
gen_placed_fnOffs hbProg11 hbLib11 hbCharSyms11 hbSyms11_eq hbSyms11_fresh

-- Block 12: `<Fallibility>::alloc_err` (36 B = 9 words)
def hbRawProg12 : Program := { code := hashbrownPlacedCode12, symbols := hbLib12.text.symbols }
def hbTree12 : WordTree := word_tree_of% hbRawProg12
theorem hbCode12_eq : hbLib12.text.code = hbTree12.toBytes := rfl
theorem hbTree12_size : hbTree12.checkSize? = some 9 := rfl
def hbCharSyms12 : List (List Char × Nat) := sym_chars_of% hbRawProg12
theorem hbSyms12_eq : hbLib12.text.symbols = toStringSymbols hbCharSyms12 := rfl
theorem hbSyms12_fresh : allFreshCharSymbols hbCharSyms12 = true := allFreshCharSymbols_of_sorted (by decide)

gen_placed_fetches hbProg12 hbLib12 hbTree12 hbCode12_eq hbTree12_size
  via_placement HbPlaced.pl12 HbPlaced.placeable12 [0 → 0x20]
gen_placed_fnOffs hbProg12 hbLib12 hbCharSyms12 hbSyms12_eq hbSyms12_fresh

end Reflection

/-! ## Read-Only Static Data -/

abbrev hbEmptyCtrlSym : String := "hashbrown_verified:.rodata.cst8+0x0"

abbrev hbEmptyMapSym : String := "hashbrown_verified:.rodata..Lanon.1"

/-- Read-only static data required by `hashbrown_verified` exports (`d0` and `d2` of
    `hashbrownLib.data`). Only `pl.ρ` is read, so `hbRodata (hashbrownLib.blockPlacement mpl i)`
    is definitionally independent of the block index `i`. -/
def hbRodata (pl : Obj.Placement) : SepProp :=
  pointsToBytesRO (pl.ρ hbEmptyCtrlSym) (List.replicate 8 0xff#8) ∗
  pointsToBytesRO (pl.ρ hbEmptyMapSym)
    (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8)

set_option maxRecDepth 200000 in
theorem hbPatchedData0 (mpl : Obj.MultiPlacement) :
    hashbrownLib.patchedData mpl
      { sym := hbEmptyCtrlSym, align := 8, readOnly := true,
        bytes := hashbrownPlacedData0, zeroTail := 0, relocs := [] } =
    List.replicate 8 0xff#8 := rfl

set_option maxRecDepth 200000 in
theorem hbPatchedData2 (mpl : Obj.MultiPlacement) :
    hashbrownLib.patchedData mpl
      { sym := hbEmptyMapSym, align := 8, readOnly := true,
        bytes := hashbrownPlacedData2, zeroTail := 0,
        relocs := [{ off := 0, kind := .abs64, sym := hbEmptyCtrlSym }] } =
    Obj.bytesLE 8 (mpl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8 := by
  have hres : hashbrownLib.resolve mpl hbEmptyCtrlSym = mpl.ρ hbEmptyCtrlSym := rfl
  have hadd : addSignedAddr (mpl.ρ hbEmptyCtrlSym) 0 = mpl.ρ hbEmptyCtrlSym := by
    simp [addSignedAddr]
  simp only [MultiPlacedLib.patchedData, List.foldl_cons, List.foldl_nil,
    MultiPlacedLib.patchDataReloc, hres, hadd, List.replicate_zero, List.append_nil]
  rfl

def hbOtherRodata (mpl : Obj.MultiPlacement) : SepProp :=
  let d1 : SymDataInfo :=
    { sym := "hashbrown:.rodata.str1.1+0x0", align := 1, readOnly := true,
      bytes := hashbrownPlacedData1, zeroTail := 0, relocs := [] }
  let d3 : SymDataInfo :=
    { sym := "hashbrown:.rodata..Lanon.0", align := 1, readOnly := true,
      bytes := hashbrownPlacedData3, zeroTail := 0, relocs := [] }
  let d4 : SymDataInfo :=
    { sym := "hashbrown:.rodata..Lanon.2", align := 8, readOnly := true,
      bytes := hashbrownPlacedData4, zeroTail := 0,
      relocs := [{ off := 0, kind := .abs64, sym := "hashbrown:.rodata.str1.1+0x0" }] }
  pointsToBytesRO (mpl.ρ d1.sym) (hashbrownLib.patchedData mpl d1) ∗
  pointsToBytesRO (mpl.ρ d3.sym) (hashbrownLib.patchedData mpl d3) ∗
  pointsToBytesRO (mpl.ρ d4.sym) (hashbrownLib.patchedData mpl d4)

set_option maxRecDepth 200000 in
theorem hbDataInit_eq (mpl : Obj.MultiPlacement) :
    hashbrownLib.dataInit mpl = (hbRodata (mplAsPl mpl) ∗ hbOtherRodata mpl) := by
  have hd : hashbrownLib.data = hashbrownData := rfl
  unfold MultiPlacedLib.dataInit hbRodata hbOtherRodata
  rw [hd]
  simp only [hashbrownData, List.map, ↓reduceIte, sepAll, mplAsPl, MultiPlacedLib.blockPlacement]
  have hr0 : hashbrownLib.resolve mpl hbEmptyCtrlSym = mpl.ρ hbEmptyCtrlSym := rfl
  have hr2 : hashbrownLib.resolve mpl hbEmptyMapSym = mpl.ρ hbEmptyMapSym := rfl
  rw [hr0, hr2, hbPatchedData0, hbPatchedData2, hbEmptyCtrlSym, hbEmptyMapSym]
  ac_rfl

theorem hbRodata_dup_eq (pl : Obj.Placement) :
    hbRodata pl ∗ hbRodata pl = hbRodata pl := by
  unfold hbRodata
  have h1 := pointsToBytesRO_dup (pl.ρ hbEmptyCtrlSym) (List.replicate 8 0xff#8)
  have h2 := pointsToBytesRO_dup (pl.ρ hbEmptyMapSym)
    (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8)
  calc
    (pointsToBytesRO (pl.ρ hbEmptyCtrlSym) (List.replicate 8 0xff#8) ∗
       pointsToBytesRO (pl.ρ hbEmptyMapSym)
         (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8)) ∗
      (pointsToBytesRO (pl.ρ hbEmptyCtrlSym) (List.replicate 8 0xff#8) ∗
       pointsToBytesRO (pl.ρ hbEmptyMapSym)
         (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8))
    _ = (pointsToBytesRO (pl.ρ hbEmptyCtrlSym) (List.replicate 8 0xff#8) ∗
         pointsToBytesRO (pl.ρ hbEmptyCtrlSym) (List.replicate 8 0xff#8)) ∗
        (pointsToBytesRO (pl.ρ hbEmptyMapSym)
           (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8) ∗
         pointsToBytesRO (pl.ρ hbEmptyMapSym)
           (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8)) := by ac_rfl
    _ = pointsToBytesRO (pl.ρ hbEmptyCtrlSym) (List.replicate 8 0xff#8) ∗
        pointsToBytesRO (pl.ρ hbEmptyMapSym)
          (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8) := by rw [h1, h2]

theorem hbRodata_dup (pl : Obj.Placement) :
    hbRodata pl ⊢ hbRodata pl ∗ hbRodata pl :=
  Entails.of_eq (hbRodata_dup_eq pl).symm

theorem hbEmptyCtrl_aligned_and_noWrap {i : Nat} {pl : Obj.Placement}
    (hP : (hashbrownLib.blockLib i).Placeable pl) :
    (pl.ρ hbEmptyCtrlSym).toNat % 8 = 0 ∧ (pl.ρ hbEmptyCtrlSym).toNat + 8 ≤ 2 ^ 64 := by
  let d0 : SymDataInfo :=
    { sym := hbEmptyCtrlSym, align := 8, readOnly := true,
      bytes := hashbrownPlacedData0, zeroTail := 0, relocs := [] }
  have hd0 : d0 ∈ (hashbrownLib.blockLib i).data := List.Mem.head _
  have hok := hP.data_ok d0 hd0
  have hlen : d0.bytes.length + d0.zeroTail = 8 := rfl
  exact ⟨hok.2.2.1, hlen ▸ hok.2.2.2⟩

theorem hbEmptyMap_aligned_and_noWrap {i : Nat} {pl : Obj.Placement}
    (hP : (hashbrownLib.blockLib i).Placeable pl) :
    (pl.ρ hbEmptyMapSym).toNat % 8 = 0 ∧ (pl.ρ hbEmptyMapSym).toNat + 32 ≤ 2 ^ 64 := by
  let d2 : SymDataInfo :=
    { sym := hbEmptyMapSym, align := 8, readOnly := true,
      bytes := hashbrownPlacedData2, zeroTail := 0,
      relocs := [{ off := 0, kind := .abs64, sym := hbEmptyCtrlSym }] }
  have hd2 : d2 ∈ (hashbrownLib.blockLib i).data :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have hok := hP.data_ok d2 hd2
  have hlen : d2.bytes.length + d2.zeroTail = 32 := rfl
  exact ⟨hok.2.2.1, hlen ▸ hok.2.2.2⟩

attribute [irreducible] mplAsPl
  hbLib0 hbLib1 hbLib2 hbLib3 hbLib4 hbLib5 hbLib6
  hbLib7 hbLib8 hbLib9 hbLib10 hbLib11 hbLib12
  HbPlaced.pl HbPlaced.pl1 HbPlaced.pl2 HbPlaced.pl3 HbPlaced.pl4 HbPlaced.pl5 HbPlaced.pl6
  HbPlaced.pl7 HbPlaced.pl8 HbPlaced.pl9 HbPlaced.pl10 HbPlaced.pl11 HbPlaced.pl12

end CaseStudies.Hashbrown.Proofs
