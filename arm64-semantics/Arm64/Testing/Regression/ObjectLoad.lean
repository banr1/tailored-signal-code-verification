/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Legacy.Object.LinkedImage
public meta import Arm64.Legacy.Object.LinkedImage
public import Arm64.Legacy.Object.Loader
public meta import Arm64.Legacy.Object.Loader
public import ProofLib.ObjectLoad
public import ProofLib.Library
public import ProofLib.SepLogic.WP
public import ProofLib.VCGen

/-!
# Relocating Loader and `library_ok` Regression Tests

Regression tests for `Arm64.Obj.LinkedImage.load`, `ProofLib.ObjectLoad`, `library_ok`, `fnAddr`
rebasing simprocs, and `sym_guard`.
-/

@[expose] public section

namespace Testing.ObjectLoad

open Arm64.Obj

/-- Little-endian bytes of instruction words. -/
def words (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => bytesLE 4 (w.setWidth 64)

/-- The object `t.o` records no relocation-free functions (`f` has relocations). -/
def handInfo : ObjectInfo := { name := "t.o" }

def handLinked : LinkedImage where
  code := words [0x94000005, 0x94000005, 0xb0000000, 0x91000000, 0xd65f03c0, 0xd65f03c0, 0]
  dataOff := 0x1000
  data := [0x68, 0x69, 0, 0, 0, 0, 0, 0] ++ List.replicate 8 0
  roData := [(0x1000, 8)]
  gotOff := 0x1010
  relocs := [{ off := 8, target := 0x1001 }]
  symbols := [("f", 0)]
  objSymbols := [("t.o", [("f", 0)])]
  stubs := [("ext", 0x18)]
  objects := [handInfo]

def handImg := handLinked.load 0x10000

-- `ld.lld` output for `.text` + `.text.g`, and the zero stub for `ext`.
#guard (handImg.toOption.map (·.code)) =
  some (words [0x94000005, 0x94000005, 0xb0000000, 0x91000000, 0xd65f03c0, 0xd65f03c0, 0])

#guard (handImg.toOption.map (·.dataAddr)) = some 0x11000
-- `data` is 16 bytes at `0x11000`, so `brkStart` is the page-aligned end `0x12000`.
#guard (handImg.toOption.map (·.brkStart)) = some 0x12000
-- `ld.lld` output for `.rodata` + `.data` (`ptr = msg + 1 = 0x11001`).
#guard (handImg.toOption.map (·.data)) =
  some ([0x68, 0x69, 0, 0, 0, 0, 0, 0] ++ bytesLE 8 0x11001)
#guard (handImg.toOption.map (·.roData)) = some [(0x11000, 8)]
#guard (handImg.toOption.map (·.symbols)) = some [("f", 0)]
#guard (handImg.toOption.map (·.stubs)) = some [("ext", 0x18)]
/-- Test helper: address of defined symbol or stub `name` (`base` if absent). -/
def symAddr (img : Image) (name : String) : BitVec 64 :=
  img.base + BitVec.ofNat 64 (((lookup name img.symbols).orElse fun _ => lookup name img.stubs).getD 0)

#guard (handImg.toOption.map (symAddr · "ext")) = some 0x10018

-- Code bytes are the same at another page-aligned base; the data relocation moves.
#guard ((handLinked.load 0x7fff_0000_3000).toOption.map (·.code)) =
  (handImg.toOption.map (·.code))
#guard ((handLinked.load 0x7fff_0000_3000).toOption.map (·.data.drop 8)) =
  some (bytesLE 8 0x7fff_0000_4001)

-- A misaligned base is rejected.
#guard (handLinked.load 0x10004).toOption.isNone

-- An image that would wrap around the address space is rejected.
#guard (handLinked.load (0 - 0x1000)).toOption.isNone

/-! ## GOT Slots, BSS, Extern Data, and `ABS32` -/

def gotLinked : LinkedImage where
  code := words [0xd65f03c0]
  dataOff := 0x1000
  data := List.replicate 8 0
  bss := 8
  externData := [("x", 0x1010, 8)]
  gotOff := 0x1018
  got := [.addr 0x1010, .addr 0, .tpoff 0x18]
  relocs := [{ off := 0, width := 4, target := 0x1010 }]
  symbols := [("r", 0)]
  stubs := []

-- GOT slot `i` holds `base + off` for `.addr off` and `v` for `.tpoff v`; bss is zero-filled;
-- extern data is relocated.
#guard ((gotLinked.load 0x20000).toOption.map (·.got)) = some [0x21010, 0x20000, 0x18]
#guard ((gotLinked.load 0x20000).toOption.map (·.gotAddr)) = some 0x21018
#guard ((gotLinked.load 0x20000).toOption.map (·.data)) =
  some (bytesLE 4 0x21010 ++ List.replicate 12 0)
#guard ((gotLinked.load 0x20000).toOption.map (·.externData)) = some [("x", 0x21010, 8)]
-- `ABS32` out of range is rejected.
#guard (gotLinked.load 0x1_0000_0000).toOption.isNone

/-! ## Malformed Linked Images -/

-- Data overlapping the code.
#guard (({ handLinked with dataOff := 0 } : LinkedImage).load 0x10000).toOption.isNone
-- Data region not page-aligned.
#guard (({ handLinked with dataOff := 0x1008, gotOff := 0x1018 } : LinkedImage).load 0x10000).toOption.isNone
-- Relocation outside the data.
#guard (({ handLinked with relocs := [{ off := 12, target := 0 }] } : LinkedImage).load 0x10000).toOption.isNone
-- rodata outside the data region.
#guard (({ handLinked with roData := [(0x1008, 16)] } : LinkedImage).load 0x10000).toOption.isNone
-- Stub outside the code.
#guard (({ handLinked with stubs := [("ext", 0x1c)] } : LinkedImage).load 0x10000).toOption.isNone
-- An object whose recorded function is not at its symbol.
#guard (({ handLinked with
    objects := [{ name := "t.o", fns := [("f", words [0x94000000])] }] } : LinkedImage).load
    0x10000).toOption.isNone
-- An object that is not in `objSymbols`.
#guard (({ handLinked with objects := [{ name := "u.o" }] } : LinkedImage).load
    0x10000).toOption.isNone
-- ... but a recorded function whose bytes match is accepted.
#guard (({ handLinked with
    objects := [{ name := "t.o", fns := [("f", words [0x94000005, 0x94000005])] }] } :
      LinkedImage).load 0x10000).toOption.isSome

/-! ## Canonical Program and Rebasing -/

open Arm64 in
def handCode : Program := handLinked.toProgram

theorem handCode_canonical : handLinked.toProgram = handCode := rfl

theorem handCode_codeAt_f : handCode.codeAt "f" "94000005 94000005 b0000000 91000000 d65f03c0" := by
  decide

open Arm64 in
example (img : Image) (h : Loads handLinked img) :
    (Program.ofImage img (fun n => if n = "ext" then some id else none)).codeAt "f"
      "94000005 94000005 b0000000 91000000 d65f03c0" := by
  rw [Program.ofImage_eq_rebase handCode_canonical h]
  exact Program.codeAt_rebase handCode_codeAt_f (by decide)

/-! ## Per-Object Symbol Tables, `symtab`, `LibrarySpec`, and `library_ok` -/

-- Per-object symbol lookup resolves `f` in `t.o` and returns `none` for unknown symbols or objects.
#guard (handImg.toOption.bind (·.symtab "t.o" "f")) = some 0x10000#64
#guard (handImg.toOption.bind (·.symtab "t.o" "ext")) = none
-- Global / stub lookup (`objName = ""`) resolves defined symbols (`f`) and extern stubs (`ext`).
#guard (handImg.toOption.bind (·.symtab "" "f")) = some 0x10000#64
#guard (handImg.toOption.bind (·.symtab "" "ext")) = some 0x10018#64
#guard (handImg.toOption.bind (·.symtab "" "nonexistent")) = none

/-- What the linker records for a minimal relocation-free object implementing `ret42`
    (`mov x0, #42; ret`). -/
def ret42Obj : ObjectInfo where
  name := "ret42.o"
  fns := [("ret42", words [0xd2800540, 0xd65f03c0])]

/-- A linked image of `ret42.o`. -/
def ret42Linked : LinkedImage where
  code := words [0xd2800540, 0xd65f03c0]
  dataOff := 0x1000
  data := []
  gotOff := 0x1000
  symbols := [("ret42", 0)]
  objSymbols := [("ret42.o", [("ret42", 0)])]
  stubs := []
  objects := [ret42Obj]

-- `LinkedImage.load` accepts an image honouring `ret42Obj`, so `library_ok ret42Lib` below is not
-- vacuous.
#guard (ret42Linked.load 0x10000).toOption.isSome

open Arm64 in
def ret42Spec : Spec Unit where
  pre := fun () _ => emp
  post := fun () _ sf => ⌜sf.readReg64 .x0 = 42#64⌝

open Arm64 in
def ret42Lib : LibrarySpec where
  name := "ret42"
  obj := some ret42Obj
  contracts := [{ sym := "ret42", spec := ret42Spec }]

open Arm64 ProofLib in
theorem ret42_ok_abstract (prog : Program)
    (h_code : prog.codeAt "ret42" "d2800540 d65f03c0") :
    prog.subroutineOk "ret42" ret42Spec := by
  wp_init _u s0
  wp_steps
  wp_done

open Arm64 in
theorem ret42Lib_ok : library_ok ret42Lib := by
  refine library_ok_single rfl rfl fun img X hLoads c hc => ?_
  rcases List.mem_singleton.1 hc with rfl
  exact Contract.Holds.of_relocFreeFn rfl hLoads (by decide) ret42_ok_abstract

open Arm64 in
/-- A second library depending on `ret42Lib` (with no additional contracts of its own)
    demonstrating `library_ok.discharge`. -/
def callerLib : LibrarySpec where
  name := "caller"
  obj := some handInfo
  deps := [ret42Lib]
  contracts := []

open Arm64 in
theorem callerLib_given_ret42 : library_ok callerLib [ret42Lib] := by
  refine ⟨fun D hD hDT => ?_, fun img X _ _ D hD hDT c hc => ?_⟩
  · simp [callerLib, ret42Lib, LibrarySpec.closure, LibrarySpec.closure.go] at hD
    rcases hD with rfl | rfl
    · exact False.elim (hDT List.mem_cons_self)
    · rfl
  · simp [callerLib, ret42Lib, LibrarySpec.closure, LibrarySpec.closure.go] at hD
    rcases hD with rfl | rfl
    · exact False.elim (hDT List.mem_cons_self)
    · cases hc

open Arm64 in
theorem callerLib_ok : library_ok callerLib :=
  callerLib_given_ret42.discharge ret42Lib_ok
    (by simp [callerLib, ret42Lib, LibrarySpec.closure, LibrarySpec.closure.go])

/-! ## `reduceFnOffSym`, `reduceFnAddrSym`, and Guarded `reduceFnAddrRebase` Simprocs -/

open Arm64 ProofLib in
def testProg : Program :=
  { handCode with symbols := [("test_fn", 0x1000), ("f", 0)] }

open Arm64 in
@[simp, arm64_norm] theorem testProg_fnOff : testProg.fnOff "test_fn" = 0x1000 := rfl

open Arm64 in
@[simp, arm64_norm] theorem testProg_fnOff_f : testProg.fnOff "f" = 0 := rfl

abbrev myFnName : String := "test_fn"
abbrev myFnAliasName : String := myFnName
abbrev zeroFnName : String := "f"
abbrev unknownFnName : String := "unknown_fn"

open Arm64 ProofLib in
theorem fnAddr_rebase_abbrev_eq (b : BitVec 64)
    (H O : String → Option (State → State)) :
    (testProg.rebase b H O).fnAddr myFnName = b + 0x1000#64 := by
  simp only [arm64_norm]

open Arm64 ProofLib in
theorem fnAddr_rebase_abbrev_norm (b : BitVec 64)
    (H O : String → Option (State → State))
    (P : BitVec 64 → Prop) (h : P (b + 0x1000#64)) :
    P ((testProg.rebase b H O).fnAddr myFnName) := by
  simp only [arm64_norm]
  guard_target =ₛ P (b + 0x1000#64)
  exact h

open Arm64 ProofLib in
theorem fnAddr_rebase_abbrev_zero_norm (b : BitVec 64)
    (H O : String → Option (State → State))
    (P : BitVec 64 → Prop) (h : P b) :
    P ((testProg.rebase b H O).fnAddr zeroFnName) := by
  simp only [arm64_norm]
  guard_target =ₛ P b
  exact h

open Arm64 ProofLib in
theorem fnOff_rebase_abbrev_norm (b : BitVec 64)
    (H O : String → Option (State → State))
    (P : Nat → Prop) (h : P 0x1000) :
    P ((testProg.rebase b H O).fnOff myFnAliasName) := by
  simp only [arm64_norm]
  guard_target =ₛ P 0x1000
  exact h

open Arm64 ProofLib in
/-- Unknown symbols without a `fnOff` simp lemma stay unexpanded under `reduceFnAddrRebase`. -/
theorem fnAddr_rebase_unknown_guarded (b : BitVec 64)
    (H O : String → Option (State → State))
    (P : BitVec 64 → Prop) (h : P ((testProg.rebase b H O).fnAddr "unknown_fn")) :
    P ((testProg.rebase b H O).fnAddr unknownFnName) := by
  simp only [arm64_norm]
  guard_target =ₛ P ((testProg.rebase b H O).fnAddr "unknown_fn")
  exact h

open Arm64 ProofLib in
theorem fnAddr_rebase_fvar_guarded (b : BitVec 64)
    (H O : String → Option (State → State)) (sym : String)
    (P : BitVec 64 → Prop) (h : P ((testProg.rebase b H O).fnAddr sym)) :
    P ((testProg.rebase b H O).fnAddr sym) := by
  fail_if_success simp only [arm64_norm]
  exact h

open Arm64 in
abbrev testRebased (b : BitVec 64) (H O : String → Option (State → State)) : Program :=
  testProg.rebase b H O

open Arm64 in
abbrev testFnAddr (b : BitVec 64) (H O : String → Option (State → State)) : BitVec 64 :=
  (testProg.rebase b H O).fnAddr "test_fn"

open Arm64 ProofLib in
theorem fnAddr_rebased_prog_abbrev_norm (b : BitVec 64)
    (H O : String → Option (State → State))
    (P : BitVec 64 → Prop) (h : P (b + 0x1000#64)) :
    P ((testRebased b H O).fnAddr "test_fn") := by
  simp only [arm64_norm]
  guard_target =ₛ P (b + 0x1000#64)
  exact h

open Arm64 ProofLib in
theorem fnAddr_rebase_whole_abbrev_norm (b : BitVec 64)
    (H O : String → Option (State → State))
    (P : BitVec 64 → Prop) (h : P (b + 0x1000#64)) :
    P (testFnAddr b H O) := by
  simp only [arm64_norm]
  guard_target =ₛ P (b + 0x1000#64)
  exact h

/-! ## `str_chars%`, `sym_enc_of%`, `stub_enc_of%`, and `sym_guard` -/

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
def guardTestImage : LinkedImage where
  code := words [0xd65f03c0, 0xd65f03c0, 0]
  dataOff := 0x1000
  data := List.replicate 16 0
  gotOff := 0x1010
  symbols := [("alpha_fn", 0), ("beta_fn", 4), ("token_data", 0x1000)]
  stubs := [("ext_hook", 8)]

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
def guardTestCode : Program := guardTestImage.toProgram

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
def guardTestCode_symChars : List (List Char × Nat) := sym_chars_of% guardTestCode

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
def guardTestCode_stubChars : List (List Char × Nat) := stub_chars_of% guardTestCode

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
def guardTestCode_symEnc : EncSymTable Nat := sym_enc_of% guardTestCode

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
def guardTestCode_stubEnc : EncSymTable Nat := stub_enc_of% guardTestCode

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem guardTestCode_symbols_eq : guardTestCode.symbols = toStringSymbols guardTestCode_symChars := by
  rfl_kernel

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem guardTestCode_stubs_eq : guardTestCode.stubs = toStringSymbols guardTestCode_stubChars := by
  rfl_kernel

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem guardTestCode_symEnc_eq : prepareCharAssocVal guardTestCode_symChars = guardTestCode_symEnc := by
  rfl_kernel

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem guardTestCode_stubEnc_eq : prepareCharAssocVal guardTestCode_stubChars = guardTestCode_stubEnc := by
  rfl_kernel

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem guardTestCode_symbols_fresh : allFreshCharSymbols guardTestCode_symChars = true := by
  rfl_kernel

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem guardTestCode_stubs_wf : wfStubCharSymbols guardTestCode_stubChars guardTestCode_symChars = true := by
  rfl_kernel

open Arm64 ProofLib ProofLib.ProgramReflection in
theorem str_chars_elaborator_ok :
    "beta_fn" = String.ofList (str_chars% "beta_fn") := by
  rfl_kernel

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem sym_guard_lookup_and_unique_ok :
    lookup "beta_fn" guardTestImage.symbols = some 4 ∧
    lookupUnique "token_data" guardTestImage.symbols = some 0x1000 ∧
    (guardTestImage.symbols.filter (·.1 == "alpha_fn")).length = 1 ∧
    guardTestImage.symbols.any (·.1 == "beta_fn") = true ∧
    guardTestCode.fnOff "beta_fn" = 4 ∧
    guardTestCode.fnOff "ext_hook" = 8 := by
  sym_guard

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem sym_guard_all_and_symtab_ok (img : Image) (hLoad : Loads guardTestImage img) :
    (["alpha_fn", "beta_fn", "token_data"].all fun name =>
      (img.symbols.filter (·.1 == name)).length == 1) = true ∧
    ([("ext_hook", 8)].all fun (n, off) =>
      lookupUnique n guardTestImage.stubs == some off &&
        !guardTestImage.symbols.any (·.1 == n)) = true ∧
    (Program.ofImage img).fnAddr "beta_fn" = img.base + 4#64 ∧
    img.symtab "" "token_data" = some (img.base + 0x1000#64) ∧
    img.symtab "" "ext_hook" = some (img.base + 8#64) := by
  sym_guard

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
def standaloneGuardImage : LinkedImage where
  code := words [0xd65f03c0]
  dataOff := 0x1000
  data := List.replicate 8 0
  gotOff := 0x1008
  symbols := [("only_in_image", 0), ("only_data", 0x1000)]
  stubs := []

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
theorem sym_guard_auto_bundle_ok (img : Image) (hLoad : Loads standaloneGuardImage img) :
    (img.symbols.filter (·.1 == "only_in_image")).length = 1 ∧
    img.symtab "" "only_data" = some (img.base + 0x1000#64) := by
  sym_guard

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad in
-- Negative test: `sym_guard` rejects a false offset equality.
/--
error: Tactic `sym_guard` failed: could not discharge symbol guard

⊢ lookup "beta_fn" guardTestImage.symbols = some 999
-/
#guard_msgs in
example : lookup "beta_fn" guardTestImage.symbols = some 999 := by
  sym_guard

open Arm64 ProofLib ProofLib.ObjectLoad in
theorem relocChunks_spec_empty_ok (b : BitVec 64) (data : List (BitVec 8)) :
    ([] : List (List DataReloc)).flatten.foldlM (DataReloc.apply b) data = .ok data :=
  relocChunks_spec b [] data data rfl

open Arm64 ProofLib ProofLib.ObjectLoad in
/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.38 = ?m.38
but is expected to have type
  relocChunks b [] [[{ off := 0, target := 0 }]] = some []
in the application
  relocChunks_spec b [[{ off := 0, target := 0 }]] [] [] rfl
-/
#guard_msgs in
example (b : BitVec 64) :
    ([[{ off := 0, target := 0, width := 8 }]] : List (List DataReloc)).flatten.foldlM
      (DataReloc.apply b) [] = .ok [] :=
  relocChunks_spec b [[{ off := 0, target := 0, width := 8 }]] [] [] rfl

end Testing.ObjectLoad
