/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.SepLogic.SymBlock.Tactic

/-!
# Layout-Generic Relocations and Symbolic Decoder Tests

Regression tests for `Obj.patchRelocs`, `Contract.holds_of_relocFn`, `VeneerAt`, symbol-relative
cut points (`reloc_call_off%`, `words_ret_off%`), TLS relocation decoding, and `checkRelocFn`
across `wp_sym_steps` and `sym_block`.
-/

@[expose] public section

namespace Testing.LayoutGenericRelocs

open Arm64 ProofLib

set_option maxHeartbeats 200000

/-! ## `ADRP` and `ADD :lo12:` Symbol Address Computation -/

/-- Template words for `adrp x0, 0; add x0, x0, #0; ret`. -/
def getSymAddrWords : List (BitVec 32) :=
  [0x90000000#32, 0x91000000#32, 0xd65f03c0#32]

def getSymAddrRelocs : List Obj.RelocEntry :=
  [ { off := 0, kind := .adrpHi21, sym := "my_table", addend := 0 }
  , { off := 4, kind := .addLo12, sym := "my_table", addend := 0 } ]

c_spec getSymAddrSpec (ctx target : BitVec 64) : (ret : u64)
  ensures_pure ret = target

theorem getSymAddr_wp_sym_steps_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ getSymAddrRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs getSymAddrRelocs getSymAddrWords a resolve)) :
    subroutine_ok prog a (getSymAddrSpec (resolve "my_table")) := by
  wp_init u s0
  wp_sym_steps
  wp_done

theorem getSymAddr_sym_block_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ getSymAddrRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs getSymAddrRelocs getSymAddrWords a resolve)) :
    subroutine_ok prog a (getSymAddrSpec (resolve "my_table")) := by
  wp_init u s0
  sym_block
  wp_done

/-! ## Mutable `.data` Globals, Nonzero Addends, and Indexed Loads -/

/-- Template words for `adrp x8, 0; ldr x9, [x8]; add x9, x9, #1; str x9, [x8]; mov x0, x9; ret`. -/
def bumpCounterWords : List (BitVec 32) :=
  [0x90000008#32, 0xf9400109#32, 0x91000529#32, 0xf9000109#32, 0xaa0903e0#32, 0xd65f03c0#32]

def bumpCounterRelocs : List Obj.RelocEntry :=
  [ { off := 0, kind := .adrpHi21, sym := "counter", addend := 0 }
  , { off := 4, kind := .ldst64Lo12, sym := "counter", addend := 0 }
  , { off := 12, kind := .ldst64Lo12, sym := "counter", addend := 0 } ]

c_spec bumpCounterSpec (ctx counterAddr : BitVec 64) (ghost v : BitVec 64) : (ret : u64)
  requires counterAddr ↦₆₄ v
  ensures  counterAddr ↦₆₄ (v + 1#64)
  ensures_pure ret = v + 1#64

theorem bumpCounter_wp_sym_steps_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ bumpCounterRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs bumpCounterRelocs bumpCounterWords a resolve)) :
    subroutine_ok prog a (bumpCounterSpec (resolve "counter")) := by
  wp_init v s0
  wp_sym_steps
  wp_done

theorem bumpCounter_sym_block_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ bumpCounterRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs bumpCounterRelocs bumpCounterWords a resolve)) :
    subroutine_ok prog a (bumpCounterSpec (resolve "counter")) := by
  wp_init v s0
  sym_block
  wp_done

/-- Template words for `adrp x8, 0; ldr x0, [x8]; ret` with `addend = 8` (`sym + 8#64`). -/
def readField8Words : List (BitVec 32) :=
  [0x90000008#32, 0xf9400100#32, 0xd65f03c0#32]

def readField8Relocs : List Obj.RelocEntry :=
  [ { off := 0, kind := .adrpHi21, sym := "pair", addend := 8 }
  , { off := 4, kind := .ldst64Lo12, sym := "pair", addend := 8 } ]

c_spec readField8Spec (ctx baseAddr : BitVec 64) (ghost v0 v1 : BitVec 64) : (ret : u64)
  preserves (baseAddr ↦₆₄ v0) ∗ ((baseAddr + 8#64) ↦₆₄ v1)
  ensures_pure ret = v1

theorem readField8_sym_block_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ readField8Relocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs readField8Relocs readField8Words a resolve)) :
    subroutine_ok prog a (readField8Spec (resolve "pair")) := by
  wp_init a_args s0
  obtain ⟨v0, v1⟩ := a_args
  sym_block
  wp_done

/-- Scaled index table access: `adrp x8, tbl; add x8, x8, x0, lsl #3; ldr x0, [x8, :lo12:tbl]; ret`
    exercising `pageOf_add_idx_add_lo12Of` (`(pageOf tbl + idx) + lo12Of tbl = tbl + idx`). -/
def readIndexedWords : List (BitVec 32) :=
  [0x90000008#32, 0x8b000d08#32, 0xf9400100#32, 0xd65f03c0#32]

def readIndexedRelocs : List Obj.RelocEntry :=
  [ { off := 0, kind := .adrpHi21, sym := "tbl", addend := 0 }
  , { off := 8, kind := .ldst64Lo12, sym := "tbl", addend := 0 } ]

c_spec readIndexedSpec (ctx tblAddr : BitVec 64) (idx : u64) (ghost v : BitVec 64) : (ret : u64)
  preserves (tblAddr + idx <<< 3#64) ↦₆₄ v
  ensures_pure ret = v

theorem readIndexed_sym_block_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ readIndexedRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs readIndexedRelocs readIndexedWords a resolve)) :
    subroutine_ok prog a (readIndexedSpec (resolve "tbl")) := by
  wp_init a_args s0
  obtain ⟨idx, v⟩ := a_args
  sym_block
  wp_done

/-! ## `Contract.holds_of_relocFn` with `.rodata`, `.data`, and `BL` -/

/-- Bytes for `read_ro_and_bump`:
    `+0`:  `stp x29, x30, [sp, #-16]!` (`0xa9bf7bfd`)
    `+4`:  `bl bump_counter`           (`0x94000000`)
    `+8`:  `adrp x8, ro_magic`         (`0x90000008`)
    `+12`: `ldr x9, [x8, :lo12:ro_magic]` (`0xf9400109`)
    `+16`: `add x0, x0, x9`            (`0x8b090000`)
    `+20`: `ldp x29, x30, [sp], #16`   (`0xa8c17bfd`)
    `+24`: `ret`                       (`0xd65f03c0`) -/
def readRoAndBumpWords : List (BitVec 32) :=
  [ 0xa9bf7bfd#32, 0x94000000#32, 0x90000008#32, 0xf9400109#32
  , 0x8b090000#32, 0xa8c17bfd#32, 0xd65f03c0#32 ]

def readRoAndBumpRelocs : List Obj.RelocEntry :=
  [ { off := 4, kind := .call26, sym := "bump_counter", addend := 0 }
  , { off := 8, kind := .adrpHi21, sym := "ro_magic", addend := 0 }
  , { off := 12, kind := .ldst64Lo12, sym := "ro_magic", addend := 0 } ]

def readRoMagicWords : List (BitVec 32) :=
  [0x90000008#32, 0x39400100#32, 0xd65f03c0#32]

def readRoMagicRelocs : List Obj.RelocEntry :=
  [ { off := 0, kind := .adrpHi21, sym := "ro_magic", addend := 0 }
  , { off := 4, kind := .ldst8Lo12, sym := "ro_magic", addend := 0 } ]

def wordsToBytesLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap Obj.bytesOfWordLE

/-- Synthetic `ObjectInfo` exercising `relocFns` and `dataSyms` (`.rodata` bytes, `.rodata` `ABS64`
    function-pointer table, `.rodata` `PREL32` offset table, and `.data` RW global). -/
def testRelocObj : Obj.ObjectInfo where
  name := "test_reloc.o"
  fns := []
  callFns := []
  relocFns :=
    [ { sym := "bump_counter"
        code := wordsToBytesLE bumpCounterWords
        relocs := bumpCounterRelocs }
    , { sym := "read_ro_magic"
        code := wordsToBytesLE readRoMagicWords
        relocs := readRoMagicRelocs } ]
  dataSyms :=
    [ { sym := "ro_magic"
        align := 1
        readOnly := true
        bytes := [0x2a#8]
        relocs := [] }
    , { sym := "fn_tbl"
        align := 8
        readOnly := true
        bytes := [0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]
        relocs := [{ off := 0, kind := .abs64, sym := "read_ro_magic", addend := 0 }] }
    , { sym := "prel_tbl"
        align := 4
        readOnly := true
        bytes := [0x00#8, 0x00#8, 0x00#8, 0x00#8]
        relocs := [{ off := 0, kind := .prel32, sym := "ro_magic", addend := 0 }] }
    , { sym := "counter"
        align := 8
        readOnly := false
        bytes := [0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]
        relocs := [] } ]

/-- Concrete `LinkedImage` laying out `testRelocObj`:
    - `bump_counter` at offset `0` (`24` bytes)
    - `read_ro_magic` at offset `24` (`12` bytes)
    - `dataOff = 4096` (page-aligned):
      - `"ro_magic"` at offset `4096` (`[0x2a#8]`, padded to `4104`)
      - `"fn_tbl"` at offset `4104` (`ABS64` relocation at `data` offset `8` targeting `24`)
      - `"prel_tbl"` at offset `4112` (`PREL32` value `4096 - 4112 = -16 = 0xfffffff0#32`, padded to `4120`)
      - `roData = [(4096, 24)]` covering offsets `[4096, 4120)`
      - `"counter"` at offset `4120` (`8` RW bytes outside `roData`)
    - `gotOff = 4128` -/
def testLinkedImage : Obj.LinkedImage where
  code :=
    let resolve : String → BitVec 64
      | "bump_counter" => 0#64
      | "read_ro_magic" => 24#64
      | "ro_magic" => 4096#64
      | "fn_tbl" => 4104#64
      | "prel_tbl" => 4112#64
      | "counter" => 4120#64
      | _ => 0#64
    wordsToBytesLE (Obj.patchRelocs bumpCounterRelocs bumpCounterWords 0#64 resolve) ++
    wordsToBytesLE (Obj.patchRelocs readRoMagicRelocs readRoMagicWords 24#64 resolve)
  dataOff := 4096
  data :=
    [ 0x2a#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8
    , 0x18#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8
    , 0xf0#8, 0xff#8, 0xff#8, 0xff#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8
    , 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8 ]
  roData := [(4096, 24)]
  gotOff := 4128
  relocs := [{ off := 8, width := 8, target := 24 }]
  symbols :=
    [ ("bump_counter", 0)
    , ("read_ro_magic", 24)
    , ("ro_magic", 4096)
    , ("fn_tbl", 4104)
    , ("prel_tbl", 4112)
    , ("counter", 4120) ]
  objSymbols :=
    [ ("test_reloc.o",
      [ ("bump_counter", 0)
      , ("read_ro_magic", 24)
      , ("ro_magic", 4096)
      , ("fn_tbl", 4104)
      , ("prel_tbl", 4112)
      , ("counter", 4120) ]) ]
  stubs := []
  objects := [testRelocObj]

theorem testLinkedImage_honours : testLinkedImage.honours testRelocObj = true := by decide

theorem testLinkedImage_wellFormed : testLinkedImage.wellFormed = true := by decide

def bumpCounterObjSpec : Spec (BitVec 64) where
  pre := fun v s => s.sym "test_reloc.o" "counter" ↦₆₄ v
  post := fun v s sf =>
    ⌜sf.readReg64 (.gpr 0#5) = v + 1#64⌝ ∗ (s.sym "test_reloc.o" "counter" ↦₆₄ (v + 1#64))

def bumpCounterImgContract : Contract :=
  { sym := "bump_counter", spec := bumpCounterObjSpec }

def readRoMagicObjSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ _ sf => ⌜sf.readReg64 (.gpr 0#5) = 42#64⌝

def readRoMagicContract : Contract :=
  { sym := "read_ro_magic", spec := readRoMagicObjSpec }

def testRelocLib : LibrarySpec where
  name := "test_reloc"
  obj := some testRelocObj
  deps := []
  contracts := [bumpCounterImgContract, readRoMagicContract]

theorem bumpCounter_contract_holds {img : Obj.Image} {X : String → Option (State → State)}
    (hLinks : LinksIn [testRelocLib] img []) :
    Contract.Holds testRelocLib img X bumpCounterImgContract := by
  refine Contract.holds_of_relocFn hLinks (by simp) (by simp) rfl
    (relocs := bumpCounterRelocs) (words := bumpCounterWords) (by decide) ?_
  intro a resolve hctx hrange hwords
  dsimp only [bumpCounterImgContract, Spec.inImage, bumpCounterObjSpec]
  wp_init v s0
  have hSymEq : s0.sym "test_reloc.o" "counter" = resolve "counter" :=
    hctx.sym_self_of_dataSym ‹s0.symtab = img.symtab› (D := testRelocLib) (o := testRelocObj)
      (d := { sym := "counter", align := 8, readOnly := false,
              bytes := [0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8],
              relocs := [] })
      (by simp) (by simp) rfl (by decide) (by decide)
  rw [hSymEq]
  sym_block
  wp_done

theorem readRoAndBump_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64) (v : BitVec 64)
    (hrange : ∀ r ∈ readRoAndBumpRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs readRoAndBumpRelocs readRoAndBumpWords a resolve))
    (hcallee : subroutine_ok prog (resolve "bump_counter") (bumpCounterSpec (resolve "counter"))) :
    subroutine_ok prog a
      { pre := fun (_ : Unit) s =>
          (resolve "counter" ↦₆₄ v) ∗
          (resolve "ro_magic" ↦₆₄ 42#64) ∗
          stackFrameAt s.sp 16
        post := fun _ _ sf =>
          ⌜sf.readReg64 (.gpr 0#5) = v + 1#64 + 42#64⌝ ∗
          (resolve "counter" ↦₆₄ (v + 1#64)) ∗
          (resolve "ro_magic" ↦₆₄ 42#64) ∗
          stackFrameAt sf.sp 16 } := by
  wp_init u s0
  wp_sym_steps
  wp_call hcallee
  wp_sym_steps
  wp_done

theorem readRoMagic_contract_holds {img : Obj.Image} {X : String → Option (State → State)}
    (hLinks : LinksIn [testRelocLib] img []) :
    Contract.Holds testRelocLib img X readRoMagicContract := by
  refine Contract.holds_of_relocFn hLinks (by simp) (by simp) rfl
    (relocs := readRoMagicRelocs) (words := readRoMagicWords) (by decide) ?_
  intro a resolve hctx hrange hwords
  dsimp only [readRoMagicContract, Spec.inImage, readRoMagicObjSpec]
  wp_init u s0
  have hRo : Obj.HoldsBytes s0.mem (resolve "ro_magic") [0x2a#8] (fun _ => .ro) :=
    hctx.holdsBytes_dataSym_ro ‹img.FrozenLoaded s0› (D := testRelocLib) (o := testRelocObj)
      (d := { sym := "ro_magic", align := 1, readOnly := true,
              bytes := [0x2a#8], relocs := [] })
      (by simp) (by simp) rfl (by decide) (by decide) rfl rfl
  refine SepWP.holdsBytes_ro_intro hRo (by decide) ?_
  wp_sym_steps
  wp_done

theorem testRelocLib_ok : library_ok testRelocLib [] := by
  have hclosure : testRelocLib.closure = [testRelocLib] := rfl
  refine ⟨fun D hD _ => ?_, fun img X hLinks _ D hD _ c hc => ?_⟩
  · rw [hclosure, List.mem_singleton] at hD
    subst hD
    rfl
  · rw [hclosure, List.mem_singleton] at hD
    subst hD
    rw [hclosure] at hLinks
    simp only [testRelocLib, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact bumpCounter_contract_holds hLinks
    · exact readRoMagic_contract_holds hLinks

def testLoadedImage : Obj.Image :=
  match testLinkedImage.load 0x100000#64 with
  | .ok img => img
  | .error _ => default

theorem testRelocLib_linksIn_nonvacuous :
    LinksIn [testRelocLib] testLoadedImage [] := by
  refine ⟨testLinkedImage, ?_, ?_⟩
  · intro D hD
    simp only [List.mem_singleton] at hD
    subst hD
    left
    intro o ho
    cases ho
    exact List.Mem.head _
  · show testLinkedImage.load testLoadedImage.base = .ok testLoadedImage
    rfl

/-! ## Additional Relocation Kinds -/

/-- `ADR_PREL_LO21` (`ADR x0, target; ret`) via `Obj.patchRelocs`. -/
def adrWords : List (BitVec 32) :=
  [0x10000000#32, 0xd65f03c0#32]

def adrRelocs : List Obj.RelocEntry :=
  [{ off := 0, kind := .adrPrelLo21, sym := "near_sym", addend := 0 }]

theorem adr_wp_sym_steps_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ adrRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs adrRelocs adrWords a resolve)) :
    subroutine_ok prog a (getSymAddrSpec (resolve "near_sym")) := by
  wp_init u s0
  wp_sym_steps
  wp_done

-- Relocation-range lookup skips a decoy `∀`-range hypothesis over a non-matching relocation list:
#guard_msgs in
theorem adr_wp_sym_steps_ok_decoy_range (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (_hdecoy : ∀ r ∈ getSymAddrRelocs,
      Obj.CodeRelocInRange r.kind (a + 64#64 + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hrange : ∀ r ∈ adrRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs adrRelocs adrWords a resolve)) :
    subroutine_ok prog a (getSymAddrSpec (resolve "near_sym")) := by
  wp_init u s0
  wp_sym_steps
  wp_done

/-- `R_AARCH64_LDST32_ABS_LO12_NC` (`adrp x8, sym32; ldr w0, [x8, :lo12:sym32]; ret`) via `sym_block`. -/
def readU32Words : List (BitVec 32) :=
  [0x90000008#32, 0xb9400100#32, 0xd65f03c0#32]

def readU32Relocs : List Obj.RelocEntry :=
  [ { off := 0, kind := .adrpHi21, sym := "sym32", addend := 0 }
  , { off := 4, kind := .ldst32Lo12, sym := "sym32", addend := 0 } ]

c_spec readU32Spec (ctx addr32 : BitVec 64) (ghost v : BitVec 32) : (ret : u32)
  preserves addr32 ↦₃₂ v
  ensures_pure ret = v

theorem readU32_sym_block_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ readU32Relocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs readU32Relocs readU32Words a resolve)) :
    subroutine_ok prog a (readU32Spec (resolve "sym32")) := by
  wp_init v s0
  sym_block
  wp_done

/-- `R_AARCH64_LDST16_ABS_LO12_NC` (`adrp x8, sym16; ldrh w0, [x8, :lo12:sym16]; ret`) via `wp_sym_steps`. -/
def readU16Words : List (BitVec 32) :=
  [0x90000008#32, 0x79400100#32, 0xd65f03c0#32]

def readU16Relocs : List Obj.RelocEntry :=
  [ { off := 0, kind := .adrpHi21, sym := "sym16", addend := 0 }
  , { off := 4, kind := .ldst16Lo12, sym := "sym16", addend := 0 } ]

c_spec readU16Spec (ctx addr16 : BitVec 64) (ghost v : BitVec 16) : (ret : u64)
  preserves addr16 ↦₁₆ v
  ensures_pure ret = v.zeroExtend 64

theorem readU16_wp_sym_steps_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ readU16Relocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs readU16Relocs readU16Words a resolve)) :
    subroutine_ok prog a (readU16Spec (resolve "sym16")) := by
  wp_init v s0
  wp_sym_steps
  wp_done

/-- Multi-relocation fetch test exercising `arm64_code_at` (`tryCloseFetchFromHasCode`) across
    `JUMP26` (`B`), `CONDBR19` (`B.eq` and `CBZ`), `LD_PREL_LO19` (`LDR` literal), `TSTBR14` (`TBZ`),
    `ADR_PREL_PG_HI21_NC` (`ADRP` unchecked), and `LDST128_ABS_LO12_NC` (128-bit SIMD `LDR Q0`). -/
def allRelocFetchWords : List (BitVec 32) :=
  [ 0x14000000#32  -- +0:  B callee          (JUMP26)
  , 0x54000000#32  -- +4:  B.eq lbl          (CONDBR19)
  , 0xb4000000#32  -- +8:  CBZ x0, lbl       (CONDBR19)
  , 0x58000000#32  -- +12: LDR x0, lit_sym   (LD_PREL_LO19)
  , 0x36000000#32  -- +16: TBZ w0, #0, lbl   (TSTBR14)
  , 0x90000000#32  -- +20: ADRP x0, far_sym  (ADR_PREL_PG_HI21_NC)
  , 0x3dc00100#32  -- +24: LDR q0, [x8, #0]  (LDST128_ABS_LO12_NC)
  ]

def allRelocFetchRelocs : List Obj.RelocEntry :=
  [ { off := 0,  kind := .jump26,      sym := "callee",  addend := 0 }
  , { off := 4,  kind := .condbr19,    sym := "lbl",     addend := 0 }
  , { off := 8,  kind := .condbr19,    sym := "lbl",     addend := 0 }
  , { off := 12, kind := .ldPrelLo19,  sym := "lit_sym", addend := 0 }
  , { off := 16, kind := .tstbr14,     sym := "lbl",     addend := 0 }
  , { off := 20, kind := .adrpHi21Nc,  sym := "far_sym", addend := 0 }
  , { off := 24, kind := .ldst128Lo12, sym := "s128",    addend := 0 }
  ]

set_option linter.literalFetch false in
theorem allRelocFetch_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ allRelocFetchRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs allRelocFetchRelocs allRelocFetchWords a resolve)) :
    prog.fetch a = some (.b (resolve "callee" - a)) ∧
    prog.fetch (a + 4#64) =
      some (.bCond .EQ (resolve "lbl" - (a + 4#64))) ∧
    prog.fetch (a + 8#64) =
      some (.cbz .W64 false (.gpr 0#5) (resolve "lbl" - (a + 8#64))) ∧
    prog.fetch (a + 12#64) =
      some (.ldrLit .W64 false (.gpr 0#5) (resolve "lit_sym" - (a + 12#64))) ∧
    prog.fetch (a + 16#64) =
      some (.tbz .W32 false (.gpr 0#5) 0 (resolve "lbl" - (a + 16#64))) ∧
    prog.fetch (a + 20#64) =
      some (.adr true (.gpr 0#5)
        (((Obj.pageOf (resolve "far_sym") - Obj.pageOf (a + 20#64)).extractLsb' 12 21).signExtend 64 <<< 12)) ∧
    prog.fetch (a + 24#64) =
      some (.ldrSimd .Q128 0#5 (.Offset (.gpr 8#5) (Obj.lo12Of (resolve "s128")))) := by
  refine ⟨by arm64_code_at, by arm64_code_at, by arm64_code_at, by arm64_code_at,
          by arm64_code_at, by arm64_code_at, by arm64_code_at⟩

/-! ## Linker Veneer Trampoline -/

theorem veneer_transfers_subroutine_ok (prog : Program) (vAddr target : BitVec 64)
    (hveneer : Obj.VeneerAt prog vAddr target)
    (hcallee : subroutine_ok prog target (getSymAddrSpec target)) :
    subroutine_ok prog vAddr (getSymAddrSpec target) :=
  Obj.subroutine_ok_of_veneerAt hveneer hcallee
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)

/-! ## Negative `#guard_msgs` and `honours = false` Checks -/

/--
error: sym_block: no instruction could be executed (no fetch at +0000000000000000)
-/
#guard_msgs (error, drop info) in
theorem adrp_missing_range_rejected (prog : Program) (a target : BitVec 64)
    (hwords : prog.hasWords a
      [Obj.adrpWord 0x90000000#32 a target,
       Obj.lo12Word 0 0x91000000#32 target,
       0xd65f03c0#32]) :
    subroutine_ok prog a (getSymAddrSpec target) := by
  wp_init u s0
  sym_block
  wp_done

/--
error: sym_block: no instruction could be executed (no fetch at +0000000000000000)
-/
#guard_msgs (error, drop info) in
theorem ldr64_missing_alignment_rejected (prog : Program) (a target : BitVec 64)
    (hwords : prog.hasWords a
      [Obj.lo12Word 3 0xf9400000#32 target,
       0xd65f03c0#32]) :
    subroutine_ok prog a (getSymAddrSpec target) := by
  wp_init u s0
  sym_block
  wp_done

/--
error: wp_step: could not fetch/decode instruction at PC `a`
hint: check (1) the `*Fns.lean` / `*Code.lean` decode module is imported or a `hasWords` / `hasCode` / `code_fetches` hypothesis is in context, (2) the PC offset is normalized (e.g. `entry + <off>#64`; try `wp_simp_pre` or `examples_generalize_entry`), or (3) execution did not step past function exit or into an un-inlined `BL` callee
-/
#guard_msgs (error, drop info) in
theorem wp_step_adrp_missing_range_rejected (prog : Program) (a target : BitVec 64)
    (hwords : prog.hasWords a
      [Obj.adrpWord 0x90000000#32 a target,
       Obj.lo12Word 0 0x91000000#32 target,
       0xd65f03c0#32]) :
    subroutine_ok prog a (getSymAddrSpec target) := by
  wp_init u s0
  wp_step

/--
error: wp_step: could not fetch/decode instruction at PC `a`
hint: check (1) the `*Fns.lean` / `*Code.lean` decode module is imported or a `hasWords` / `hasCode` / `code_fetches` hypothesis is in context, (2) the PC offset is normalized (e.g. `entry + <off>#64`; try `wp_simp_pre` or `examples_generalize_entry`), or (3) execution did not step past function exit or into an un-inlined `BL` callee
-/
#guard_msgs (error, drop info) in
theorem wp_step_mismatched_scale_rejected (prog : Program) (a target : BitVec 64)
    (hal : Obj.Lo12Aligned 2 target)
    (hwords : prog.hasWords a
      [Obj.lo12Word 2 0xf9400000#32 target,
       0xd65f03c0#32]) :
    subroutine_ok prog a (getSymAddrSpec target) := by
  wp_init u s0
  wp_step

theorem honours_zero_align_rejected :
    testLinkedImage.honours
      { testRelocObj with
        dataSyms := [{ sym := "ro_magic", align := 0, readOnly := true, bytes := [0x2a#8], relocs := [] }] } = false := by
  decide

theorem honours_abs64_in_code_rejected :
    testLinkedImage.honours
      { testRelocObj with
        relocFns := [{ sym := "bump_counter"
                       code := wordsToBytesLE bumpCounterWords
                       relocs := [{ off := 0, kind := .abs64, sym := "counter", addend := 0 }] }] } = false := by
  decide

theorem img_fnAddr_pc_base_sym_block_ok (prog : Program) (img : Obj.Image)
    (resolve : String → BitVec 64)
    (hrange : ∀ r ∈ getSymAddrRelocs,
      Obj.CodeRelocInRange r.kind (img.fnAddr "get_sym_addr" + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords (img.fnAddr "get_sym_addr")
      (Obj.patchRelocs getSymAddrRelocs getSymAddrWords (img.fnAddr "get_sym_addr") resolve)) :
    subroutine_ok prog (img.fnAddr "get_sym_addr") (getSymAddrSpec (resolve "my_table")) := by
  wp_init u s0
  sym_block
  wp_done

/-! ## Symbol-Relative Cut Points -/

/-- Bytes for `bump_twice_and_add_ro` (`8` words, `32` bytes):
    `+0`:  `stp x29, x30, [sp, #-16]!`     (`0xa9bf7bfd`)
    `+4`:  `bl bump_counter` (1st call)    (`0x94000000`)
    `+8`:  `bl bump_counter` (2nd call)    (`0x94000000`)
    `+12`: `adrp x8, ro_magic`             (`0x90000008`)
    `+16`: `ldr x9, [x8, :lo12:ro_magic]`  (`0xf9400109`)
    `+20`: `add x0, x0, x9`                (`0x8b090000`)
    `+24`: `ldp x29, x30, [sp], #16`       (`0xa8c17bfd`)
    `+28`: `ret`                           (`0xd65f03c0`) -/
def bumpTwiceAndAddRoWords : List (BitVec 32) :=
  [ 0xa9bf7bfd#32, 0x94000000#32, 0x94000000#32, 0x90000008#32
  , 0xf9400109#32, 0x8b090000#32, 0xa8c17bfd#32, 0xd65f03c0#32 ]

def bumpTwiceAndAddRoRelocs : List Obj.RelocEntry :=
  [ { off := 4,  kind := .call26,     sym := "bump_counter", addend := 0 }
  , { off := 8,  kind := .call26,     sym := "bump_counter", addend := 0 }
  , { off := 12, kind := .adrpHi21,   sym := "ro_magic",     addend := 0 }
  , { off := 16, kind := .ldst64Lo12, sym := "ro_magic",     addend := 0 } ]

#guard_expr (reloc_call_off% bumpTwiceAndAddRoRelocs "bump_counter") =ₛ 4#64
#guard_expr (reloc_call_off% bumpTwiceAndAddRoRelocs "bump_counter" 1) =ₛ 8#64
#guard_expr (words_ret_off% bumpTwiceAndAddRoWords) =ₛ 28#64
example : Obj.findCallOff bumpTwiceAndAddRoRelocs "bump_counter" 0 = 4#64 := rfl
example : Obj.findCallOff bumpTwiceAndAddRoRelocs "bump_counter" 1 = 8#64 := rfl
example : Obj.findRetOff bumpTwiceAndAddRoWords 0 = 28#64 := rfl

theorem bumpTwiceAndAddRo_sepWPp_named_cuts_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64) (v : BitVec 64)
    (hrange : ∀ r ∈ bumpTwiceAndAddRoRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs bumpTwiceAndAddRoRelocs bumpTwiceAndAddRoWords a resolve))
    (hcallee : subroutine_ok prog (resolve "bump_counter") (bumpCounterSpec (resolve "counter"))) :
    subroutine_ok prog a
      { pre := fun (_ : Unit) s =>
          (resolve "counter" ↦₆₄ v) ∗
          (resolve "ro_magic" ↦₆₄ 42#64) ∗
          stackFrameAt s.sp 16
        post := fun _ _ sf =>
          ⌜sf.readReg64 (.gpr 0#5) = v + 1#64 + 1#64 + 42#64⌝ ∗
          (resolve "counter" ↦₆₄ (v + 1#64 + 1#64)) ∗
          (resolve "ro_magic" ↦₆₄ 42#64) ∗
          stackFrameAt sf.sp 16 } := by
  wpp_init u s0
  sepWPp_cut_call bumpTwiceAndAddRoRelocs "bump_counter" 0
  wp_steps_to_call bumpTwiceAndAddRoRelocs "bump_counter" 0
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  apply SepWPp.of_sepWP (mid := a + reloc_call_off% bumpTwiceAndAddRoRelocs "bump_counter" 1)
  wp_step
  wp_call hcallee
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  apply SepWPp.of_sepWP_ret
  wp_step
  wp_call hcallee
  wp_sym_steps_to_ret bumpTwiceAndAddRoWords
  wp_sym_step
  wp_done

theorem bumpTwiceAndAddRo_sepWP_named_cuts_ok (prog : Program) (a : BitVec 64)
    (resolve : String → BitVec 64) (v : BitVec 64)
    (hrange : ∀ r ∈ bumpTwiceAndAddRoRelocs,
      Obj.CodeRelocInRange r.kind (a + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords a (Obj.patchRelocs bumpTwiceAndAddRoRelocs bumpTwiceAndAddRoWords a resolve))
    (hcallee : subroutine_ok prog (resolve "bump_counter") (bumpCounterSpec (resolve "counter"))) :
    subroutine_ok prog a
      { pre := fun (_ : Unit) s =>
          (resolve "counter" ↦₆₄ v) ∗
          (resolve "ro_magic" ↦₆₄ 42#64) ∗
          stackFrameAt s.sp 16
        post := fun _ _ sf =>
          ⌜sf.readReg64 (.gpr 0#5) = v + 1#64 + 1#64 + 42#64⌝ ∗
          (resolve "counter" ↦₆₄ (v + 1#64 + 1#64)) ∗
          (resolve "ro_magic" ↦₆₄ 42#64) ∗
          stackFrameAt sf.sp 16 } := by
  wp_init u s0
  wp_cut_call bumpTwiceAndAddRoRelocs "bump_counter"
  wp_steps_to_call bumpTwiceAndAddRoRelocs "bump_counter"
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  apply SepWP.cut (mid := a + reloc_call_off% bumpTwiceAndAddRoRelocs "bump_counter" 1)
  wp_step
  wp_call hcallee
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  wp_step
  wp_call hcallee
  wp_steps_to_ret bumpTwiceAndAddRoWords
  wp_step
  wp_done

/-! ## `TLSDESC` to `TLSLE` Relaxation and Direct `TLSLE` Decode Lemmas -/

theorem tlsdesc_to_tlsle_decode_ok (tprel : BitVec 64) :
    decode (Obj.tlsdescAdrPage21Word tprel) =
      some (.moveWide .W64 .MOVZ .x0 (tprel.extractLsb' 16 16) 16) ∧
    decode (Obj.tlsdescLd64Lo12Word tprel) =
      some (.moveWide .W64 .MOVK .x0 (tprel.extractLsb' 0 16) 0) :=
  ⟨Obj.decode_tlsdescAdrPage21Word tprel, Obj.decode_tlsdescLd64Lo12Word tprel⟩

theorem tlsle_hi12_and_lo12_decode_ok (tprel : BitVec 64) :
    decode (Obj.tprelHi12Word 0x91400108#32 tprel) =
      some (.addSubImm .W64 .ADD
        (Reg.fromSPBits 8#5) (Reg.fromSPBits 8#5)
        (tprel.extractLsb' 12 12) true) ∧
    decode (Obj.lo12Word 0 0x91000108#32 tprel) =
      some (.addSubImm .W64 .ADD
        (Reg.fromSPBits 8#5) (Reg.fromSPBits 8#5)
        ((Obj.lo12Of tprel).truncate 12) false) :=
  ⟨Obj.decode_tprelHi12Word rfl tprel,
   Obj.decode_addLo12Word rfl tprel⟩

/-! ## `checkRelocFn` and `checkRelocFnAt` Edge Cases -/

section CheckRelocFnEdgeCases

open ProofLib.ProgramReflection

/-- Clean instruction templates exercising every distinct code relocation mask family. -/
def allRelocKindWords : List (BitVec 32) :=
  [ 0x94000000#32 -- +0:  call26       (BL)
  , 0x14000000#32 -- +4:  jump26       (B)
  , 0x90000008#32 -- +8:  adrpHi21     (ADRP X8)
  , 0xb0000009#32 -- +12: adrpHi21Nc   (ADRP X9)
  , 0x1000000a#32 -- +16: adrPrelLo21  (ADR X10)
  , 0x91000108#32 -- +20: addLo12      (ADD X8, X8, #0)
  , 0x3940010b#32 -- +24: ldst8Lo12    (LDRB W11, [X8])
  , 0x7940010c#32 -- +28: ldst16Lo12   (LDRH W12, [X8])
  , 0xb940010d#32 -- +32: ldst32Lo12   (LDR W13, [X8])
  , 0xf940010e#32 -- +36: ldst64Lo12   (LDR X14, [X8])
  , 0x3dc00100#32 -- +40: ldst128Lo12  (LDR Q0, [X8])
  , 0x54000000#32 -- +44: condbr19     (B.EQ)
  , 0x5800000f#32 -- +48: ldPrelLo19   (LDR X15, label)
  , 0x36000010#32 -- +52: tstbr14      (TBZ W16, #0, label)
  , 0xd65f03c0#32 -- +56: non-relocated RET
  ]

/-- Object words with non-zero immediate link placeholders sharing the opcode and register mask
    bits of `allRelocKindWords`. -/
def allRelocKindPatchedWords : List (BitVec 32) :=
  (allRelocKindWords.take 14).zip
    [ Obj.RelocKind.call26, .jump26, .adrpHi21, .adrpHi21Nc, .adrPrelLo21, .addLo12
    , .ldst8Lo12, .ldst16Lo12, .ldst32Lo12, .ldst64Lo12, .ldst128Lo12
    , .condbr19, .ldPrelLo19, .tstbr14 ]
  |>.map (fun (w, k) => w ||| (~~~Obj.relocOpcodeMask k &&& 0xdeadbeef#32))
  |>.concat 0xd65f03c0#32

def allRelocKindRelocs : List Obj.RelocEntry :=
  [ { off := 0,  kind := .call26,      sym := "t" }
  , { off := 4,  kind := .jump26,      sym := "t" }
  , { off := 8,  kind := .adrpHi21,    sym := "t" }
  , { off := 12, kind := .adrpHi21Nc,  sym := "t" }
  , { off := 16, kind := .adrPrelLo21, sym := "t" }
  , { off := 20, kind := .addLo12,     sym := "t" }
  , { off := 24, kind := .ldst8Lo12,   sym := "t" }
  , { off := 28, kind := .ldst16Lo12,  sym := "t" }
  , { off := 32, kind := .ldst32Lo12,  sym := "t" }
  , { off := 36, kind := .ldst64Lo12,  sym := "t" }
  , { off := 40, kind := .ldst128Lo12, sym := "t" }
  , { off := 44, kind := .condbr19,    sym := "t" }
  , { off := 48, kind := .ldPrelLo19,  sym := "t" }
  , { off := 52, kind := .tstbr14,     sym := "t" } ]

def allRelocKindObj : Obj.ObjectInfo where
  name := "all_kinds.o"
  relocFns := [{ sym := "all_kinds", code := wordsToBytesLE allRelocKindPatchedWords,
                 relocs := allRelocKindRelocs }]

example : checkRelocFn allRelocKindObj "all_kinds" allRelocKindRelocs allRelocKindWords = true := by
  decide +kernel
example : checkRelocFnAt allRelocKindObj 0 "all_kinds" allRelocKindRelocs allRelocKindWords = true := by
  decide +kernel
example : allRelocKindObj.RelocFnChecked "all_kinds" allRelocKindRelocs allRelocKindWords :=
  Obj.ObjectInfo.RelocFnChecked.of_checkRelocFnAt (idx := 0) (by decide +kernel)

example : checkRelocFn testRelocObj "bump_counter" bumpCounterRelocs
    (bumpCounterWords.set 0 0x90000001#32) = false := by
  decide +kernel

example : checkRelocFn testRelocObj "bump_counter" bumpCounterRelocs
    (bumpCounterWords.set 2 0x91000929#32) = false := by
  decide +kernel

example : checkRelocFn { name := "empty.o", relocFns := [{ sym := "f", code := [] }] }
    "f" [] [] = false := by decide +kernel

example : checkRelocFn testRelocObj "bump_counter" bumpCounterRelocs
    (bumpCounterWords.take 4) = false := by decide +kernel
example : checkRelocFn testRelocObj "bump_counter" bumpCounterRelocs
    (bumpCounterWords ++ [0xd65f03c0#32]) = false := by decide +kernel

example : checkRelocFn
    { name := "odd.o", relocFns := [{ sym := "f", code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8, 0x00#8] }] }
    "f" [] [0xd65f03c0#32] = false := by decide +kernel

example : checkRelocWordsStream (wordsToBytesLE bumpCounterWords) bumpCounterWords
    (bumpCounterRelocs.reverse) 0 = false := by decide +kernel

example : checkRelocWordsStream (wordsToBytesLE bumpCounterWords) bumpCounterWords
    [ { off := 0, kind := .adrpHi21, sym := "counter" }
    , { off := 0, kind := .adrpHi21, sym := "counter" } ] 0 = false := by decide +kernel

example : checkRelocWordsStream (wordsToBytesLE bumpCounterWords) bumpCounterWords
    [{ off := 2, kind := .adrpHi21, sym := "counter" }] 0 = false := by decide +kernel

example : checkRelocWordsStream (wordsToBytesLE bumpCounterWords) bumpCounterWords
    (bumpCounterRelocs ++ [{ off := 24, kind := .call26, sym := "counter" }]) 0 = false := by
  decide +kernel

example : checkRelocFnAt testRelocObj 1 "bump_counter" bumpCounterRelocs bumpCounterWords = false := by
  decide +kernel
example : checkRelocFnAt testRelocObj 99 "bump_counter" bumpCounterRelocs bumpCounterWords = false := by
  decide +kernel
example : checkRelocFn testRelocObj "missing_fn" bumpCounterRelocs bumpCounterWords = false := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  checkRelocFn testRelocObj "bump_counter" bumpCounterRelocs (bumpCounterWords.set 2 2432698665#32) = true
is false
-/
#guard_msgs (error, drop info) in
example : checkRelocFn testRelocObj "bump_counter" bumpCounterRelocs
    (bumpCounterWords.set 2 0x91000929#32) = true := by
  decide +kernel

end CheckRelocFnEdgeCases

end Testing.LayoutGenericRelocs
