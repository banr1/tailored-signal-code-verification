/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.GenDecodes
public import ProofLib.ObjectLoad

/-!
# Tests for `ProofLib.GenDecodes`

Tests `gen_decodes`, `gen_fetches`, and `gen_concrete_fetches` across single offsets, ranges,
`raw` mode, undecodable padding words, structural theorem-type equality against hand-written
reference lemmas, and diagnostic error cases.
-/

@[expose] public section

namespace Examples.Testing.GenDecodesTest

open Arm64 ProofLib.ProgramReflection ProofLib.GenDecodes

/-! ## Synthetic program fixture (`widgetCode`) -/

/-- Synthetic 8-word instruction stream:
* `0x00`: `0xa9bf7bfd` (`stp x29, x30, [sp, #-16]!`)
* `0x04`: `0x910003fd` (`mov x29, sp`)
* `0x08`: `0x8b010800` (`add x0, x0, x1, lsl #2`)
* `0x0c`: `0x92401c00` (`and x0, x0, #0xff`)
* `0x10`: `0x34000040` (`cbz w0, #0x18`)
* `0x14`: `0x00000000` (undecodable zero word)
* `0x18`: `0xa8c17bfd` (`ldp x29, x30, [sp], #16`)
* `0x1c`: `0xd65f03c0` (`ret`) -/
def widgetCode : Program :=
  Program.ofWords 0#64
    [ 0xa9bf7bfd#32, 0x910003fd#32, 0x8b010800#32, 0x92401c00#32
    , 0x34000040#32, 0x00000000#32, 0xa8c17bfd#32, 0xd65f03c0#32 ]

abbrev widgetCodeTextEnd : Nat := 0x1c

def widgetCode_tree : WordTree :=
  .node 4
    (.node 2
      (.node 1 (.leaf 0xfd#8 0x7b#8 0xbf#8 0xa9#8) (.leaf 0xfd#8 0x03#8 0x00#8 0x91#8))
      (.node 1 (.leaf 0x00#8 0x08#8 0x01#8 0x8b#8) (.leaf 0x00#8 0x1c#8 0x40#8 0x92#8)))
    (.node 2
      (.node 1 (.leaf 0x40#8 0x00#8 0x00#8 0x34#8) (.leaf 0x00#8 0x00#8 0x00#8 0x00#8))
      (.node 1 (.leaf 0xfd#8 0x7b#8 0xc1#8 0xa8#8) (.leaf 0xc0#8 0x03#8 0x5f#8 0xd6#8)))

theorem widgetCode_code_eq : widgetCode.code = widgetCode_tree.toBytes := by rfl_kernel

theorem widgetCode_tree_size : widgetCode_tree.checkSize? = some 8 := by rfl_kernel

theorem widgetCode_noStubBefore : noStubBefore widgetCodeTextEnd widgetCode.stubs = true := by
  rfl_kernel

theorem widgetCode_fetch_at {off : Nat} {inst : Instr}
    (h : widgetCode_tree.fetchDecodeAt off = some inst) (hoff : off < 2 ^ 64 := by decide) :
    widgetCode.fetch (BitVec.ofNat 64 off) = some inst := by
  have h' := fetch_of_wordTree 8 widgetCode_code_eq widgetCode_tree_size h hoff
  rwa [show widgetCode.base = 0#64 from rfl, BitVec.zero_add] at h'

theorem widgetCode_fetch_rebase {b : BitVec 64} {X O : String → Option (State → State)}
    {off : Nat} {inst : Instr}
    (h : widgetCode_tree.fetchDecodeAt off = some inst)
    (hhook : (widgetCode.rebase b X O).hookAtOff? off = none)
    (hoff : off < 2 ^ 64 := by decide) :
    (widgetCode.rebase b X O).fetch (b + BitVec.ofNat 64 off) = some inst :=
  (Program.fetch_rebase_eq_of_hookAtOff? rfl (fun _ => rfl) (fun _ => rfl) hoff hhook).trans
    (widgetCode_fetch_at h hoff)

theorem widgetCode_fetch_rebase_text {b : BitVec 64} {X : String → Option (State → State)}
    {off : Nat} {inst : Instr}
    (h : widgetCode_tree.fetchDecodeAt off = some inst)
    (htext : off < widgetCodeTextEnd := by decide)
    (hoff : off < 2 ^ 64 := by decide) :
    (widgetCode.rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst :=
  widgetCode_fetch_rebase h
    (hookAtOff?_eq_none_of_noStubBefore widgetCode_noStubBefore (fun _ => rfl) htext) hoff

/-! ## Reference static theorems for structural statement comparison -/

section ReferenceFixtures
set_option linter.literalFetch false

theorem widgetExpected_decode_0x0 :
    widgetCode_tree.fetchDecodeAt 0x0 =
      some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp (-16#64))) := by
  rfl_kernel

theorem widgetExpected_fetch_0x0 :
    widgetCode.fetch 0x0#64 =
      some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp (-16#64))) :=
  widgetCode_fetch_at widgetExpected_decode_0x0

theorem widgetExpected_rebase_fetch_0x0
    (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetCode.rebase b X).fetch (b + 0x0#64) =
      some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp (-16#64))) :=
  widgetCode_fetch_rebase_text widgetExpected_decode_0x0

theorem widgetExpected_rebase_fetch_base
    (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetCode.rebase b X).fetch b =
      some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp (-16#64))) := by
  simpa using widgetExpected_rebase_fetch_0x0 b X

theorem widgetExpected_decode_0x4 :
    widgetCode_tree.fetchDecodeAt 0x4 =
      some (.addSubImm .W64 .ADD (.gpr 29#5) .sp 0x0#12 false) := by
  rfl_kernel

theorem widgetExpected_decode_0x8 :
    widgetCode_tree.fetchDecodeAt 0x8 =
      some (.addSubShift .W64 .ADD (.gpr 0#5) (.gpr 0#5) (.gpr 1#5) .LSL 2) := by
  rfl_kernel

theorem widgetExpected_decode_0xc :
    widgetCode_tree.fetchDecodeAt 0xc =
      some (.logicalImm .W64 .AND (.gpr 0#5) (.gpr 0#5) 0xff#64) := by
  rfl_kernel

theorem widgetExpected_decode_0x10 :
    widgetCode_tree.fetchDecodeAt 0x10 =
      some (.cbz .W32 false (.gpr 0#5) 0x8#64) := by
  rfl_kernel

theorem widgetExpected_decode_0x18 :
    widgetCode_tree.fetchDecodeAt 0x18 =
      some (.ldp .W64 false (.gpr 29#5) (.gpr 30#5) (.PostIndex .sp 0x10#64)) := by
  rfl_kernel

theorem widgetExpected_decode_0x1c :
    widgetCode_tree.fetchDecodeAt 0x1c =
      some (.ret (.gpr 30#5)) := by
  rfl_kernel

theorem widgetExpected_fetch_0x1c :
    widgetCode.fetch 0x1c#64 =
      some (.ret (.gpr 30#5)) :=
  widgetCode_fetch_at widgetExpected_decode_0x1c

end ReferenceFixtures

/-! ## Positive tests: `gen_fetches` and `gen_decodes` -/

-- `gen_fetches` with implicit `widgetCodeTextEnd` (0x1c), `root = true`, spanning an undecodable
-- word at `0x14` (skipped) and offset `0x1c == widgetCodeTextEnd` (emits `decode` and `fetch`,
-- omits `rebase_fetch`).
gen_fetches widgetCode widgetBin true [0x0 → 0x1c]

-- `gen_fetches` with explicit `textEnd` and `root = false`.
gen_fetches widgetCode widgetSub 0x1c false [0x0 → 0x4]

-- `gen_decodes` with single offset, range, and `raw` mode.
gen_decodes widgetCode_tree widgetOnlyDec [0x0, 0x4 → 0xc, raw 0x18]

/-- Concrete-base fixture (`0x400000`) for `gen_concrete_fetches`. -/
def widgetConcreteCode : Program :=
  Program.ofWords 0x400000#64
    [ 0xa9bf7bfd#32, 0x910003fd#32, 0x8b010800#32, 0x92401c00#32
    , 0x34000040#32, 0x00000000#32, 0xa8c17bfd#32, 0xd65f03c0#32 ]

theorem widgetConcreteCode_code_eq : widgetConcreteCode.code = widgetCode_tree.toBytes := by rfl_kernel

theorem widgetConcreteCode_fetch_addr {off : Nat} {addr : BitVec 64} {inst : Instr}
    (h : widgetCode_tree.fetchDecodeAt off = some inst)
    (haddr : 0x400000#64 + BitVec.ofNat 64 off = addr)
    (hb : Nat.ble off 0x10000 = true) :
    widgetConcreteCode.fetch addr = some inst :=
  haddr ▸ fetch_of_wordTree 8 widgetConcreteCode_code_eq widgetCode_tree_size h
    (Nat.lt_of_le_of_lt (Nat.le_of_ble_eq_true hb) (by decide))

gen_concrete_fetches widgetConcrete widgetCode_tree widgetConcreteCode_fetch_addr 0x400000
  [(0x0, 0x8), (0x18, 0x1c)]

example :
    widgetConcreteCode.fetch 0x400000#64 =
      some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp (-16#64))) := by
  simp only [arm64_norm]

example :
    widgetConcreteCode.fetch 0x40001c#64 =
      some (.ret (.gpr 30#5)) := by
  simp only [arm64_norm]

-- Verify structural equality (`ConstantInfo.type ==`) between `gen_fetches` and static theorems.
open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let pairs := #[
    (`Examples.Testing.GenDecodesTest.widgetBin_decode_0x0,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0x0),
    (`Examples.Testing.GenDecodesTest.widgetBin_fetch_0x0,
     `Examples.Testing.GenDecodesTest.widgetExpected_fetch_0x0),
    (`Examples.Testing.GenDecodesTest.widgetBin_rebase_fetch_0x0,
     `Examples.Testing.GenDecodesTest.widgetExpected_rebase_fetch_0x0),
    (`Examples.Testing.GenDecodesTest.widgetBin_rebase_fetch_base,
     `Examples.Testing.GenDecodesTest.widgetExpected_rebase_fetch_base),
    (`Examples.Testing.GenDecodesTest.widgetCode_fetch_0x0,
     `Examples.Testing.GenDecodesTest.widgetExpected_fetch_0x0),
    (`Examples.Testing.GenDecodesTest.widgetCode_rebase_fetch_0x0,
     `Examples.Testing.GenDecodesTest.widgetExpected_rebase_fetch_0x0),
    (`Examples.Testing.GenDecodesTest.widgetCode_rebase_fetch_base,
     `Examples.Testing.GenDecodesTest.widgetExpected_rebase_fetch_base),
    (`Examples.Testing.GenDecodesTest.widgetBin_decode_0x4,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0x4),
    (`Examples.Testing.GenDecodesTest.widgetBin_decode_0x8,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0x8),
    (`Examples.Testing.GenDecodesTest.widgetBin_decode_0xc,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0xc),
    (`Examples.Testing.GenDecodesTest.widgetBin_decode_0x10,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0x10),
    (`Examples.Testing.GenDecodesTest.widgetBin_decode_0x18,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0x18),
    (`Examples.Testing.GenDecodesTest.widgetBin_decode_0x1c,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0x1c),
    (`Examples.Testing.GenDecodesTest.widgetBin_fetch_0x1c,
     `Examples.Testing.GenDecodesTest.widgetExpected_fetch_0x1c),
    (`Examples.Testing.GenDecodesTest.widgetOnlyDec_decode_0x0,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0x0),
    (`Examples.Testing.GenDecodesTest.widgetOnlyDec_decode_0xc,
     `Examples.Testing.GenDecodesTest.widgetExpected_decode_0xc)
  ]
  for (genName, expName) in pairs do
    let some ciGen := env.find? genName | throwError "missing generated theorem {genName}"
    let some ciExp := env.find? expName | throwError "missing expected theorem {expName}"
    unless ciGen.type == ciExp.type do
      throwError "statement mismatch for {genName}:\n  got:  {ciGen.type}\n  want: {ciExp.type}"
  -- Undecodable word at 0x14 must be skipped by `gen_fetches`.
  if env.contains `Examples.Testing.GenDecodesTest.widgetBin_decode_0x14 then
    throwError "expected undecodable offset 0x14 to be skipped by gen_fetches"
  -- Offset 0x1c == widgetCodeTextEnd must not emit rebase_fetch.
  if env.contains `Examples.Testing.GenDecodesTest.widgetBin_rebase_fetch_0x1c then
    throwError "expected offset 0x1c >= textEnd to omit rebase_fetch"

-- Verify `@[simp]` and `@[arm64_norm]` discharge fetch goals directly.
example (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetCode.rebase b X).fetch b =
      some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.PreIndex .sp (-16#64))) := by
  simp

example (b : BitVec 64) (X : String → Option (State → State)) :
    (widgetCode.rebase b X).fetch (b + 0x8#64) =
      some (.addSubShift .W64 .ADD (.gpr 0#5) (.gpr 0#5) (.gpr 1#5) .LSL 2) := by
  simp only [arm64_norm]

/-! ## Negative tests (`#guard_msgs`) -/

/-- error: gen_decodes: offset 2 is not 4-byte aligned -/
#guard_msgs in
gen_decodes widgetCode_tree widgetBadAlign [0x2]

/-- error: gen_decodes: word index out of range -/
#guard_msgs in
gen_decodes widgetCode_tree widgetBadRange [0x20]

/-- error: gen_decodes: the word 0x00000000#32 at offset 20 does not decode (at 0x14: unsupported instruction encoding (insn 0x00000000) — not modeled in Arm64/Trusted/ISA) -/
#guard_msgs in
gen_decodes widgetCode_tree widgetBadWord [0x14]

/-- error: gen_decodes: bad range 8 → 4 -/
#guard_msgs in
gen_decodes widgetCode_tree widgetEmptyRange [0x8 → 0x4]

/-- error: gen_concrete_fetches: bad range (8, 4) -/
#guard_msgs in
gen_concrete_fetches widgetBadRange2 widgetCode_tree widgetConcreteCode_fetch_addr 0x400000 [(0x8, 0x4)]

/-- error: gen_concrete_fetches: decode failed at offset 20 -/
#guard_msgs in
gen_concrete_fetches widgetBadWord2 widgetCode_tree widgetConcreteCode_fetch_addr 0x400000 [(0x14, 0x14)]

end Examples.Testing.GenDecodesTest
