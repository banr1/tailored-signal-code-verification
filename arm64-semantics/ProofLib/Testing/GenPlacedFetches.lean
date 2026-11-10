/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public meta import Lean.Elab.Tactic

/-!
# Tests for `gen_placed_fetches` and `gen_placed_fnOffs`

Exercises `gen_placed_fetches` and `gen_placed_fnOffs` across unrelocated chunks, relaxable
`ADRP`+`ADD` pairs, intra-block `call26` and `jump26` branches, branch-to-branch trampolines,
`rd == 31` (`XZR` vs `SP`) relaxation guards, and `RelocTree` / `CharSymVec` validation.
-/

@[expose] public section

namespace Examples.Testing.GenPlacedFetches

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

set_option linter.literalFetch false

/-- `NOP; ADRP X1, tbl; ADD X1, X1, :lo12:tbl; BL helper; RET; helper: RET`, unrelocated. -/
def gadgetBlk : CodeBlock where
  code := bytesOfWordLE 0xd503201f#32 ++ bytesOfWordLE 0x90000001#32 ++
    bytesOfWordLE 0x91000021#32 ++ bytesOfWordLE 0x94000000#32 ++
    bytesOfWordLE 0xd65f03c0#32 ++ bytesOfWordLE 0xd65f03c0#32
  symbols := [("gadget", 0), ("helper", 20)]
  relocs := [{ off := 4, kind := .adrpHi21, sym := "tbl" },
             { off := 8, kind := .addLo12, sym := "tbl" },
             { off := 12, kind := .call26, sym := "helper" }]

def gadgetLib : PlacedLib where
  name := "gadget"
  text := gadgetBlk
  exports := ["gadget"]

/-- The library placed under `pl`. -/
def gadgetPC (pl : Placement) : Program := gadgetLib.program pl

def gadgetTextProg : Program := { code := gadgetBlk.code }

def gadgetTree : WordTree := word_tree_of% gadgetTextProg

theorem gadget_code_eq : gadgetLib.text.code = gadgetTree.toBytes := by rfl_kernel

theorem gadget_tree_size : gadgetTree.checkSize? = some 6 := by rfl_kernel

gen_placed_fetches gadgetPC gadgetLib gadgetTree gadget_code_eq gadget_tree_size [0x0 → 0x14]

/-! ## Positive tests: the generated lemmas -/

example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) :
    ((gadgetPC pl).rebase b X).fetch b = some .nop :=
  gadgetPC_rebase_fetch_base pl b X

/-- The `call26` site decodes to `BL +8` (to `helper`) independently of `pl`. -/
example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) :
    ((gadgetPC pl).rebase b X).fetch (b + 0xc#64) = some (.bl 8#64) :=
  gadgetPC_rebase_fetch_0xc pl b X

example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) :
    ((gadgetPC pl).rebase b X).fetch (b + 0x14#64) = some (.ret (.gpr 30#5)) :=
  gadgetPC_rebase_fetch_0x14 pl b X

/-- The pair lemma sets `X1 := pl.ρ "tbl"` and skips both words. -/
example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) {tgt : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : gadgetLib.Placeable pl) (hb : b = pl.base) (hpc : s.pc = b + 0x4#64)
    (hrun : s.status = .Running)
    (hnext : SepWP ((gadgetPC pl).rebase b X) tgt
      ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).setPC (b + 0xc#64)) P post oom) :
    SepWP ((gadgetPC pl).rebase b X) tgt s P post oom :=
  gadgetPC_pairStep_0x4 pl b X hP hb hpc hrun hnext

/-- The generated lemmas drive `wp_steps`/`wp_step` from offset 0 through the call and back. -/
example (pl : Placement) (s : State) (hP : gadgetLib.Placeable pl)
    (hpc : s.pc = pl.base) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop)
    (hQ : Q (((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).writeReg64 (.gpr 30#5)
      (pl.base + 0x10#64)).setPC (pl.base + 0x10#64)) emp) :
    SepWP ((gadgetPC pl).rebase pl.base (fun _ => none)) (pl.base + 0x10#64) s emp Q
      (fun _ => emp) := by
  wp_steps 3
  wp_step
  wp_steps 1
  wp_done

/-! ## Negative tests -/

/-- error: Unknown identifier `gadgetPC_rebase_fetch_0x4` -/
#guard_msgs (substring := true) in
example := gadgetPC_rebase_fetch_0x4

/-- error: Unknown identifier `gadgetPC_rebase_fetch_0x8` -/
#guard_msgs (substring := true) in
example := gadgetPC_rebase_fetch_0x8

def gadgetPC2 (pl : Placement) : Program := gadgetLib.program pl

/-- error: gen_placed_fetches: offset 24 is out of bounds -/
#guard_msgs (substring := true) in
gen_placed_fetches gadgetPC2 gadgetLib gadgetTree gadget_code_eq gadget_tree_size [0x18]

/-- A relaxable pair with addend `8`: the pair lemma writes `pl.ρ "tbl" + 8`. -/
def addendLib : PlacedLib where
  name := "addend"
  text := { gadgetBlk with
    relocs := [{ off := 4, kind := .adrpHi21, sym := "tbl", addend := 8 },
               { off := 8, kind := .addLo12, sym := "tbl", addend := 8 }] }
  exports := ["gadget"]

def addendPC (pl : Placement) : Program := addendLib.program pl

theorem addend_code_eq : addendLib.text.code = gadgetTree.toBytes := by rfl_kernel

gen_placed_fetches addendPC addendLib gadgetTree addend_code_eq gadget_tree_size [0x4]

example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) {tgt : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : addendLib.Placeable pl) (hb : b = pl.base) (hpc : s.pc = b + 0x4#64)
    (hrun : s.status = .Running)
    (hnext : SepWP ((addendPC pl).rebase b X) tgt
      ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl" + 8#64)).setPC (b + 0xc#64)) P post oom) :
    SepWP ((addendPC pl).rebase b X) tgt s P post oom :=
  addendPC_pairStep_0x4 pl b X hP hb hpc hrun hnext

/-- A relaxable pair with a negative addend. -/
def negAddendLib : PlacedLib where
  name := "negAddend"
  text := { gadgetBlk with
    relocs := [{ off := 4, kind := .adrpHi21, sym := "tbl", addend := -8 },
               { off := 8, kind := .addLo12, sym := "tbl", addend := -8 }] }
  exports := ["gadget"]

def negAddendPC (pl : Placement) : Program := negAddendLib.program pl

theorem negAddend_code_eq : negAddendLib.text.code = gadgetTree.toBytes := by rfl_kernel

/-- error: gen_placed_fetches: relaxable pair at 4 has unsupported addend -8 -/
#guard_msgs (substring := true) in
gen_placed_fetches negAddendPC negAddendLib gadgetTree negAddend_code_eq gadget_tree_size [0x4]

/-- A `call26` with a non-zero addend is skipped (no fetch lemma), with a message. -/
def brAddendLib : PlacedLib where
  name := "brAddend"
  text := { gadgetBlk with
    relocs := [{ off := 12, kind := .call26, sym := "helper", addend := 4 }] }
  exports := ["gadget"]

def brAddendPC (pl : Placement) : Program := brAddendLib.program pl

theorem brAddend_code_eq : brAddendLib.text.code = gadgetTree.toBytes := by rfl_kernel

/-- info: gen_placed_fetches: skipping branch at 12 (nonzero addend) -/
#guard_msgs in
gen_placed_fetches brAddendPC brAddendLib gadgetTree brAddend_code_eq gadget_tree_size [0xc]

/-- error: Unknown identifier `brAddendPC_rebase_fetch_0xc` -/
#guard_msgs (substring := true) in
example := brAddendPC_rebase_fetch_0xc

/-! ## Intra-block `jump26` and branch-to-branch candidates -/

/-- `BL tramp; RET; tramp: B helper; helper: RET`: the `jump26` at `8` gets a fetch lemma (`B +4`
    for every placement); the `call26` at `0` targets a symbol whose first word is a `jump26`, so
    the linker may retarget it (branch-to-branch), and it gets a call-step lemma instead. -/
def trampBlk : CodeBlock where
  code := bytesOfWordLE 0x94000000#32 ++ bytesOfWordLE 0xd65f03c0#32 ++
    bytesOfWordLE 0x14000000#32 ++ bytesOfWordLE 0xd65f03c0#32
  symbols := [("tramp_main", 0), ("tramp", 8), ("helper", 12)]
  relocs := [{ off := 0, kind := .call26, sym := "tramp" },
             { off := 8, kind := .jump26, sym := "helper" }]

def trampLib : PlacedLib where
  name := "tramp"
  text := trampBlk
  exports := ["tramp_main"]

def trampPC (pl : Placement) : Program := trampLib.program pl

def trampTextProg : Program := { code := trampBlk.code }

def trampTree : WordTree := word_tree_of% trampTextProg

theorem tramp_code_eq : trampLib.text.code = trampTree.toBytes := by rfl_kernel

theorem tramp_tree_size : trampTree.checkSize? = some 4 := by rfl_kernel

#guard_msgs in
gen_placed_fetches trampPC trampLib trampTree tramp_code_eq tramp_tree_size [0x0 → 0xc]

example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) :
    ((trampPC pl).rebase b X).fetch (b + 0x8#64) = some (.b 4#64) :=
  trampPC_rebase_fetch_0x8 pl b X

/-- The call-step lemma lands on `helper` with `X30 = b + 4`, for every `b`. -/
example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) {tgt : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : trampLib.Placeable pl) (hpc : s.pc = b + 0x0#64) (hrun : s.status = .Running)
    (hnext : SepWP ((trampPC pl).rebase b X) tgt
      ((s.writeReg64 Reg.lr (b + 0x0#64 + 4#64)).setPC (b + 0xc#64)) P post oom) :
    SepWP ((trampPC pl).rebase b X) tgt s P post oom :=
  trampPC_callStep_0x0 pl b X hP hpc hrun hnext

/- The call-step hook: `wp_steps` takes the branch-to-branch call as one call step and stops at
   `helper` (not at `tramp`), and the helper's `RET` returns to `b + 4`. -/
/-- info: wp_steps: stopped at pc b + 12#64 (target b + 4#64): stopped at subroutine call boundary -/
#guard_msgs (substring := true, whitespace := lax) in
set_option proofLib.wpVerbose true in
example (pl : Placement) (b : BitVec 64) (s : State) (hP : trampLib.Placeable pl)
    (hpc : s.pc = b + 0x0#64) (hrun : s.status = .Running) (Q : State → SepProp → Prop)
    (hQ : Q ((s.writeReg64 (.gpr 30#5) (b + 4#64)).setPC (b + 4#64)) emp) :
    SepWP ((trampPC pl).rebase b (fun _ => none)) (b + 4#64) s emp Q (fun _ => emp) := by
  wp_steps 1
  wp_steps 1
  wp_done

/-- `check_skip_norm prog pc`: report `skipNormFetchAt prog pc` in the main goal's context. -/
elab "check_skip_norm " p:term:max pc:term:max : tactic => Lean.Elab.Tactic.withMainContext do
  let prog ← Lean.Elab.Term.elabTerm p (some (Lean.mkConst ``Arm64.Program))
  let pcE ← Lean.Elab.Term.elabTerm pc (some (Lean.mkApp (Lean.mkConst ``BitVec) (Lean.toExpr 64)))
  Lean.logInfo m!"skip: {← skipNormFetchAt prog pcE}"

/- `skipNormFetchAt`: true at the call-step site `0x0` (so the step tactics skip the
   `arm64_norm` fetch fallback there), false at the ordinary `B` at `0x8`, and false at `0x0` once
   `proofLib.skipNormAtCallStep` is off. -/
/-- info: skip: true -/
#guard_msgs in
set_option linter.unusedVariables false in
example (pl : Placement) (b : BitVec 64) : True := by
  check_skip_norm ((trampPC pl).rebase b (fun _ => none)) (b + 0x0#64)
  trivial

/-- info: skip: false -/
#guard_msgs in
set_option linter.unusedVariables false in
example (pl : Placement) (b : BitVec 64) : True := by
  check_skip_norm ((trampPC pl).rebase b (fun _ => none)) (b + 0x8#64)
  trivial

/-- info: skip: false -/
#guard_msgs in
set_option proofLib.skipNormAtCallStep false in
set_option linter.unusedVariables false in
example (pl : Placement) (b : BitVec 64) : True := by
  check_skip_norm ((trampPC pl).rebase b (fun _ => none)) (b + 0x0#64)
  trivial

/- With `proofLib.skipNormAtCallStep` off, `wp_steps` tries the `arm64_norm` fetch first, which
   fails at the branch-to-branch site, and still takes the call step. -/
/-- info: wp_steps: stopped at pc b + 12#64 (target b + 4#64): stopped at subroutine call boundary -/
#guard_msgs (substring := true, whitespace := lax) in
set_option proofLib.skipNormAtCallStep false in
set_option proofLib.wpVerbose true in
example (pl : Placement) (b : BitVec 64) (s : State) (hP : trampLib.Placeable pl)
    (hpc : s.pc = b + 0x0#64) (hrun : s.status = .Running) (Q : State → SepProp → Prop)
    (hQ : Q ((s.writeReg64 (.gpr 30#5) (b + 4#64)).setPC (b + 4#64)) emp) :
    SepWP ((trampPC pl).rebase b (fun _ => none)) (b + 4#64) s emp Q (fun _ => emp) := by
  wp_steps 1
  wp_steps 1
  wp_done

/-- error: Unknown identifier `trampPC_rebase_fetch_base` -/
#guard_msgs (substring := true) in
example := trampPC_rebase_fetch_base

/-- A trampoline whose `B` has a non-zero addend: no call-step lemma, and the `BL` is skipped. -/
def trampAddLib : PlacedLib where
  name := "trampAdd"
  text := { trampBlk with
    relocs := [{ off := 0, kind := .call26, sym := "tramp" },
               { off := 8, kind := .jump26, sym := "helper", addend := 4 }] }
  exports := ["tramp_main"]

def trampAddPC (pl : Placement) : Program := trampAddLib.program pl

theorem trampAdd_code_eq : trampAddLib.text.code = trampTree.toBytes := by rfl_kernel

/-- info: gen_placed_fetches: skipping branch-to-branch candidate at 0 → tramp -/
#guard_msgs in
gen_placed_fetches trampAddPC trampAddLib trampTree trampAdd_code_eq tramp_tree_size [0x0]

/-- error: Unknown identifier `trampAddPC_callStep_0x0` -/
#guard_msgs (substring := true) in
example := trampAddPC_callStep_0x0

/-! ## Multi-chunk unrelocated blocks (> 64 instructions) and `gen_placed_fnOffs` -/

/-- 70 `NOP`s (`0x0..0x114`), an `ADRP X1, tbl; ADD X1, X1, :lo12:tbl` pair (`0x118..0x11c`),
    and 5 `NOP`s + `RET` (`0x120..0x134`): exercises splitting > 64 unrelocated offsets into
    64-instruction chunks as well as splitting across relocation sites, within the default
    200,000-heartbeat budget. -/
def chunkedBlk : CodeBlock where
  code :=
    (List.replicate 70 (bytesOfWordLE 0xd503201f#32)).flatten ++
    bytesOfWordLE 0x90000001#32 ++ bytesOfWordLE 0x91000021#32 ++
    (List.replicate 5 (bytesOfWordLE 0xd503201f#32)).flatten ++
    bytesOfWordLE 0xd65f03c0#32
  symbols := [("chunked_entry", 0), ("chunked_tail", 0x120)]
  relocs := [{ off := 0x118, kind := .adrpHi21, sym := "tbl" },
             { off := 0x11c, kind := .addLo12, sym := "tbl" }]

def chunkedLib : PlacedLib where
  name := "chunked"
  text := chunkedBlk
  exports := ["chunked_entry", "chunked_tail"]

def chunkedPC (pl : Placement) : Program := chunkedLib.program pl

def chunkedTextProg : Program := { code := chunkedBlk.code, symbols := chunkedBlk.symbols }

def chunkedTree : WordTree := word_tree_of% chunkedTextProg

theorem chunked_code_eq : chunkedLib.text.code = chunkedTree.toBytes := by rfl_kernel

theorem chunked_tree_size : chunkedTree.checkSize? = some 78 := by rfl_kernel

def chunkedSymChars : List (List Char × Nat) := sym_chars_of% chunkedTextProg

theorem chunked_symbols_eq : chunkedLib.text.symbols = toStringSymbols chunkedSymChars := by
  rfl_kernel

theorem chunked_symbols_fresh : allFreshCharSymbols chunkedSymChars = true := by rfl_kernel

set_option maxHeartbeats 200000 in
gen_placed_fnOffs chunkedPC chunkedLib chunkedSymChars chunked_symbols_eq chunked_symbols_fresh

set_option maxHeartbeats 200000 in
gen_placed_fetches chunkedPC chunkedLib chunkedTree chunked_code_eq chunked_tree_size
  [0x0 → 0x134]

example : chunkedPC._gpf_shared_relocTree.wf = true := chunkedPC._gpf_shared_relocTree_wf
example : ProofLib.ObjectLoad.prepareCharAssocVal chunkedPC._gpf_shared_symChars =
    chunkedPC._gpf_shared_symEnc := chunkedPC._gpf_shared_symEnc_eq

-- Chunk 0 (`0x0..0xfc`), chunk 1 (`0x100..0x114`), pair (`0x118`), and chunk 2 (`0x120..0x134`):
example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) :
    ((chunkedPC pl).rebase b X).fetch b = some .nop :=
  chunkedPC_rebase_fetch_base pl b X

example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) :
    ((chunkedPC pl).rebase b X).fetch (b + 0xfc#64) = some .nop :=
  chunkedPC_rebase_fetch_0xfc pl b X

example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) :
    ((chunkedPC pl).rebase b X).fetch (b + 0x100#64) = some .nop :=
  chunkedPC_rebase_fetch_0x100 pl b X

example (pl : Placement) (b : BitVec 64) (X : String → Option (State → State)) :
    ((chunkedPC pl).rebase b X).fetch (b + 0x134#64) = some (.ret (.gpr 30#5)) :=
  chunkedPC_rebase_fetch_0x134 pl b X

example (pl : Placement) : (chunkedPC pl).fnOff "chunked_tail" = 0x120 :=
  chunkedPC_fnOff_0x120 pl

/-! ## `rd == 31` (`XZR` vs `SP`) relaxation guard -/

/-- `ADRP XZR, tbl; ADD SP, SP, :lo12:tbl; RET`: destination register 31 (`0x1f`) is `XZR` in
    `ADR`/`ADRP` but `SP` in `ADD`, so `relaxableAt 0` is `false` and `gen_placed_fetches`
    refuses to emit an unsound `pairStep` lemma at offset 0. -/
def rd31Blk : CodeBlock where
  code := bytesOfWordLE 0x9000001f#32 ++ bytesOfWordLE 0x910003ff#32 ++
    bytesOfWordLE 0xd65f03c0#32
  symbols := [("rd31_entry", 0)]
  relocs := [{ off := 0, kind := .adrpHi21, sym := "tbl" },
             { off := 4, kind := .addLo12, sym := "tbl" }]

theorem rd31_not_relaxableAt : rd31Blk.relaxableAt 0 = false := by decide

/--
error: Tactic `decide` proved that the proposition
  rd31Blk.relaxableAt 0 = true
is false
-/
#guard_msgs (error, drop info) in
example : rd31Blk.relaxableAt 0 = true := by decide

def rd31Lib : PlacedLib where
  name := "rd31"
  text := rd31Blk
  exports := ["rd31_entry"]

def rd31PC (pl : Placement) : Program := rd31Lib.program pl

def rd31TextProg : Program := { code := rd31Blk.code }

def rd31Tree : WordTree := word_tree_of% rd31TextProg

theorem rd31_code_eq : rd31Lib.text.code = rd31Tree.toBytes := by rfl_kernel

theorem rd31_tree_size : rd31Tree.checkSize? = some 3 := by rfl_kernel

gen_placed_fetches rd31PC rd31Lib rd31Tree rd31_code_eq rd31_tree_size [0x0 → 0x8]

/-- error: Unknown identifier `rd31PC_pairStep_0x0` -/
#guard_msgs (substring := true) in
example := rd31PC_pairStep_0x0

/-! ## Interval-annotated `RelocTree` and `CharSymVec` regression tests -/

section TreeHelpers
open ProofLib.GenPlacedFetches

def gadgetRelocTree : RelocTree :=
  .node 4 12
    (.leaf { off := 4, kind := .adrpHi21, sym := "tbl" })
    (.node 8 12
      (.leaf { off := 8, kind := .addLo12, sym := "tbl" })
      (.leaf { off := 12, kind := .call26, sym := "helper" }))

theorem gadgetRelocTree_wf : gadgetRelocTree.wf = true := rfl

example : gadgetBlk.relocAt? 8 = some { off := 8, kind := .addLo12, sym := "tbl" } :=
  relocAt?_of_tree rfl gadgetRelocTree_wf rfl

example : gadgetBlk.relocAt? 16 = none :=
  relocAt?_of_tree rfl gadgetRelocTree_wf rfl

example : (gadgetBlk.relocAt? 20).isNone = true :=
  relocAt?_isNone_of_tree_noRelocIn (lo := 16) (hi := 24) rfl gadgetRelocTree_wf rfl
    (by decide) (by decide)

/-- Malformed `RelocTree` whose internal span `[4, 8]` omits leaf at `12` fails `wf`. -/
def badRelocTree : RelocTree :=
  .node 4 8
    (.leaf { off := 4, kind := .adrpHi21, sym := "tbl" })
    (.leaf { off := 12, kind := .call26, sym := "helper" })

/-- error: Tactic `decide` proved that the proposition
  badRelocTree.wf = true
is false -/
#guard_msgs (error, drop info) in
example : badRelocTree.wf = true := by decide

-- Range `[8, 16]` contains relocations at `8` and `12`, so `noRelocIn` returns `false`.
/-- error: Tactic `decide` proved that the proposition
  gadgetRelocTree.noRelocIn 8 16 = true
is false -/
#guard_msgs (error, drop info) in
example : gadgetRelocTree.noRelocIn 8 16 = true := by decide

def chunkedSymVec : CharSymVec :=
  .node 1
    (.leaf "chunked_entry".toList 0)
    (.leaf "chunked_tail".toList 0x120)

theorem chunkedSymVec_size : chunkedSymVec.checkSize? = some 2 := rfl

example (pl : Placement) : (chunkedPC pl).fnOff "chunked_tail" = 0x120 :=
  placed_fnOff_of_allFresh_vec (fun _ => chunked_symbols_eq) chunked_symbols_fresh
    rfl chunkedSymVec_size 1 rfl rfl pl

/-- Mis-annotated `CharSymVec` whose `leftLen = 2` disagrees with the 1-leaf left subtree. -/
def badSymVec : CharSymVec :=
  .node 2
    (.leaf "chunked_entry".toList 0)
    (.leaf "chunked_tail".toList 0x120)

/-- error: Tactic `decide` proved that the proposition
  badSymVec.checkSize? = some 2
is false -/
#guard_msgs (error, drop info) in
example : badSymVec.checkSize? = some 2 := by decide

def gadgetSymChars : List (List Char × Nat) :=
  [("gadget".toList, 0), ("helper".toList, 20)]

def gadgetSymEnc : ProofLib.ObjectLoad.EncSymTable Nat :=
  ProofLib.ObjectLoad.prepareCharAssocVal gadgetSymChars

example : Arm64.Obj.lookup "helper" gadgetBlk.symbols = some 20 :=
  lookup_of_enc (xs := gadgetSymChars) (enc := gadgetSymEnc) rfl rfl
    (cs := "helper".toList) rfl rfl rfl

example : Arm64.Obj.lookup "missing" gadgetBlk.symbols = none :=
  lookup_of_enc (xs := gadgetSymChars) (enc := gadgetSymEnc) rfl rfl
    (cs := "missing".toList) rfl rfl rfl

def extWidgetLib : PlacedLib where
  name := "extWidget"
  text := {
    code := bytesOfWordLE 0x94000000#32 ++ bytesOfWordLE 0xd65f03c0#32
    symbols := [("entry", 0)]
    relocs := [{ off := 0, kind := .call26, sym := "ext_a" }]
    externs := ["ext_a", "ext_b"]
  }
  data := [{ sym := "tbl", align := 8, bytes := bytesOfWordLE 0x0#32 ++ bytesOfWordLE 0x0#32 }]

gen_interned_lib extWidgetI extWidgetLib 0x1000 0x4000 0x8000

def extWidgetPl : Placement :=
  extWidgetI_layout.toPlacement extWidgetI_lib.names

#guard extWidgetPl.base == 0x1000#64 && extWidgetPl.ρ "ext_a" == 0x4000#64

theorem extWidgetI_ok :
    extWidgetLib.Placeable extWidgetPl ∧
      (extWidgetLib.text.externs.map extWidgetPl.ρ).Nodup :=
  Obj.Interned.placeable_and_externs_of_checkPlaceable (ly := extWidgetI_layout)
    extWidgetI_lib_eq extWidgetI_names_eq (by decide +kernel)

example (e e' : String) (he : e ∈ extWidgetLib.text.externs) (he' : e' ∈ extWidgetLib.text.externs)
    (hoff : (extWidgetI_layout.toPlacement extWidgetI_lib.names).ρ e -
      (extWidgetI_layout.toPlacement extWidgetI_lib.names).base =
      (extWidgetI_layout.toPlacement extWidgetI_lib.names).ρ e' -
      (extWidgetI_layout.toPlacement extWidgetI_lib.names).base) :
    e = e' :=
  eq_of_externs_nodup extWidgetI_ok.2 he he' hoff

-- Placing externs inside `[base, base + code.length)` fails `checkPlaceableExt`.
gen_interned_lib badExtWidgetI extWidgetLib 0x1000 0x1000 0x8000

/-- error: Tactic `decide` proved that the proposition
  Interned.checkPlaceableExt badExtWidgetI_lib badExtWidgetI_layout badExtWidgetI_nameChars = true
is false -/
#guard_msgs (error, drop info) in
example : Obj.Interned.checkPlaceableExt badExtWidgetI_lib badExtWidgetI_layout
    badExtWidgetI_nameChars = true := by decide

end TreeHelpers

end Examples.Testing.GenPlacedFetches
