/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.ObjectLoad

/-!
# Pair-Step Hook Tests

Positive and negative tests for `ProofLib.tryPairStepHook` (`wp_step`, `wp_steps`, `wp_sym_step`,
and `wp_sym_steps`) on relaxable `ADRP`+`ADD` relocation pairs (`Obj.CodeBlock.sepWP_relaxablePair`),
including shifted-base reducible wrappers.
-/

@[expose] public section

namespace Examples.Testing.PairStepHook

open Arm64 Arm64.Obj ProofLib

set_option linter.literalFetch false

/-- `NOP; ADRP X1, tbl; ADD X1, X1, :lo12:tbl; RET`, unrelocated. -/
def widgetBlk : CodeBlock where
  code := bytesOfWordLE 0xd503201f#32 ++ bytesOfWordLE 0x90000001#32 ++
    bytesOfWordLE 0x91000021#32 ++ bytesOfWordLE 0xd65f03c0#32
  symbols := [("widget", 0)]
  relocs := [{ off := 4, kind := .adrpHi21, sym := "tbl" },
             { off := 8, kind := .addLo12, sym := "tbl" }]

def widgetLib : PlacedLib where
  name := "widget"
  text := widgetBlk
  exports := ["widget"]

/-- The library placed under `pl`, as the code constant of `(widgetPC pl).rebase b X`. -/
def widgetPC (pl : Placement) : Program := widgetLib.program pl

theorem widgetPC_rebase_fetch_base (pl : Placement) (b : BitVec 64)
    (X : String → Option (State → State)) :
    ((widgetPC pl).rebase b X).fetch b = some .nop := by
  have h := Program.fetch_of_readWordOff (prog := (widgetPC pl).rebase b X) (off := 0)
    (w := widgetBlk.wordAt 0) (by decide) rfl
    ((CodeBlock.readWordOff_patched (blk := widgetBlk) (pl := pl) rfl (by decide) (by decide)).trans
      (congrArg some (CodeBlock.patchedWord_of_relocAt_none rfl)))
  rw [show ((widgetPC pl).rebase b X).base + BitVec.ofNat 64 0 = b from BitVec.add_zero b] at h
  exact h.trans (by rfl)

theorem widgetPC_rebase_fetch_0xc (pl : Placement) (b : BitVec 64)
    (X : String → Option (State → State)) :
    ((widgetPC pl).rebase b X).fetch (b + 0xc#64) = some (.ret (.gpr 30#5)) :=
  (Program.fetch_of_readWordOff (prog := (widgetPC pl).rebase b X) (off := 12)
    (w := widgetBlk.wordAt 12) (by decide) rfl
    ((CodeBlock.readWordOff_patched (blk := widgetBlk) (pl := pl) rfl (by decide) (by decide)).trans
      (congrArg some (CodeBlock.patchedWord_of_relocAt_none rfl)))).trans (by rfl)

/-- The relaxable pair at offset 4: `X1 := pl.ρ "tbl"`, `pc := b + 12`, under either encoding. -/
theorem widgetPC_pairStep_0x4 (pl : Placement) (b : BitVec 64)
    (X : String → Option (State → State)) {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : widgetLib.Placeable pl) (hb : b = pl.base) (hpc : s.pc = b + 0x4#64)
    (hrun : s.status = .Running)
    (hnext : SepWP ((widgetPC pl).rebase b X) tgt
      ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).setPC (b + 0xc#64)) P post oom) :
    SepWP ((widgetPC pl).rebase b X) tgt s P post oom := by
  subst hb
  exact CodeBlock.sepWP_relaxablePair (blk := widgetBlk) (off := 4)
    (r := { off := 4, kind := .adrpHi21, sym := "tbl" }) hP.text rfl rfl
    (by decide) rfl (by decide) (by decide) rfl rfl hpc hrun hnext

/-! ## Positive tests -/

/-- `wp_steps 4` covers `NOP` (1), the pair (2) and `RET` (1). -/
example (pl : Placement) (s : State) (hP : widgetLib.Placeable pl)
    (hpc : s.pc = pl.base) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop)
    (hQ : Q ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).setPC (s.readReg64 (.gpr 30#5))) emp) :
    SepWP ((widgetPC pl).rebase pl.base (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_steps 4
  wp_done

/-- `wp_sym_steps` covers the same block. -/
example (pl : Placement) (s : State) (hP : widgetLib.Placeable pl)
    (hpc : s.pc = pl.base) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop)
    (hQ : Q ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).setPC (s.readReg64 (.gpr 30#5))) emp) :
    SepWP ((widgetPC pl).rebase pl.base (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_sym_steps 4
  wp_done

/-- A single `wp_step` at the pair steps both words. -/
example (pl : Placement) (s : State) (hP : widgetLib.Placeable pl)
    (hpc : s.pc = pl.base + 0x4#64) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop)
    (hQ : Q ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).setPC (s.readReg64 (.gpr 30#5))) emp) :
    SepWP ((widgetPC pl).rebase pl.base (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_step
  wp_step
  wp_done

/-- A bundled `Placeable pl ∧ b = pl.base` hypothesis (here through a reducible abbreviation)
    discharges both side conditions through its `∧` components, at a symbolic base `b`. -/
abbrev WidgetAt (pl : Placement) (b : BitVec 64) : Prop := widgetLib.Placeable pl ∧ b = pl.base

example (pl : Placement) (b : BitVec 64) (s : State) (hat : WidgetAt pl b)
    (hpc : s.pc = b + 0x4#64) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop)
    (hQ : Q ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).setPC (s.readReg64 (.gpr 30#5))) emp) :
    SepWP ((widgetPC pl).rebase b (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_step
  wp_step
  wp_done

/-! ## Negative tests -/

/-- could not discharge hypothesis
  widgetLib.Placeable pl
hint: add it to the local context (tried the state spine, `assumption`, and `rfl`) -/
#guard_msgs (substring := true) in
/-- Without `Placeable`, the hook fails loudly, naming the hypothesis. -/
example (pl : Placement) (s : State)
    (hpc : s.pc = pl.base + 0x4#64) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop) :
    SepWP ((widgetPC pl).rebase pl.base (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_step

/-- error: wp_step: could not fetch/decode instruction at PC `pl.base + 8#64` -/
#guard_msgs (substring := true) in
/-- At offset 8 (second word of the pair) there is neither a fetch lemma nor a pair lemma. -/
example (pl : Placement) (s : State) (hP : widgetLib.Placeable pl)
    (hpc : s.pc = pl.base + 0x8#64) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop) :
    SepWP ((widgetPC pl).rebase pl.base (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_step

/-! ## Shifted-base reducible wrapper tests (`b + bOff#64`) -/

/-- Reducible wrapper rebasing `widgetPC pl` at `b + 0x100#64`. -/
abbrev widgetShifted (pl : Placement) (b : BitVec 64)
    (X : String → Option (State → State)) : Program :=
  (widgetPC pl).rebase (b + 0x100#64) X

/-- `wp_steps 4` over `widgetShifted` steps `NOP` (`b + 0x100`), the relaxable pair (`b + 0x104`),
    and `RET` (`b + 0x10c`), reassociating `(b + 0x100#64) + 0x4#64` automatically. -/
example (pl : Placement) (b : BitVec 64) (s : State)
    (hat : WidgetAt pl (b + 0x100#64))
    (hpc : s.pc = b + 0x100#64) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop)
    (hQ : Q ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).setPC (s.readReg64 (.gpr 30#5))) emp) :
    SepWP (widgetShifted pl b (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_steps 4
  wp_done

/-- `wp_sym_steps 4` over `widgetShifted` covers the same shifted-base block. -/
example (pl : Placement) (b : BitVec 64) (s : State)
    (hat : WidgetAt pl (b + 0x100#64))
    (hpc : s.pc = b + 0x100#64) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop)
    (hQ : Q ((s.writeReg64 (.gpr 1#5) (pl.ρ "tbl")).setPC (s.readReg64 (.gpr 30#5))) emp) :
    SepWP (widgetShifted pl b (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_sym_steps 4
  wp_done

/-- could not discharge hypothesis
  b + 256#64 = pl.base -/
#guard_msgs (substring := true) in
/-- Negative: missing shifted-base equality `b + 0x100#64 = pl.base` fails loudly. -/
example (pl : Placement) (b : BitVec 64) (s : State) (hP : widgetLib.Placeable pl)
    (hpc : s.pc = b + 0x104#64) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop) :
    SepWP (widgetShifted pl b (fun _ => none)) (s.readReg64 (.gpr 30#5)) s emp Q
      (fun _ => emp) := by
  wp_step

end Examples.Testing.PairStepHook
