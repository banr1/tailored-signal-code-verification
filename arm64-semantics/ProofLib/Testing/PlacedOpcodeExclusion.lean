/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.OpcodeExclusion

/-!
# Placed Opcode-Exclusion Tests

Positive and negative `#guard_msgs` tests for `CodeBlock.patchSafe` and
`PlacedLib.program_noSvc0_of_patchSafe` / `program_noMsrTpidrEl0_of_patchSafe` across ordinary,
relaxable GOT/TLSIE, and rejected relocation patterns.
-/

@[expose] public section

namespace ProofLib.Testing.PlacedOpcodeExclusion

open Arm64 Arm64.Obj

def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

def widgetRelocs : List RelocEntry :=
  [⟨0, .call26, "ext", 0, false⟩, ⟨4, .adrpHi21, "buf", 0, false⟩, ⟨8, .addLo12, "buf", 0, false⟩,
    ⟨12, .adrpHi21, "tab", 0, false⟩, ⟨16, .ldst64Lo12, "tab", 0, false⟩]

def Widget : CodeBlock where
  code := wordsLE [0x94000000, 0x90000000, 0x91000000, 0x90000001, 0xF9400021, 0xD53BD042,
    0xD65F03C0, 0xD503201F]
  symbols := [("f", 0)]
  relocs := widgetRelocs
  externs := ["ext"]

def WidgetLib : PlacedLib := { name := "widget", text := Widget }

theorem widget_svc : Widget.patchSafe svc0Pat = true := by decide +kernel

theorem widget_msr : Widget.patchSafe msrTpidrEl0Pat = true := by decide +kernel

example : ∀ pl, WidgetLib.Placeable pl →
    (WidgetLib.program pl).allInstrs (fun i => !i.isSvc0) = true := fun pl _ =>
  PlacedLib.program_noSvc0_of_patchSafe widget_svc pl

example : ∀ pl, WidgetLib.Placeable pl →
    (WidgetLib.program pl).allInstrs (fun i => !i.isMsrTpidrEl0) = true := fun pl _ =>
  PlacedLib.program_noMsrTpidrEl0_of_patchSafe widget_msr pl

example : svc0Pat.matches 0xd4000001#32 = true := by decide
example : svc0Pat.matches 0xd4000021#32 = false := by decide
example : msrTpidrEl0Pat.matches 0xd51bd042#32 = true := by decide
example : msrTpidrEl0Pat.matches 0xd53bd042#32 = false := by decide

/-- A GOT pair and an initial-exec TLS pair (relaxable to `NOP`/`ADR`, `ADRP`/`ADD` and
    `MOVZ`/`MOVK`). -/
def GotBlock : CodeBlock where
  code := wordsLE [0x90000000, 0xF9400000, 0x90000001, 0xF9400021, 0xD65F03C0]
  relocs := [⟨0, .adrGotPage, "g", 0, false⟩, ⟨4, .ld64GotLo12Nc, "g", 0, false⟩,
    ⟨8, .tlsieAdrGottprelPage21, "t", 0, false⟩, ⟨12, .tlsieLd64GottprelLo12Nc, "t", 0, false⟩]

example : GotBlock.patchSafe svc0Pat = true := by decide +kernel
example : GotBlock.patchSafe msrTpidrEl0Pat = true := by decide +kernel

/-! ## Negative Tests -/

/-- `Widget` with an unrelocated `svc #0` in place of the `nop`. -/
def WidgetSvc : CodeBlock := { Widget with
  code := wordsLE [0x94000000, 0x90000000, 0x91000000, 0x90000001, 0xF9400021, 0xD53BD042,
    0xD65F03C0, 0xD4000001] }

/--
error: Tactic `decide` proved that the proposition
  CodeBlock.patchSafe svc0Pat WidgetSvc = true
is false
-/
#guard_msgs (error, drop info) in
example : WidgetSvc.patchSafe svc0Pat = true := by decide +kernel

/-- `Widget` with an unrelocated `msr tpidr_el0, x2` in place of the `mrs`. -/
def WidgetMsr : CodeBlock := { Widget with
  code := wordsLE [0x94000000, 0x90000000, 0x91000000, 0x90000001, 0xF9400021, 0xD51BD042,
    0xD65F03C0, 0xD503201F] }

/--
error: Tactic `decide` proved that the proposition
  CodeBlock.patchSafe msrTpidrEl0Pat WidgetMsr = true
is false
-/
#guard_msgs (error, drop info) in
example : WidgetMsr.patchSafe msrTpidrEl0Pat = true := by decide +kernel

/-- `Widget` with a `prel32` relocation on its last word. -/
def WidgetPrel : CodeBlock := { Widget with
  relocs := widgetRelocs ++ [⟨28, .prel32, "tab", 0, false⟩] }

/--
error: Tactic `decide` proved that the proposition
  CodeBlock.patchSafe svc0Pat WidgetPrel = true
is false
-/
#guard_msgs (error, drop info) in
example : WidgetPrel.patchSafe svc0Pat = true := by decide +kernel

/-- A `jump26` relocation on a template word whose top six bits are those of `svc`. -/
def WidgetBadBranch : CodeBlock := { Widget with
  relocs := widgetRelocs ++ [⟨24, .jump26, "f", 0, false⟩] }

/--
error: Tactic `decide` proved that the proposition
  CodeBlock.patchSafe svc0Pat WidgetBadBranch = true
is false
-/
#guard_msgs (error, drop info) in
example : WidgetBadBranch.patchSafe svc0Pat = true := by decide +kernel

/-- `Widget` with its relocations out of order. -/
def WidgetUnsorted : CodeBlock := { Widget with relocs := widgetRelocs.reverse }

/--
error: Tactic `decide` proved that the proposition
  CodeBlock.patchSafe svc0Pat WidgetUnsorted = true
is false
-/
#guard_msgs (error, drop info) in
example : WidgetUnsorted.patchSafe svc0Pat = true := by decide +kernel

end ProofLib.Testing.PlacedOpcodeExclusion
