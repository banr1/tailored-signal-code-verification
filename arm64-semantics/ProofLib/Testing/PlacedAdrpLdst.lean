/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed

/-!
# Placed ADRP and Load/Store Relocation Tests

Regression tests for `ProofLib.Placed.AdrpLdst` (`PlacedLib.sepWP_rebase_adrpPlain` and
`PlacedLib.fetch_rebase_ldstLo12_of_placeable`) on a synthetic relocated library, including
negative `#guard_msgs` checks for mismatched relocation kinds and scales.
-/

@[expose] public section

namespace Examples.Testing.PlacedAdrpLdstTest

open Arm64 Arm64.Obj ProofLib

arm64_proof_prelude

-- Intentional fixture: the fetch lemmas below state the decoded instruction by hand.
set_option linter.literalFetch false

def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- Synthetic library `nop; adrp x1; ldr x0, [x1]; ldrb w2, [x1]; ret; nop` with `ADRP`, `LDR`,
    and `LDRB` relocated against `tab + 8`. -/
def Widget : PlacedLib where
  name := "widget"
  text :=
    { code := wordsLE [0xD503201F, 0x90000001, 0xF9400020, 0x39400022, 0xD65F03C0, 0xD503201F]
      symbols := [("f", 0)]
      relocs := [⟨4, .adrpHi21, "tab", 8, false⟩, ⟨8, .ldst64Lo12, "tab", 8, false⟩,
        ⟨12, .ldst8Lo12, "tab", 8, false⟩] }
  data := [{ sym := "tab", align := 8, readOnly := true, bytes := List.replicate 16 0#8 }]
  exports := ["f"]

theorem target_tab (pl : Placement) :
    Widget.text.target pl ⟨4, .adrpHi21, "tab", 8, false⟩ = pl.ρ "tab" + 8#64 := rfl

theorem fetch_ldr (pl : Placement) (hP : Widget.Placeable pl) (b : BitVec 64)
    (X O : String → Option (State → State)) :
    ((Widget.program pl).rebase b X O).fetch (b + BitVec.ofNat 64 8) =
      some (.ldr .W64 .X64 false (.gpr 0#5) (.Offset (.gpr 1#5) (lo12Of (pl.ρ "tab" + 8#64)))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (r := ⟨8, .ldst64Lo12, "tab", 8, false⟩)
    hP rfl rfl (by simp [Program.hookAtOff?, PlacedLib.program, Widget]) rfl (by decide)
    (by decide) (by decide) rfl rfl

theorem fetch_ldrb (pl : Placement) (hP : Widget.Placeable pl) (b : BitVec 64)
    (X O : String → Option (State → State)) :
    ((Widget.program pl).rebase b X O).fetch (b + BitVec.ofNat 64 12) =
      some (.ldr .W32 .B8 false (.gpr 2#5) (.Offset (.gpr 1#5) (lo12Of (pl.ρ "tab" + 8#64)))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (r := ⟨12, .ldst8Lo12, "tab", 8, false⟩)
    hP rfl rfl (by simp [Program.hookAtOff?, PlacedLib.program, Widget]) rfl (by decide)
    (by decide) (by decide) rfl rfl

theorem adrp_ldr (pl : Placement) (hP : Widget.Placeable pl) {s : State} {v : BitVec 64}
    (hpc : s.pc = pl.base + BitVec.ofNat 64 4) (hrun : s.status = .Running) :
    SepWP ((Widget.program pl).rebase pl.base) (pl.base + BitVec.ofNat 64 12) s
      ((pl.ρ "tab" + 8#64) ↦₆₄ v)
      (fun sf _ => sf.readReg64 .x0 = v ∧ sf.readReg64 .x1 = pageOf (pl.ρ "tab" + 8#64)) := by
  have hf := fetch_ldr pl hP pl.base (fun _ => none) (fun _ => none)
  refine PlacedLib.sepWP_rebase_adrpPlain (off := 4) (off4 := 8) (r := ⟨4, .adrpHi21, "tab", 8, false⟩)
    (rd := 1#5) hP rfl rfl rfl (by decide) rfl (by decide) (by decide) (by decide)
    (target_tab pl) rfl (by simp [Program.hookAtOff?, PlacedLib.program, Widget]) hpc hrun ?_
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm]

/-- info: 'Examples.Testing.PlacedAdrpLdstTest.adrp_ldr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms adrp_ldr

/-! ## Negative tests -/

-- The plain-`ADRP` rule does not apply at the `ldr` site: its relocation is `ldst64Lo12` and its
-- template is not an `ADRP`.
/--
error: Tactic `decide` proved that the proposition
  Widget.text.wordAt 8 &&& 2667577344#32 = 2415919104#32
is false
---
error: Application type mismatch: The argument
  rfl
has type
-/
#guard_msgs (substring := true) in
theorem adrp_rule_rejects_ldr_site (pl : Placement) (hP : Widget.Placeable pl) {s : State}
    (hpc : s.pc = pl.base + BitVec.ofNat 64 8) (hrun : s.status = .Running)
    (hk : ∀ s', SepWP ((Widget.program pl).rebase pl.base) (pl.base + BitVec.ofNat 64 12) s' emp
      (fun _ _ => True)) :
    SepWP ((Widget.program pl).rebase pl.base) (pl.base + BitVec.ofNat 64 12) s emp
      (fun _ _ => True) := by
  exact PlacedLib.sepWP_rebase_adrpPlain (off := 8) (off4 := 12)
    (r := ⟨8, .ldst64Lo12, "tab", 8, false⟩) (rd := 0#5) hP rfl rfl rfl (by decide) rfl
    (by decide) (by decide) (by decide) rfl rfl
    (by simp [Program.hookAtOff?, PlacedLib.program, Widget]) hpc hrun (hk _)

-- The scale-3 (`ldr x`) fetch rule does not apply at the `ldrb` site: `ldstLo12Scale` of its
-- `ldst8Lo12` relocation is `0`, and the template's size field is `0`.
/--
error: Tactic `decide` proved that the proposition
  (BitVec.extractLsb' 30 2 (Widget.text.wordAt 12)).toNat = 3
is false
---
error: Application type mismatch: The argument
  rfl
has type
-/
#guard_msgs (substring := true) in
theorem ldst64_rule_rejects_ldrb_site (pl : Placement) (hP : Widget.Placeable pl) :
    (Widget.program pl).fetch (pl.base + BitVec.ofNat 64 12) =
      some (.ldr .W64 .X64 false (.gpr 2#5) (.Offset (.gpr 1#5) (lo12Of (pl.ρ "tab" + 8#64)))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (scale := 3) (b := pl.base) (X' := fun _ => none)
    (O' := fun _ => none) (r := ⟨12, .ldst8Lo12, "tab", 8, false⟩)
    hP rfl rfl (by simp [Program.hookAtOff?, PlacedLib.program, Widget]) rfl (by decide)
    (by decide) (by decide) rfl rfl

end Examples.Testing.PlacedAdrpLdstTest
