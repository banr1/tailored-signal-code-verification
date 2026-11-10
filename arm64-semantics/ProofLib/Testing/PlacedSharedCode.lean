/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed

/-!
# Placed `SharedCode` Regression Tests

Regression tests for `RelocCodeAtWith`, `RelocCodeAt`, `placed_reloc_code_at_with%`,
`placed_reloc_code_at%`, and `placed_code_at%` across two placed libraries containing the same
relocated function at different block offsets.
-/

@[expose] public section

namespace ProofLib.Testing.PlacedSharedCode

open Arm64 Arm64.Obj

set_option autoImplicit false

def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- Template words of `f`: `adrp x1, tab; ldr x0, [x1, :lo12:tab]; bl g; ret`. -/
def fWords : List (BitVec 32) := [0x90000001#32, 0xF9400020#32, 0x94000000#32, 0xD65F03C0#32]

def fRelocs : List RelocEntry :=
  [⟨0, .adrpHi21, "tab", 0, false⟩, ⟨4, .ldst64Lo12, "tab", 0, false⟩, ⟨8, .call26, "g", 0, false⟩]

/-- Template words of `g`: `ret; nop`. -/
def gWords : List (BitVec 32) := [0xD65F03C0#32, 0xD503201F#32]

def tabData : SymDataInfo := { sym := "tab", align := 8, bytes := List.replicate 8 0#8 }

/-- `f` at block offset 0, `g` at 16. -/
def Alpha : PlacedLib where
  name := "alpha"
  text :=
    { code := wordsLE (fWords ++ gWords)
      symbols := [("f", 0), ("g", 16)]
      relocs := fRelocs }
  data := [tabData]
  exports := ["f", "g"]

/-- `g` at block offset 0, `f` at 8. -/
def Widget : PlacedLib where
  name := "widget"
  text :=
    { code := wordsLE (gWords ++ fWords)
      symbols := [("g", 0), ("f", 8)]
      relocs := fRelocs.map fun r => { r with off := r.off + 8 } }
  data := [tabData]
  exports := ["f", "g"]

/-- Generic contract over any program holding `f`'s template patched against resolver `res`. -/
theorem f_shared (prog : Program) (res : String → BitVec 64)
    (h : RelocCodeAtWith prog "f" fWords fRelocs res) :
    prog.hasWords (prog.fnAddr "f")
      [adrpWord 0x90000001#32 (prog.fnAddr "f" + BitVec.ofNat 64 0) (res "tab"),
       lo12Word 3 0xF9400020#32 (res "tab"),
       branchWord 0x94000000#32 (prog.fnAddr "f" + BitVec.ofNat 64 8) (res "g"),
       0xD65F03C0#32] :=
  h.1

/-- `Alpha` instance, every placement: `tab` resolves to `pl.ρ "tab"`, `g` to the placed `g`. -/
theorem alpha_f (pl : Placement) (hP : Alpha.Placeable pl) :
    (Alpha.program pl).hasWords ((Alpha.program pl).fnAddr "f")
      [adrpWord 0x90000001#32 ((Alpha.program pl).fnAddr "f" + BitVec.ofNat 64 0) (pl.ρ "tab"),
       lo12Word 3 0xF9400020#32 (pl.ρ "tab"),
       branchWord 0x94000000#32 ((Alpha.program pl).fnAddr "f" + BitVec.ofNat 64 8)
         ((Alpha.program pl).fnAddr "g"),
       0xD65F03C0#32] := by
  have h := f_shared (Alpha.program pl) _ (placed_reloc_code_at_with% hP)
  have htab : Alpha.text.resolve pl "tab" = pl.ρ "tab" :=
    PlacedLib.resolve_data hP (d := tabData) (by simp [Alpha])
  rwa [htab, PlacedLib.resolve_eq_fnAddr (by decide)] at h

/-- `Widget` instance of the same generic fact. -/
theorem widget_f (pl : Placement) (hP : Widget.Placeable pl) :
    (Widget.program pl).hasWords ((Widget.program pl).fnAddr "f")
      [adrpWord 0x90000001#32 ((Widget.program pl).fnAddr "f" + BitVec.ofNat 64 0) (pl.ρ "tab"),
       lo12Word 3 0xF9400020#32 (pl.ρ "tab"),
       branchWord 0x94000000#32 ((Widget.program pl).fnAddr "f" + BitVec.ofNat 64 8)
         ((Widget.program pl).fnAddr "g"),
       0xD65F03C0#32] := by
  have h := f_shared (Widget.program pl) _ (placed_reloc_code_at_with% hP)
  have htab : Widget.text.resolve pl "tab" = pl.ρ "tab" :=
    PlacedLib.resolve_data hP (d := tabData) (by simp [Widget])
  rwa [htab, PlacedLib.resolve_eq_fnAddr (by decide)] at h

/-- The relocation-free `g`, in both libraries. -/
theorem alpha_g (pl : Placement) (hP : Alpha.Placeable pl) :
    (Alpha.program pl).codeAt "g" gWords := placed_code_at% hP

theorem widget_g (pl : Placement) (hP : Widget.Placeable pl) :
    (Widget.program pl).codeAt "g" gWords := placed_code_at% hP

/-- With text-only targets (here: only the `bl g`), `RelocCodeAt.of_with` recovers `RelocCodeAt`. -/
theorem alpha_bl_only (pl : Placement)
    (h : RelocCodeAtWith (Alpha.program pl) "f" fWords [⟨8, .call26, "g", 0, false⟩]
      (Alpha.text.resolve pl)) :
    RelocCodeAt (Alpha.program pl) "f" fWords [⟨8, .call26, "g", 0, false⟩] :=
  RelocCodeAt.of_with (fun _ hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact PlacedLib.resolve_eq_fnAddr (by decide)) h

-- The text-only form rejects `f` because `tab` is not a block symbol.
#guard_msgs (drop error) in
example (pl : Placement) (hP : Alpha.Placeable pl) :
    RelocCodeAt (Alpha.program pl) "f" fWords fRelocs :=
  placed_reloc_code_at% hP

/-- The failing side condition is the text-symbol check on `tab`. -/
example : (fRelocs.all fun r => (lookup r.sym Alpha.text.symbols).isSome) = false := by decide

end ProofLib.Testing.PlacedSharedCode
