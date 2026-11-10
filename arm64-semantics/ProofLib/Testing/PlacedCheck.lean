/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed

/-!
# `ProofLib.Placed` Check and Transfer Tests

Regression tests for `Interned.check`, `Interned.checkDisjoint`, `Interned.checkPlaceable`,
`Interned.checkPlaceableExt`, split-check helpers, `CodeBlock.relaxedAtFast`, GOT and TLS
relaxation checking, and `ElfImage` transfer lemmas (`codeLoaded_of_inElf`,
`satisfies_dataInit_of_inElf`, `externAt?_program`).
-/

@[expose] public section

namespace Examples.Testing.PlacedCheckTest

open Arm64 Arm64.Obj Arm64.Obj.Interned Arm64.Process ProofLib ProofLib.ObjectLoad
  ProofLib.ProgramReflection

def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- Names table (strictly increasing): `buf` = 0, `ext` = 1, `f` = 2, `tab` = 3. -/
def nameChars : List (List Char) := [['b', 'u', 'f'], ['e', 'x', 't'], ['f'], ['t', 'a', 'b']]

def Widget : Lib where
  name := "widget"
  names := nameChars.map String.ofList
  code := wordsLE [0x94000000, 0x90000000, 0x91000000, 0x90000001, 0xF9400021, 0x94000000,
    0xD65F03C0, 0xD503201F]
  symbols := [(2, 0)]
  relocs := [⟨0, .call26, 1, 0, false⟩, ⟨4, .adrpHi21, 0, 0, false⟩, ⟨8, .addLo12, 0, 0, false⟩,
    ⟨12, .adrpHi21, 3, 0, false⟩, ⟨16, .ldst64Lo12, 3, 0, false⟩, ⟨20, .call26, 2, 0, false⟩]
  externs := [1]
  data := [{ sym := 3, align := 8, readOnly := true, bytes := List.replicate 8 0#8,
             relocs := [⟨0, .abs64, 2, 0, false⟩] },
           { sym := 0, align := 8, readOnly := false, zeroTail := 8 }]
  exports := [2]

/-- Layout keeping every `adrp; add` pair. -/
def ly0 : Layout := { base := 0x400000#64, addrs := [0x410000#64, 0x500000#64, 0#64, 0x401000#64] }

/-- Layout relaxing the `adrp; add` pair at offset 4 to `nop; adr`. -/
def ly1 : Layout := { ly0 with relax := [4] }

/-! ## Hand-Built Images -/

def code0 : List (BitVec 8) := wordsLE [0x94040000, 0x90000080, 0x91000000, 0xB0000001,
  0xF9400021, 0x97FFFFFB, 0xD65F03C0, 0xD503201F]

def code1 : List (BitVec 8) := wordsLE [0x94040000, 0xD503201F, 0x1007FFC0, 0xB0000001,
  0xF9400021, 0x97FFFFFB, 0xD65F03C0, 0xD503201F]

def symChars : List (List Char × BitVec 64) := [(['f'], 0x400000#64)]

def mkImg (code : List (BitVec 8)) (tabPerm bufPerm : Perm := Perm.ro) : ElfImage where
  entry := 0x400000#64
  phdrVaddr := 0x400040#64
  phnum := 3
  segments := [{ start := 0x400000#64, perm := Perm.rx, bytes := code },
    { start := 0x401000#64, perm := tabPerm, bytes := [0#8, 0#8, 0x40#8, 0#8, 0#8, 0#8, 0#8, 0#8] },
    { start := 0x410000#64, perm := bufPerm, bytes := List.replicate 8 0#8 }]
  brkStart := 0x420000#64
  symbols := toStringAssoc symChars

def img0 : ElfImage := mkImg code0 Perm.ro Perm.rw
def img1 : ElfImage := mkImg code1 Perm.ro Perm.rw

/-! ## `check` and Transfer Lemmas -/

theorem widget_names_nodup : Widget.names.Nodup := nodup_of_namesNodup rfl (by decide)
theorem widget_idsOk : Widget.IdsOk := Lib.idsOk_spec (by decide)

theorem check0 : Widget.toLib.Placeable (ly0.toPlacement Widget.names) ∧
    Widget.toLib.InElf img0 (ly0.toPlacement Widget.names) :=
  check_spec (symChars := symChars) rfl rfl (by decide +kernel)

theorem check1 : Widget.toLib.Placeable (ly1.toPlacement Widget.names) ∧
    Widget.toLib.InElf img1 (ly1.toPlacement Widget.names) :=
  check_spec (symChars := symChars) rfl rfl (by decide +kernel)

example {inputs : ProcessInputs} {s : State} (hload : img0.loadState inputs = .ok s)
    (X O : String → Option (State → State)) :
    (Widget.toLib.program (ly0.toPlacement Widget.names) X O).CodeLoaded s.mem :=
  PlacedLib.codeLoaded_of_inElf check0.1 check0.2 hload

example {inputs : ProcessInputs} {s : State} (hload : img1.loadState inputs = .ok s) :
    s.mem ⊨ Widget.toLib.dataInit (ly1.toPlacement Widget.names) :=
  PlacedLib.satisfies_dataInit_of_inElf check1.1 check1.2 hload
    (Interned.dataDisjoint_of_dataSorted rfl rfl widget_names_nodup widget_idsOk check1.1
      (by decide))

theorem checkDisjoint0 : Widget.toLib.Placeable (ly0.toPlacement Widget.names) ∧
    Widget.toLib.InElf img0 (ly0.toPlacement Widget.names) ∧
    Widget.toLib.DataDisjoint (ly0.toPlacement Widget.names) :=
  checkDisjoint_spec (symChars := symChars) rfl rfl (by decide +kernel)

example {inputs : ProcessInputs} {s : State} (hload : img0.loadState inputs = .ok s) :
    s.mem ⊨ Widget.toLib.dataInit (ly0.toPlacement Widget.names) :=
  PlacedLib.satisfies_dataInit_of_inElf checkDisjoint0.1 checkDisjoint0.2.1 hload
    checkDisjoint0.2.2

example (X O : String → Option (State → State)) (svc : State → State) :
    let pl := ly0.toPlacement Widget.names
    (Widget.toLib.program pl X O svc).externAt? (pl.ρ "ext") = (X "ext").or
      ((Widget.toLib.program pl X O svc).symbols.findSome? fun (n, o) =>
        if o == (pl.ρ "ext" - pl.base).toNat then O n else none) :=
  PlacedLib.externAt?_program
    (Interned.externsNodup_of_check rfl rfl widget_names_nodup widget_idsOk (by decide))
    (by decide)

/-! ## Rejection Checks -/

/-- `buf` placed at `0x401004`, overlapping `tab`'s 8 bytes at `0x401000`. -/
def lyOverlap : Layout :=
  { ly0 with addrs := [0x401004#64, 0x500000#64, 0#64, 0x401000#64] }

/--
error: Tactic `decide` proved that the proposition
  check Widget ly0 nameChars (mkImg (code0.set 1 1#8) Perm.ro Perm.rw) (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check Widget ly0 nameChars (mkImg (code0.set 1 1#8) Perm.ro Perm.rw)
    (prepareCharAssocVal symChars) = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  check Widget ly1 nameChars img0 (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check Widget ly1 nameChars img0 (prepareCharAssocVal symChars) = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  check Widget ly0 nameChars (mkImg code0) (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check Widget ly0 nameChars (mkImg code0 Perm.ro Perm.ro)
    (prepareCharAssocVal symChars) = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  dataSorted Widget lyOverlap = true
is false
-/
#guard_msgs (error, drop info) in
example : Interned.dataSorted Widget lyOverlap = true := by decide

/--
error: Tactic `decide` proved that the proposition
  checkDisjoint Widget lyOverlap nameChars img0 (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : checkDisjoint Widget lyOverlap nameChars img0 (prepareCharAssocVal symChars) = true := by
  decide +kernel

/-! ## GOT (`ADR_GOT_PAGE` + `LD64_GOT_LO12_NC`), TLSIE, and Register-31 Relaxation Tests -/

/-- Block testing register-31 (`0x1f`) exclusion in `relaxableAt` and `gotPairAt` (where `31` is
    `XZR` in `ADRP`/`ADR` but `SP` in `ADD` and `Rn` of `LDR`) and inclusion in
    `tlsieRelaxableAt` (where `31` is `XZR` in `ADRP`, `LDR`, `MOVZ`, and `MOVK`). -/
def reg31Block : CodeBlock where
  code := wordsLE [
    0x9000001F, 0x910003FF, -- 0x00: adrp xzr, 0; add sp, sp, #0 (not relaxable)
    0x9000001F, 0xF94003FF, -- 0x08: adrp xzr, 0; ldr xzr, [sp, #0] (not gotPairAt)
    0x9000001F, 0xF94003FF, -- 0x10: adrp xzr, 0; ldr xzr, [sp, #0] (tlsieRelaxableAt = true)
    0x90000000, 0xF9400000, -- 0x18: adrp x0, 0;  ldr x0, [x0, #0]  (gotPairAt = true)
    0x90000000, 0xF9400020  -- 0x20: adrp x0, 0;  ldr x0, [x1, #0]  (Rn != Rd: tlsieRelaxableAt 0x24 = false)
  ]
  align := 4
  symbols := [("f", 0)]
  relocs := [
    ⟨0x00, .adrpHi21, "d", 0, false⟩, ⟨0x04, .addLo12, "d", 0, false⟩,
    ⟨0x08, .adrGotPage, "g", 0, false⟩, ⟨0x0C, .ld64GotLo12Nc, "g", 0, false⟩,
    ⟨0x10, .tlsieAdrGottprelPage21, "t", 0, false⟩,
    ⟨0x14, .tlsieLd64GottprelLo12Nc, "t", 0, false⟩,
    ⟨0x18, .adrGotPage, "g", 0, false⟩, ⟨0x1C, .ld64GotLo12Nc, "g", 0, false⟩,
    ⟨0x20, .tlsieAdrGottprelPage21, "t", 0, false⟩,
    ⟨0x24, .tlsieLd64GottprelLo12Nc, "t", 0, false⟩
  ]
  externs := []

example : reg31Block.relaxableAt 0x00 = false := by decide +kernel
example : reg31Block.gotPairAt 0x08 = false := by decide +kernel
example : reg31Block.tlsieRelaxableAt 0x10 = true := by decide +kernel
example : reg31Block.tlsieRelaxableAt 0x14 = true := by decide +kernel
example : reg31Block.gotPairAt 0x18 = true := by decide +kernel
example : reg31Block.tlsieRelaxableAt 0x20 = true := by decide +kernel
example : reg31Block.tlsieRelaxableAt 0x24 = false := by decide +kernel

/-- Names table for `GotTlsWidget`: `ext_a` = 0, `ext_b` = 1, `f` = 2, `tls_v` = 3. -/
def gotTlsNameChars : List (List Char) :=
  [['e', 'x', 't', '_', 'a'], ['e', 'x', 't', '_', 'b'], ['f'], ['t', 'l', 's', '_', 'v']]

/-- Synthetic library with two GOT load pairs and one initial-exec TLS (`TLSIE`) pair. -/
def GotTlsWidget : Lib where
  name := "got_tls_widget"
  names := gotTlsNameChars.map String.ofList
  code := wordsLE [
    0x90000000, 0xF9400000, -- 0x00: adrp x0, :got:ext_a; ldr x0, [x0, :got_lo12:ext_a]
    0x90000001, 0xF9400021, -- 0x08: adrp x1, :got:ext_b; ldr x1, [x1, :got_lo12:ext_b]
    0x90000002, 0xF9400042, -- 0x10: adrp x2, :gottprel:tls_v; ldr x2, [x2, :gottprel_lo12:tls_v]
    0xD65F03C0              -- 0x18: ret
  ]
  symbols := [(2, 0)]
  relocs := [
    ⟨0x00, .adrGotPage, 0, 0, false⟩, ⟨0x04, .ld64GotLo12Nc, 0, 0, false⟩,
    ⟨0x08, .adrGotPage, 1, 0, false⟩, ⟨0x0C, .ld64GotLo12Nc, 1, 0, false⟩,
    ⟨0x10, .tlsieAdrGottprelPage21, 3, 0, false⟩,
    ⟨0x14, .tlsieLd64GottprelLo12Nc, 3, 0, false⟩
  ]
  externs := [0, 1]
  data := []
  exports := [2]

/-- Relaxed layout: `ext_a` at `0x410008` (`GotToNopAdr`), `ext_b` at `0x600020` (`GotToAdrpAdd`),
    and `tls_v` at thread-pointer offset `0x10010` (`TLSIE` -> `TLSLE` `MOVZ` + `MOVK`). -/
def lyGotTlsRelax : Layout :=
  { base := 0x400000#64
    addrs := [0x410008#64, 0x600020#64, 0#64, 0x10010#64]
    relax := [0x00, 0x0C, 0x10, 0x14] }

/-- Unrelaxed (`--no-relax`) layout: 8-byte aligned GOT slots at `0x420000..0x420010`. -/
def lyGotTlsUnrelax : Layout :=
  { base := 0x400000#64
    addrs := [0x420000#64, 0x420008#64, 0#64, 0x420010#64]
    relax := [] }

def codeGotTlsRelax : List (BitVec 8) := wordsLE [
  0xD503201F, 0x10080020, -- nop; adr x0, 0x410008
  0x90001001, 0x91008021, -- adrp x1, 0x600000; add x1, x1, #0x20
  0xD2A00022, 0xF2800202, -- movz x2, #1, lsl #16; movk x2, #0x10
  0xD65F03C0
]

def codeGotTlsUnrelax : List (BitVec 8) := wordsLE [
  0x90000100, 0xF9400000, -- adrp x0, 0x420000; ldr x0, [x0, #0]
  0x90000101, 0xF9400421, -- adrp x1, 0x420000; ldr x1, [x1, #8]
  0x90000102, 0xF9400842, -- adrp x2, 0x420000; ldr x2, [x2, #16]
  0xD65F03C0
]

def imgGotTlsRelax : ElfImage := mkImg codeGotTlsRelax
def imgGotTlsUnrelax : ElfImage := mkImg codeGotTlsUnrelax

theorem checkGotTlsRelax :
    GotTlsWidget.toLib.Placeable (lyGotTlsRelax.toPlacement GotTlsWidget.names) ∧
    GotTlsWidget.toLib.InElf imgGotTlsRelax (lyGotTlsRelax.toPlacement GotTlsWidget.names) :=
  check_spec (symChars := symChars) rfl rfl (by decide +kernel)

theorem checkGotTlsUnrelax :
    GotTlsWidget.toLib.Placeable (lyGotTlsUnrelax.toPlacement GotTlsWidget.names) ∧
    GotTlsWidget.toLib.InElf imgGotTlsUnrelax (lyGotTlsUnrelax.toPlacement GotTlsWidget.names) :=
  check_spec (symChars := symChars) rfl rfl (by decide +kernel)

/--
error: Tactic `decide` proved that the proposition
  check GotTlsWidget lyGotTlsRelax gotTlsNameChars imgGotTlsUnrelax (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check GotTlsWidget lyGotTlsRelax gotTlsNameChars imgGotTlsUnrelax
    (prepareCharAssocVal symChars) = true := by decide +kernel

/-- Layout with an out-of-range TP offset (`>= 2^32`, with identical low 32 bits `0x10010`)
    in relaxed TLSIE mode. -/
def lyGotTlsBadTp : Layout :=
  { lyGotTlsRelax with addrs := [0x410008#64, 0x600020#64, 0#64, 0x100010010#64] }

/--
error: Tactic `decide` proved that the proposition
  check GotTlsWidget lyGotTlsBadTp gotTlsNameChars imgGotTlsRelax (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check GotTlsWidget lyGotTlsBadTp gotTlsNameChars imgGotTlsRelax
    (prepareCharAssocVal symChars) = true := by decide +kernel

/-- Layout with an out-of-range GOT `NOP + ADR` target (`0x610008`, `> 1 MiB` from `0x400004` but
    with identical low 21 bits `0x10004`, so `adrWord` truncates to the exact bytes in
    `imgGotTlsRelax`). Rejected by `AdrInRange` in `relocInRange`. -/
def lyGotTlsBadAdr : Layout :=
  { lyGotTlsRelax with addrs := [0x610008#64, 0x600020#64, 0#64, 0x10010#64] }

/--
error: Tactic `decide` proved that the proposition
  check GotTlsWidget lyGotTlsBadAdr gotTlsNameChars imgGotTlsRelax (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check GotTlsWidget lyGotTlsBadAdr gotTlsNameChars imgGotTlsRelax
    (prepareCharAssocVal symChars) = true := by decide +kernel

/-- Layout with a 4-byte-aligned (not 8-byte-aligned) unrelaxed GOT slot (`0x420004`, where
    `lo12Word 3` truncates bit 2 to produce the exact bytes in `imgGotTlsUnrelax`). Rejected by
    `Lo12Aligned 3` in `relocInRange`. -/
def lyGotTlsMisalignedSlot : Layout :=
  { lyGotTlsUnrelax with addrs := [0x420004#64, 0x420008#64, 0#64, 0x420010#64] }

/--
error: Tactic `decide` proved that the proposition
  check GotTlsWidget lyGotTlsMisalignedSlot gotTlsNameChars imgGotTlsUnrelax (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check GotTlsWidget lyGotTlsMisalignedSlot gotTlsNameChars imgGotTlsUnrelax
    (prepareCharAssocVal symChars) = true := by decide +kernel

/-- Synthetic library with a 4-instruction `TLSDESC` sequence (`tlsdescAdrPage21`, `tlsdescLd64Lo12`,
    `tlsdescAddLo12`, `tlsdescCall`) and direct `TLSLE` (`tlsleAddTprelHi12`,
    `tlsleLdst64TprelLo12Nc`, `tlsleMovwTprelG0`) relocations. -/
def TlsDescLeWidget : Lib where
  name := "tlsdesc_le_widget"
  names := gotTlsNameChars.map String.ofList
  code := wordsLE [
    0x90000000, 0xF9400000, -- 0x00: adrp x0, :tlsdesc:tls_v; ldr x0, [x0, :tlsdesc_lo12:tls_v]
    0x91000000, 0xD63F0000, -- 0x08: add x0, x0, :tlsdesc_lo12:tls_v; blr x0 (:tlsdesccall:tls_v)
    0x91400021, 0xF9400021, -- 0x10: add x1, x1, #:tprel_hi12:tls_v, lsl #12; ldr x1, [x1, #:tprel_lo12_nc:tls_v]
    0xD2800002,             -- 0x18: movz x2, #:tprel_g0:ext_a
    0xD65F03C0              -- 0x1C: ret
  ]
  symbols := [(2, 0)]
  relocs := [
    ⟨0x00, .tlsdescAdrPage21, 3, 0, false⟩,
    ⟨0x04, .tlsdescLd64Lo12, 3, 0, false⟩,
    ⟨0x08, .tlsdescAddLo12, 3, 0, false⟩,
    ⟨0x0C, .tlsdescCall, 3, 0, false⟩,
    ⟨0x10, .tlsleAddTprelHi12, 3, 0, false⟩,
    ⟨0x14, .tlsleLdst64TprelLo12Nc, 3, 0, false⟩,
    ⟨0x18, .tlsleMovwTprelG0, 0, 0, false⟩
  ]
  externs := []
  data := []
  exports := [2]

/-- Valid layout: `ext_a` at TP offset `0x20`, `tls_v` at 8-byte aligned TP offset `0x12010`. -/
def lyTlsDescLe : Layout :=
  { base := 0x400000#64
    addrs := [0x20#64, 0#64, 0#64, 0x12010#64]
    relax := [] }

def codeTlsDescLe : List (BitVec 8) := wordsLE [
  0xD2A00020, 0xF2840200, -- movz x0, #1, lsl #16; movk x0, #0x2010
  0xD503201F, 0xD503201F, -- nop; nop
  0x91404821, 0xF9400821, -- add x1, x1, #0x12, lsl #12; ldr x1, [x1, #0x10]
  0xD2800402,             -- movz x2, #0x20
  0xD65F03C0
]

def imgTlsDescLe : ElfImage := mkImg codeTlsDescLe

theorem checkTlsDescLe :
    TlsDescLeWidget.toLib.Placeable (lyTlsDescLe.toPlacement TlsDescLeWidget.names) ∧
    TlsDescLeWidget.toLib.InElf imgTlsDescLe (lyTlsDescLe.toPlacement TlsDescLeWidget.names) :=
  check_spec (symChars := symChars) rfl rfl (by decide +kernel)

/-- Layout with TP offset `>= 2^24` (`0x1012010`, identical low 24 bits) rejected by `TprelHi12InRange`. -/
def lyTlsDescLeBadHi12 : Layout :=
  { lyTlsDescLe with addrs := [0x20#64, 0#64, 0#64, 0x1012010#64] }

/--
error: Tactic `decide` proved that the proposition
  check TlsDescLeWidget lyTlsDescLeBadHi12 gotTlsNameChars imgTlsDescLe (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check TlsDescLeWidget lyTlsDescLeBadHi12 gotTlsNameChars imgTlsDescLe
    (prepareCharAssocVal symChars) = true := by decide +kernel

/-- Layout with 4-byte-aligned (not 8-byte-aligned) TP offset `0x12014` rejected by `Lo12Aligned 3`
    on `tlsleLdst64TprelLo12Nc`. -/
def lyTlsDescLeMisaligned : Layout :=
  { lyTlsDescLe with addrs := [0x20#64, 0#64, 0#64, 0x12014#64] }

/--
error: Tactic `decide` proved that the proposition
  check TlsDescLeWidget lyTlsDescLeMisaligned gotTlsNameChars imgTlsDescLe (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check TlsDescLeWidget lyTlsDescLeMisaligned gotTlsNameChars imgTlsDescLe
    (prepareCharAssocVal symChars) = true := by decide +kernel

/-- Layout with `tlsleMovwTprelG0` target `>= 2^16` (`0x10020`, identical low 16 bits) rejected by
    `TprelG0InRange`. -/
def lyTlsDescLeBadG0 : Layout :=
  { lyTlsDescLe with addrs := [0x10020#64, 0#64, 0#64, 0x12010#64] }

/--
error: Tactic `decide` proved that the proposition
  check TlsDescLeWidget lyTlsDescLeBadG0 gotTlsNameChars imgTlsDescLe (prepareCharAssocVal symChars) = true
is false
-/
#guard_msgs (error, drop info) in
example : check TlsDescLeWidget lyTlsDescLeBadG0 gotTlsNameChars imgTlsDescLe
    (prepareCharAssocVal symChars) = true := by decide +kernel

/-! ## ELF-Free `checkPlaceable` and `checkPlaceableExt` Tests -/

theorem widget_placeable0 : Widget.toLib.Placeable (ly0.toPlacement Widget.names) :=
  placeable_of_checkPlaceable rfl rfl (by decide +kernel)

theorem widget_exists_placeable : ∃ pl, Widget.toLib.Placeable pl :=
  exists_placeable_of_checkPlaceable (ly := ly0) rfl rfl (by decide +kernel)

theorem gotTls_placeable_and_externs :
    GotTlsWidget.toLib.Placeable (lyGotTlsUnrelax.toPlacement GotTlsWidget.names) ∧
      (GotTlsWidget.toLib.text.externs.map (lyGotTlsUnrelax.toPlacement GotTlsWidget.names).ρ).Nodup :=
  placeable_and_externs_of_checkPlaceable rfl rfl (by decide +kernel)

theorem gotTls_exists_placeable_and_externs :
    ∃ pl, GotTlsWidget.toLib.Placeable pl ∧ (GotTlsWidget.toLib.text.externs.map pl.ρ).Nodup :=
  exists_placeable_and_externs_of_checkPlaceable (ly := lyGotTlsUnrelax) rfl rfl (by decide +kernel)

example :
    let pl := lyGotTlsUnrelax.toPlacement GotTlsWidget.names
    (GotTlsWidget.toLib.text.externs.map fun e => (pl.ρ e - pl.base).toNat).Nodup :=
  externsOffsetNodup_of_externsNodup gotTls_placeable_and_externs.2

/-- Layout aliasing `ext_a` and `ext_b` at the same address `0x420000`. -/
def lyGotTlsAliasedExterns : Layout :=
  { lyGotTlsUnrelax with addrs := [0x420000#64, 0x420000#64, 0#64, 0x420010#64] }

/-- `checkPlaceable` alone succeeds when two externs alias, but `checkPlaceableExt` rejects it. -/
example : checkPlaceable GotTlsWidget lyGotTlsAliasedExterns gotTlsNameChars = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  checkPlaceableExt GotTlsWidget lyGotTlsAliasedExterns gotTlsNameChars = true
is false
-/
#guard_msgs (error, drop info) in
example : checkPlaceableExt GotTlsWidget lyGotTlsAliasedExterns gotTlsNameChars = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  checkPlaceable GotTlsWidget lyGotTlsBadAdr gotTlsNameChars = true
is false
-/
#guard_msgs (error, drop info) in
example : checkPlaceable GotTlsWidget lyGotTlsBadAdr gotTlsNameChars = true := by
  decide +kernel

/-- Synthetic 500-symbol `PlacedLib` (`1` export, `39` externs, `460` data objects, `1,000`
    relocations) exercising `checkPlaceableExt` by `decide +kernel`. -/
def scaleDigits : List Char := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

def scaleDigits5 : List Char := ['0', '1', '2', '3', '4']

def scaleNameChars : List (List Char) :=
  scaleDigits5.flatMap fun a =>
    scaleDigits.flatMap fun b =>
      scaleDigits.map fun c => ['s', a, b, c]

def mkScaleRelocs : Nat → Nat → List Reloc
  | 0, _ => []
  | k + 1, off =>
    ⟨off, .adrpHi21, 40 + k, 0, false⟩ ::
      ⟨off + 4, .addLo12, 40 + k, 0, false⟩ ::
      mkScaleRelocs k (off + 8)

def mkScaleData : Nat → Nat → List Data
  | 0, _ => []
  | k + 1, i =>
    { sym := 40 + i
      align := 8
      readOnly := true
      bytes := [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
      zeroTail := 8
      relocs := [⟨0, .abs64, i, 0, false⟩] } :: mkScaleData k (i + 1)

def mkScaleAddrs : Nat → Nat → List (BitVec 64)
  | 0, _ => []
  | k + 1, a => BitVec.ofNat 64 a :: mkScaleAddrs k (a + 64)

def ScaleWidget : Lib where
  name := "scale_widget"
  names := scaleNameChars.map String.ofList
  code := List.replicate (540 * 4) 0#8
  align := 16
  symbols := [(0, 0)]
  relocs := mkScaleRelocs 270 0
  externs := (List.range 39).map (· + 1)
  data := mkScaleData 460 0
  exports := [0]

def lyScale : Layout where
  base := 0x100000#64
  addrs := 0#64 :: mkScaleAddrs 499 0x200040
  relax := []
  b2b := []

set_option maxRecDepth 200000 in
theorem scaleWidget_placeable :
    ∃ pl, ScaleWidget.toLib.Placeable pl ∧ (ScaleWidget.toLib.text.externs.map pl.ρ).Nodup :=
  exists_placeable_and_externs_of_checkPlaceable (ly := lyScale) rfl rfl (by decide +kernel)

/-! ## Split-Check Placement Helpers (`placeable_and_externs_of_split_checks`) -/

set_option maxRecDepth 200000 in
theorem scaleWidget_namesOk : namesNodup scaleNameChars = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem scaleWidget_idsOk : ScaleWidget.idsOk = true := by decide +kernel

theorem scaleWidget_sizeOk : Nat.blt ScaleWidget.names.length 1048576 = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem scaleWidget_textOk : checkTextPlaceable ScaleWidget lyScale = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem scaleWidget_dataOk : checkDataPlaceable ScaleWidget lyScale = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem scaleWidget_relocsOk : checkTextRelocsOk ScaleWidget lyScale = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem scaleWidget_externsOk : checkExternsDisjoint ScaleWidget lyScale = true := by decide +kernel

theorem scaleWidget_placeable_split :
    ScaleWidget.toLib.Placeable (lyScale.toPlacement ScaleWidget.names) :=
  placeable_of_split_checks rfl rfl scaleWidget_namesOk scaleWidget_idsOk scaleWidget_sizeOk
    scaleWidget_textOk scaleWidget_dataOk scaleWidget_relocsOk

theorem scaleWidget_exists_placeable_split : ∃ pl, ScaleWidget.toLib.Placeable pl :=
  exists_placeable_of_split_checks rfl rfl scaleWidget_namesOk scaleWidget_idsOk scaleWidget_sizeOk
    scaleWidget_textOk scaleWidget_dataOk scaleWidget_relocsOk

theorem scaleWidget_placeable_and_externs_split :
    ScaleWidget.toLib.Placeable (lyScale.toPlacement ScaleWidget.names) ∧
      (ScaleWidget.toLib.text.externs.map (lyScale.toPlacement ScaleWidget.names).ρ).Nodup :=
  placeable_and_externs_of_split_checks rfl rfl scaleWidget_namesOk scaleWidget_idsOk
    scaleWidget_sizeOk scaleWidget_textOk scaleWidget_dataOk scaleWidget_relocsOk
    scaleWidget_externsOk

theorem scaleWidget_exists_placeable_and_externs_split :
    ∃ pl, ScaleWidget.toLib.Placeable pl ∧ (ScaleWidget.toLib.text.externs.map pl.ρ).Nodup :=
  exists_placeable_and_externs_of_split_checks rfl rfl scaleWidget_namesOk scaleWidget_idsOk
    scaleWidget_sizeOk scaleWidget_textOk scaleWidget_dataOk scaleWidget_relocsOk
    scaleWidget_externsOk

/--
error: Tactic `decide` proved that the proposition
  checkExternsDisjoint GotTlsWidget lyGotTlsAliasedExterns = true
is false
-/
#guard_msgs (error, drop info) in
example : checkExternsDisjoint GotTlsWidget lyGotTlsAliasedExterns = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  checkTextRelocsOk GotTlsWidget lyGotTlsBadAdr = true
is false
-/
#guard_msgs (error, drop info) in
example : checkTextRelocsOk GotTlsWidget lyGotTlsBadAdr = true := by
  decide +kernel

/-! ## Short-Circuiting `CodeBlock.relaxedAtFast` and `CodeBlock.checkPlaceable` Tests -/

example (pl : Placement) (off : Nat) :
    ({ code := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] } : CodeBlock).relaxedAt pl off = false :=
  CodeBlock.relaxedAt_of_relocs_nil rfl off

example (blk : CodeBlock) (off : Nat) :
    blk.relaxedAt { base := 0x1000#64, ρ := fun _ => 0x2000#64 } off = false :=
  CodeBlock.relaxedAt_of_relax_false rfl

example (blk : CodeBlock) (pl : Placement) (off : Nat) :
    blk.relaxedAtFast pl off = blk.relaxedAt pl off :=
  CodeBlock.relaxedAtFast_eq blk pl off

def unrelaxedWitnessPl : Placement where
  base := 0x100000#64
  ρ _ := 0x200040#64

set_option maxRecDepth 200000 in
theorem scaleWidget_codeBlock_placeable_direct :
    ScaleWidget.toLib.text.Placeable unrelaxedWitnessPl :=
  CodeBlock.placeable_of_checkPlaceable (by decide +kernel)

set_option linter.unusedSimpArgs true in
theorem widget_codeBlock_checkPlaceable_simp :
    Widget.toLib.text.checkPlaceable unrelaxedWitnessPl = true := by
  simp only [Obj.CodeBlock.checkPlaceable, Obj.CodeBlock.relaxedAt, unrelaxedWitnessPl,
    Bool.and_false, Bool.not_false, Bool.true_or, Bool.and_true]
  decide +kernel

def twoBlockMultiWidget : MultiPlacedLib where
  name := "two_block_widget"
  blocks := [Widget.toLib.text, { code := wordsLE [0xd65f03c0#32], symbols := [("g", 0)] }]
  data := Widget.toLib.data
  exports := ["f", "g"]

def twoBlockWitnessMpl : MultiPlacement where
  base i := if i == 0 then 0x100000#64 else 0x101000#64
  ρ sym := if sym == "ext" then 0x200000#64 else if sym == "buf" then 0x300000#64 else 0x300010#64

theorem twoBlock_blksOk : twoBlockMultiWidget.checkBlocksPlaceable twoBlockWitnessMpl = true := by
  decide +kernel

theorem twoBlock_disjOk : twoBlockMultiWidget.checkBlocksDisjoint twoBlockWitnessMpl = true := by
  decide +kernel

theorem twoBlock_symsOk : twoBlockMultiWidget.checkBlockSymbolsNodup = true := by decide +kernel

theorem twoBlock_dataNdOk : twoBlockMultiWidget.checkDataNodup = true := by decide +kernel

theorem twoBlock_dataOk : twoBlockMultiWidget.checkDataPlaceable twoBlockWitnessMpl = true := by
  decide +kernel

theorem twoBlock_placeable_split : twoBlockMultiWidget.Placeable twoBlockWitnessMpl :=
  MultiPlacedLib.placeable_of_split_checks twoBlock_blksOk twoBlock_disjOk twoBlock_symsOk
    twoBlock_dataNdOk twoBlock_dataOk

theorem twoBlock_exists_placeable_split : ∃ mpl, twoBlockMultiWidget.Placeable mpl :=
  MultiPlacedLib.exists_placeable_of_split_checks twoBlock_blksOk twoBlock_disjOk twoBlock_symsOk
    twoBlock_dataNdOk twoBlock_dataOk

end Examples.Testing.PlacedCheckTest
