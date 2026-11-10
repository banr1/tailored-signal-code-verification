/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed

/-!
# Object-Label and Gate-A Regression Tests

Positive and negative regression tests for `checkLabelsFromObjectsB`, `gen_labels_from_objects`,
`checkGateALabelsB`, `GateALabelsAnchored`, and `DataLabelAnchored` on synthetic multi-object
fixtures (`AlphaObjs`, `AlphaLib`, `WeakStrongObjs`, `UniqueNonLocalObjs`).
-/

@[expose] public section

namespace Examples.Testing.LabelsCoverageTest

open Arm64 Arm64.Obj ProofLib

/-! ## Synthetic Two-Object Fixture -/

def nopBytes (n : Nat) : List (BitVec 8) :=
  List.flatten (List.replicate n [0x1f#8, 0x20#8, 0x03#8, 0xd5#8])

def alphaObj0 : ExtractedObj :=
  { name := "alpha.o"
    sections :=
      [ { name := ".text.alpha_entry"
          bytes := nopBytes 4
          size := 16
          align := 4
          isExec := true
          readOnly := true
          isNobits := false
          isTls := false
          relocs :=
            [ { off := 0, kind := some .call26, symIdx := 2, addend := 0 }
            , { off := 4, kind := some .call26, symIdx := 3, addend := 0 }
            , { off := 8, kind := some .call26, symIdx := 4, addend := 0 }
            , { off := 12, kind := some .call26, symIdx := 5, addend := 0 } ] }
      , { name := ".rodata.cst8"
          bytes := [1#8, 2#8, 3#8, 4#8, 5#8, 6#8, 7#8, 8#8]
          size := 8
          align := 8
          isExec := false
          readOnly := true
          isNobits := false
          isTls := false
          relocs := [] } ]
    symbols :=
      [ { rawName := "", name := "", sec := .undef, value := 0, size := 0,
          kind := .other, bind := .local }
      , { rawName := "_ZN5alpha5entryE", name := "alpha::entry", sec := .sec 0,
          value := 0, size := 16, kind := .func, bind := .global }
      , { rawName := "_ZN5alpha6helperE", name := "alpha::helper", sec := .undef,
          value := 0, size := 0, kind := .func, bind := .global }
      , { rawName := "__custom_rng", name := "__custom_rng", sec := .undef,
          value := 0, size := 0, kind := .func, bind := .global }
      , { rawName := "_RNvNtCs_4core9panicking5panic", name := "core::panicking::panic",
          sec := .undef, value := 0, size := 0, kind := .func, bind := .global }
      , { rawName := "weak_hook", name := "weak_hook", sec := .undef,
          value := 0, size := 0, kind := .func, bind := .weak }
      , { rawName := "MAX_FILTER", name := "log::MAX_FILTER", sec := .undef,
          value := 0, size := 0, kind := .object, bind := .global }
      , { rawName := "pruned_stub", name := "pruned_stub", sec := .undef,
          value := 0, size := 0, kind := .func, bind := .global } ] }

def alphaObj1 : ExtractedObj :=
  { name := "probe.o"
    sections :=
      [ { name := ".text.helper"
          bytes := nopBytes 4
          size := 16
          align := 4
          isExec := true
          readOnly := true
          isNobits := false
          isTls := false
          relocs :=
            [ { off := 0, kind := some .adrpHi21, symIdx := 2, addend := 0 }
            , { off := 4, kind := some .addLo12, symIdx := 3, addend := 0 }
            , { off := 8, kind := some .call26, symIdx := 4, addend := 0 } ] }
      , { name := ".bss.STORAGE"
          bytes := []
          size := 1
          align := 1
          isExec := false
          readOnly := false
          isNobits := true
          isTls := false
          relocs := [] }
      , { name := ".data.TOKEN"
          bytes := [0#8]
          size := 1
          align := 1
          isExec := false
          readOnly := false
          isNobits := false
          isTls := false
          relocs := [] } ]
    symbols :=
      [ { rawName := "", name := "", sec := .undef, value := 0, size := 0,
          kind := .other, bind := .local }
      , { rawName := "_ZN5alpha6helperE", name := "alpha::helper", sec := .sec 0,
          value := 0, size := 16, kind := .func, bind := .global }
      , { rawName := "STORAGE.0", name := "probe::STORAGE", sec := .sec 1,
          value := 0, size := 1, kind := .object, bind := .local }
      , { rawName := "TOKEN", name := "probe::TOKEN", sec := .sec 2,
          value := 0, size := 1, kind := .object, bind := .local }
      , { rawName := "unused_ext", name := "unused_ext", sec := .undef,
          value := 0, size := 0, kind := .func, bind := .global } ] }

def AlphaObjs : List ExtractedObj := [alphaObj0, alphaObj1]

def alphaExterns : List String :=
  ["__custom_rng", "_RNvNtCs_4core9panicking5panic", "weak_hook", "unused_ext"]

def AlphaLib : MultiPlacedLib :=
  { name := "alpha"
    blocks :=
      [ { code := nopBytes 4
          align := 4
          symbols := [("alpha::entry", 0)]
          relocs :=
            [ { off := 0, kind := .call26, sym := "alpha::helper", addend := 0 }
            , { off := 4, kind := .call26, sym := "__custom_rng", addend := 0 }
            , { off := 8, kind := .call26, sym := "_RNvNtCs_4core9panicking5panic", addend := 0 }
            , { off := 12, kind := .call26, sym := "weak_hook", addend := 0 } ]
          externs := alphaExterns
          weakRefs := ["weak_hook"] }
      , { code := nopBytes 4
          align := 4
          symbols := [("alpha::helper", 0)]
          relocs :=
            [ { off := 0, kind := .adrpHi21, sym := "probe::STORAGE [probe.o]", addend := 0,
                localSym := true }
            , { off := 4, kind := .addLo12, sym := "probe::TOKEN [probe.o]", addend := 0,
                localSym := true }
            , { off := 8, kind := .call26, sym := "unused_ext", addend := 0 } ]
          externs := alphaExterns
          weakRefs := ["weak_hook"] } ]
    data :=
      [ { sym := ".rodata.cst8 [alpha.o]@0"
          align := 8
          readOnly := true
          bytes := [1#8, 2#8, 3#8, 4#8, 5#8, 6#8, 7#8, 8#8]
          zeroTail := 0
          relocs := [] }
      , { sym := "probe::STORAGE [probe.o]"
          align := 1
          readOnly := false
          bytes := []
          zeroTail := 1
          relocs := [] }
      , { sym := "probe::TOKEN [probe.o]"
          align := 1
          readOnly := false
          bytes := [0#8]
          zeroTail := 0
          relocs := [] } ]
    exports := ["alpha::entry"]
    exportSyms := [("alpha::entry", "_ZN5alpha5entryE")] }

/-! ## Provenance Tests -/

def handBOList : List SliceOrigin :=
  [ { oi := 0, si := 0, start := 0, len := 16 }
  , { oi := 1, si := 0, start := 0, len := 16 } ]

def handDOList : List SliceOrigin :=
  [ { oi := 0, si := 1, start := 0, len := 8 }
  , { oi := 1, si := 1, start := 0, len := 1 }
  , { oi := 1, si := 2, start := 0, len := 1 } ]

def handDO : Fin AlphaLib.data.length → SliceOrigin
  | ⟨0, _⟩ => { oi := 0, si := 1, start := 0, len := 8 }
  | ⟨1, _⟩ => { oi := 1, si := 1, start := 0, len := 1 }
  | ⟨2, _⟩ => { oi := 1, si := 2, start := 0, len := 1 }

theorem alpha_labels_direct :
    ∃ bO dO, LabelsFromObjects AlphaObjs AlphaLib bO dO :=
  exists_labelsFromObjects_of_check (bO := handBOList) (dO := handDOList) (by decide +kernel)

gen_labels_from_objects alpha_lbl AlphaObjs AlphaLib

/-- `AlphaObjs` with a COMDAT group on `alphaObj1`, testing preservation of `ExtractedObj.groups`
    through `IObj.toExtractedObj`. -/
def AlphaGroupedObjs : List ExtractedObj :=
  [alphaObj0, { alphaObj1 with groups := [{ signature := "alpha_comdat", members := [0] }] }]

theorem alpha_grouped_labels_direct :
    ∃ bO dO, LabelsFromObjects AlphaGroupedObjs AlphaLib bO dO :=
  exists_labelsFromObjects_of_check (bO := handBOList) (dO := handDOList) (by decide +kernel)

gen_labels_from_objects alpha_grouped_lbl AlphaGroupedObjs AlphaLib

/-! ## Gate-A Anchoring and Elimination Tests -/

def alphaHooks : List (String × String) :=
  [("__custom_rng", "__custom_rng")]

def alphaPruned : List String := ["pruned_stub"]
def alphaExternData : List String := ["MAX_FILTER"]
def alphaPanics : List String := ["_RNvNtCs_4core9panicking5panic"]
def alphaIsPanic (s : String) : Bool := s == "_RNvNtCs_4core9panicking5panic"

def storageSpec : CoveredDataSpec :=
  { di := 1
    sym := "probe::STORAGE [probe.o]"
    origin := { oi := 1, si := 1, start := 0, len := 1 }
    rawName := "STORAGE.0"
    demangledName := "probe::STORAGE"
    expectedReadOnly := some false
    expectedBytes := some []
    expectedZeroTail := some 1
    soleInSection := true }

def tokenSpec : CoveredDataSpec :=
  { di := 2
    sym := "probe::TOKEN [probe.o]"
    origin := { oi := 1, si := 2, start := 0, len := 1 }
    rawName := "TOKEN"
    demangledName := "probe::TOKEN"
    expectedReadOnly := some false
    expectedBytes := some [0#8]
    expectedZeroTail := some 0
    soleInSection := true }

def alphaDataSpecs : List CoveredDataSpec := [storageSpec, tokenSpec]

theorem alpha_gate_a_anchored :
    GateALabelsAnchored AlphaObjs AlphaLib handDO alphaExterns alphaHooks alphaPruned
      alphaExternData alphaPanics [] alphaIsPanic 2 alphaDataSpecs :=
  gateALabels_of_check (by decide +kernel)

theorem alpha_gate_a_with_gen_dO :
    GateALabelsAnchored AlphaObjs AlphaLib alpha_lbl_dO alphaExterns alphaHooks alphaPruned
      alphaExternData alphaPanics [] alphaIsPanic 2 alphaDataSpecs :=
  gateALabels_of_check (by decide +kernel)

/-- Hook-first and panic-first dispatch agree on any hook table keyed by `alphaHooks`. -/
theorem alpha_hookFirst_eq_panicFirst (rngHook : State → State) (x : String) :
    (match lookup x [("__custom_rng", rngHook)] with
     | some h => some h
     | none => if alphaIsPanic x then some Rust.panicked else none) =
    (if alphaIsPanic x then some Rust.panicked else lookup x [("__custom_rng", rngHook)]) :=
  by
    have h := alpha_gate_a_anchored.hookFirst_eq_panicFirst [("__custom_rng", rngHook)]
      (by intro p hp; simp at hp; subst hp; simp [alphaHooks]) Rust.panicked x
    cases hlk : lookup x [("__custom_rng", rngHook)] <;> rw [hlk] at h <;> exact h

/-- Placement where both unhooked externs (`weak_hook` and `unused_ext`) share dummy address `0#64`
    (as in `--gc-sections` linked ELFs), while active hook and panic stubs sit at distinct addresses. -/
def alphaMpl : MultiPlacement :=
  { base := fun i => if i == 0 then 0x1000#64 else 0x1100#64
    ρ := fun s =>
      if s == "__custom_rng" then 0x2000#64
      else if s == "_RNvNtCs_4core9panicking5panic" then 0x3000#64
      else if s == "probe::STORAGE [probe.o]" then 0x4000#64
      else if s == "probe::TOKEN [probe.o]" then 0x4008#64
      else 0#64 }

def alphaExternFn (rngHook : State → State) (s : String) : Option (State → State) :=
  if alphaIsPanic s then some Rust.panicked else lookup s [("__custom_rng", rngHook)]

private theorem alphaExternFn_inactive (rngHook : State → State) :
    ∀ x ∈ alphaExterns, x ∉ alphaHooks.map Prod.fst → x ∉ alphaPanics →
      alphaExternFn rngHook x = none := by
  intro x _ hnhk hnpan
  simp only [alphaHooks, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hnhk
  simp only [alphaPanics, List.mem_cons, List.not_mem_nil, or_false] at hnpan
  have h1 : alphaIsPanic x = false := by simp [alphaIsPanic, beq_eq_false_iff_ne, hnpan]
  have h2 : lookup x [("__custom_rng", rngHook)] = none := by
    simp [lookup, List.find?, beq_eq_false_iff_ne.2 (Ne.symm hnhk)]
  simp [alphaExternFn, h1, h2]

/-- `externAt?` evaluates to `some rngHook` at `0x2000#64` despite `weak_hook` and `unused_ext`
    both mapping to `0#64`. -/
theorem alpha_externAt_rng (rngHook : State → State) :
    (AlphaLib.blockProgram alphaMpl 0 (alphaExternFn rngHook)).externAt? 0x2000#64 =
      some rngHook := by
  have hact_nd : (((alphaHooks.map Prod.fst) ++ alphaPanics).map alphaMpl.ρ).Nodup := by decide
  have he : "__custom_rng" ∈ (alphaHooks.map Prod.fst) ++ alphaPanics := by decide
  have hr : alphaMpl.ρ "__custom_rng" = 0x2000#64 := rfl
  rw [← hr, alpha_gate_a_with_gen_dO.externAt?_at_active alpha_lbl_spec alphaMpl (by decide)
    (alphaExternFn rngHook) (alphaExternFn_inactive rngHook) hact_nd he]
  rfl

/-- `externAt?` evaluates to `none` at dummy address `0#64`. -/
theorem alpha_externAt_zero_none (rngHook : State → State) :
    (AlphaLib.blockProgram alphaMpl 0 (alphaExternFn rngHook)).externAt? 0#64 = none := by
  have hact_nd : (((alphaHooks.map Prod.fst) ++ alphaPanics).map alphaMpl.ρ).Nodup := by decide
  exact alpha_gate_a_with_gen_dO.externAt?_outside_active alpha_lbl_spec alphaMpl (by decide)
    (alphaExternFn rngHook) (alphaExternFn_inactive rngHook) hact_nd (by decide)

/-- `DataLabelAnchored.sole_reloc_sym_eq` + `resolve_eq_rho` connect `probe.o`'s raw `STB_LOCAL`
    relocation on `TOKEN` directly to `alphaMpl.ρ "probe::TOKEN [probe.o]"`. -/
theorem alpha_token_reloc_provenance :
    AlphaLib.resolve alphaMpl tokenSpec.sym = 0x4008#64 ∧
    ∃ r ∈ AlphaLib.blocks[1].relocs,
      r.off = 4 ∧ r.kind = .addLo12 ∧ r.sym = "probe::TOKEN [probe.o]" ∧ r.addend = 0 := by
  have htok : DataLabelAnchored AlphaObjs AlphaLib alpha_lbl_dO tokenSpec :=
    alpha_gate_a_with_gen_dO.data_anchored tokenSpec (by simp [alphaDataSpecs])
  refine ⟨?_, ?_⟩
  · rw [htok.resolve_eq_rho alpha_lbl_spec alphaMpl]
    rfl
  · let bi : Fin AlphaLib.blocks.length := ⟨1, by decide⟩
    have hbO : alpha_lbl_bO bi = { oi := 1, si := 0, start := 0, len := 16 } := by decide +kernel
    let rr : RawReloc := { off := 4, kind := some .addLo12, symIdx := 3, addend := 0 }
    let sy : RawSym :=
      { rawName := "TOKEN", name := "probe::TOKEN", sec := .sec 2,
        value := 0, size := 1, kind := .object, bind := .local }
    have hbobj : AlphaObjs[(alpha_lbl_bO bi).oi]? = some alphaObj1 := by rw [hbO]; rfl
    have hbsec : alphaObj1.sections[(alpha_lbl_bO bi).si]? = some alphaObj1.sections[0] := by
      rw [hbO]; rfl
    have hrr : rr ∈ alphaObj1.sections[0].relocs := by decide
    have hlo : (alpha_lbl_bO bi).start ≤ rr.off := by rw [hbO]; decide
    have hhi : rr.off < (alpha_lbl_bO bi).start + (alpha_lbl_bO bi).len := by rw [hbO]; decide
    have hsy : alphaObj1.symbols[rr.symIdx]? = some sy := rfl
    obtain ⟨r, hr_mem, hoff, hkind, hsym, hadd⟩ :=
      htok.sole_reloc_sym_eq alpha_lbl_spec rfl bi hbobj hbsec hrr hlo hhi hsy
        (t := 0) (Or.inl ⟨by rw [hbO]; rfl, rfl, rfl, rfl⟩)
    rw [hbO] at hoff
    dsimp only [tokenSpec, rr] at hoff hkind hadd
    exact ⟨r, hr_mem, by omega, Option.some.inj hkind.symm, hsym, by omega⟩

/-! ## Negative Regression Tests -/

/-- Misspelled external data symbol (`MAX_FILTRE` absent from `AlphaObjs`) is rejected. -/
theorem neg_typo_extern_data_rejected :
    checkExternDataUndefB AlphaObjs ["MAX_FILTRE"] = false := by decide +kernel

/-- Defined non-local symbol (`_ZN5alpha5entryE`) listed in `externData` is rejected. -/
theorem neg_defined_extern_data_rejected :
    checkExternDataUndefB AlphaObjs ["_ZN5alpha5entryE"] = false := by decide +kernel

/-- Mismatched hook demangled name is rejected. -/
theorem neg_wrong_hook_demangled_rejected :
    checkGateALabelsB AlphaObjs AlphaLib handDO alphaExterns
      [("__custom_rng", "wrong::demangled")] alphaPruned alphaExternData alphaPanics []
      alphaIsPanic 2 alphaDataSpecs = false := by decide +kernel

/-- Hooked symbol also listed in `prunedStubs` is rejected. -/
theorem neg_hooked_pruned_stub_rejected :
    checkGateALabelsB AlphaObjs AlphaLib handDO alphaExterns alphaHooks
      ["__custom_rng"] alphaExternData alphaPanics [] alphaIsPanic 2 alphaDataSpecs = false := by
  decide +kernel

/-- Non-panic `.undef` symbol (`unused_ext`) placed into `panicSyms` is rejected. -/
theorem neg_bogus_panic_sym_rejected :
    checkGateALabelsB AlphaObjs AlphaLib handDO alphaExterns alphaHooks alphaPruned
      alphaExternData ["_RNvNtCs_4core9panicking5panic", "unused_ext"] []
      (fun s => s == "_RNvNtCs_4core9panicking5panic" || s == "unused_ext") 1
      alphaDataSpecs = false := by decide +kernel

/-- Omitting `.o` panic symbol `_RNvNtCs_4core9panicking5panic` (referenced in `alphaExterns`) from
    `panicSyms` is rejected by completeness (`panics_complete`). -/
theorem neg_omitted_panic_sym_rejected :
    checkGateALabelsB AlphaObjs AlphaLib handDO alphaExterns alphaHooks alphaPruned
      alphaExternData [] [] (fun _ => false) 3 alphaDataSpecs = false := by decide +kernel

/-- Overbroad `isPanic := fun _ => true` is rejected. -/
theorem neg_overbroad_isPanic_rejected :
    checkGateALabelsB AlphaObjs AlphaLib handDO alphaExterns alphaHooks alphaPruned
      alphaExternData alphaPanics [] (fun _ => true) 2 alphaDataSpecs = false := by
  decide +kernel

/-- Wrong `CoveredDataSpec` (`expectedReadOnly := some true` on writable `TOKEN`) is rejected. -/
theorem neg_wrong_covered_data_rejected :
    checkCoveredDataSpecB AlphaObjs AlphaLib handDO
      { tokenSpec with expectedReadOnly := some true } = false := by decide +kernel

/-- Tampered `MultiPlacedLib` whose block bytes do not match any `.o` slice. -/
def BadAlphaLib : MultiPlacedLib :=
  { AlphaLib with
    blocks :=
      [ { code := [0x00#8, 0x00#8, 0x00#8, 0x00#8]
          align := 4
          symbols := [("alpha::entry", 0)] } ] }

/--
error: gen_labels_from_objects: could not locate SliceOrigin for block 0 (first symbol: some "alpha::entry")
-/
#guard_msgs in
gen_labels_from_objects bad_alpha_lbl AlphaObjs BadAlphaLib

/-! ## In-Object Non-Local Relocation Binding and Weak/Strong Precedence -/

/-- `a.o` defines `STB_WEAK` `foo` and calls `foo` via an in-object `.call26` against its own
    `.symtab` entry, while `b.o` defines a strong `STB_GLOBAL` `foo`. Static linkers bind `a.o`'s
    `bl foo` to `b.o`'s strong copy, so `RelocMatches` rejects a `MultiPlacedLib` whose `bl` in
    `a.o` resolves to `a.o`'s weak copy. -/
def WeakStrongObjs : List ExtractedObj :=
  [ { name := "a.o"
      sections :=
        [ { name := ".text.caller"
            bytes := nopBytes 2
            size := 8
            align := 4
            isExec := true
            readOnly := true
            isNobits := false
            isTls := false
            relocs := [ { off := 0, kind := some .call26, symIdx := 1, addend := 0 } ] }
        , { name := ".text.weak_foo"
            bytes := nopBytes 1
            size := 4
            align := 4
            isExec := true
            readOnly := true
            isNobits := false
            isTls := false
            relocs := [] } ]
      symbols :=
        [ { rawName := "caller", name := "caller", sec := .sec 0, value := 0, size := 8,
            kind := .func, bind := .global }
        , { rawName := "foo", name := "foo [a.o]", sec := .sec 1, value := 0, size := 4,
            kind := .func, bind := .weak }
        , { rawName := "unused_dup", name := "unused_dup [a.o]", sec := .sec 1, value := 0,
            size := 4, kind := .func, bind := .weak } ] }
  , { name := "b.o"
      sections :=
        [ { name := ".text.strong_foo"
            bytes := nopBytes 2
            size := 8
            align := 4
            isExec := true
            readOnly := true
            isNobits := false
            isTls := false
            relocs := [] } ]
      symbols :=
        [ { rawName := "foo", name := "foo", sec := .sec 0, value := 0, size := 8,
            kind := .func, bind := .global }
        , { rawName := "unused_dup", name := "unused_dup [b.o]", sec := .sec 0, value := 0,
            size := 4, kind := .func, bind := .weak } ] } ]

def WeakStrongBadLib : MultiPlacedLib :=
  { name := "weak_strong_bad"
    blocks :=
      [ { code := nopBytes 2
          align := 4
          symbols := [("caller", 0)]
          relocs := [ { off := 0, kind := .call26, sym := "foo [a.o]", addend := 0 } ]
          externs := []
          weakRefs := [] }
      , { code := nopBytes 1
          align := 4
          symbols := [("foo [a.o]", 0)]
          relocs := []
          externs := []
          weakRefs := [] }
      , { code := nopBytes 2
          align := 4
          symbols := [("foo", 0)]
          relocs := []
          externs := []
          weakRefs := [] } ]
    data := []
    exports := ["caller"] }

def weakStrongBOList : List SliceOrigin :=
  [ { oi := 0, si := 0, start := 0, len := 8 }
  , { oi := 0, si := 1, start := 0, len := 4 }
  , { oi := 1, si := 0, start := 0, len := 8 } ]

/-- Direct decidable checker rejects in-object binding to an overridden `STB_WEAK` definition. -/
theorem neg_inobj_weak_overridden_by_strong_rejected :
    checkLabelsFromObjectsB WeakStrongObjs WeakStrongBadLib weakStrongBOList [] = false := by
  decide +kernel

/--
error: gen_labels_from_objects: block[0] raw relocation #0 at off=0 has no matching placed RelocEntry
-/
#guard_msgs in
gen_labels_from_objects bad_weak_strong_lbl WeakStrongObjs WeakStrongBadLib

/-- When `a.o`'s in-object `.call26` targets a unique non-local definition `solo` (with unreferenced
    duplicate `unused_dup` also present across `a.o` and `b.o`), both `checkLabelsFromObjectsB` and
    `gen_labels_from_objects` succeed. -/
def UniqueNonLocalObjs : List ExtractedObj :=
  [ { name := "a.o"
      sections :=
        [ { name := ".text.caller"
            bytes := nopBytes 2
            size := 8
            align := 4
            isExec := true
            readOnly := true
            isNobits := false
            isTls := false
            relocs := [ { off := 0, kind := some .call26, symIdx := 1, addend := 0 } ] }
        , { name := ".text.solo"
            bytes := nopBytes 1
            size := 4
            align := 4
            isExec := true
            readOnly := true
            isNobits := false
            isTls := false
            relocs := [] } ]
      symbols :=
        [ { rawName := "caller", name := "caller", sec := .sec 0, value := 0, size := 8,
            kind := .func, bind := .global }
        , { rawName := "solo", name := "solo", sec := .sec 1, value := 0, size := 4,
            kind := .func, bind := .weak }
        , { rawName := "unused_dup", name := "unused_dup [a.o]", sec := .sec 1, value := 0,
            size := 4, kind := .func, bind := .weak } ] }
  , { name := "b.o"
      sections :=
        [ { name := ".text.other"
            bytes := nopBytes 1
            size := 4
            align := 4
            isExec := true
            readOnly := true
            isNobits := false
            isTls := false
            relocs := [] } ]
      symbols :=
        [ { rawName := "unused_dup", name := "unused_dup [b.o]", sec := .sec 0, value := 0,
            size := 4, kind := .func, bind := .weak } ] } ]

def UniqueNonLocalLib : MultiPlacedLib :=
  { name := "unique_nonlocal_ok"
    blocks :=
      [ { code := nopBytes 2
          align := 4
          symbols := [("caller", 0)]
          relocs := [ { off := 0, kind := .call26, sym := "solo", addend := 0 } ]
          externs := []
          weakRefs := [] }
      , { code := nopBytes 1
          align := 4
          symbols := [("solo", 0)]
          relocs := []
          externs := []
          weakRefs := [] } ]
    data := []
    exports := ["caller"] }

theorem unique_nonlocal_inobj_direct :
    ∃ bO dO, LabelsFromObjects UniqueNonLocalObjs UniqueNonLocalLib bO dO :=
  exists_labelsFromObjects_of_check
    (bO := [{ oi := 0, si := 0, start := 0, len := 8 }, { oi := 0, si := 1, start := 0, len := 4 }])
    (dO := [])
    (by decide +kernel)

gen_labels_from_objects unique_nonlocal_lbl UniqueNonLocalObjs UniqueNonLocalLib

end Examples.Testing.LabelsCoverageTest

end
