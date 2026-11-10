/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed

/-!
# ELF Symbol Precedence Regression Tests

Regression tests for `Arm64.Obj.Resolves`, `Arm64.Obj.Discarded`, their decidable checkers in
`ProofLib.Placed.LabelsCheck`, and the conservative interned `gen_labels_from_objects` path:
weak/strong symbol precedence, duplicate-global and `.other` fail-closed competitors, COMDAT
group deduplication, and local vs. overridden-weak relocation resolution.
-/

@[expose] public section

namespace Examples.Testing.LabelsPrecedenceTest

open Arm64 Arm64.Obj ProofLib

/-! ## Fixture Helpers -/

def nopBytes (n : Nat) : List (BitVec 8) :=
  List.flatten (List.replicate n [0x1f#8, 0x20#8, 0x03#8, 0xd5#8])

def textSec (name : String) (n : Nat) (relocs : List RawReloc := []) : RawSec :=
  { name := name, bytes := nopBytes n, size := 4 * n, align := 4, isExec := true,
    readOnly := true, isNobits := false, isTls := false, relocs := relocs }

def fn (raw : String) (bind : SymBind) (sec : SymSec) (size : Nat := 4) (name : String := raw) :
    RawSym :=
  { rawName := raw, name := name, sec := sec, value := 0, size := size, kind := .func, bind := bind }

def obj1 (name : String) (syms : List RawSym) (groups : List RawGroup := []) : ExtractedObj :=
  { name := name, sections := [textSec ".text.f" 1], symbols := syms, groups := groups }

/-! ## Weak vs. Strong -/

def WeakThenStrong : List ExtractedObj :=
  [obj1 "w.o" [fn "foo" .weak (.sec 0)], obj1 "s.o" [fn "foo" .global (.sec 0)]]

theorem weak_strong_find :
    findResolves? WeakThenStrong "foo" = some (1, 0, 0, fn "foo" .global (.sec 0)) := by
  decide +kernel

theorem weak_strong_strong_resolves :
    Resolves WeakThenStrong "foo" 1 0 0 (fn "foo" .global (.sec 0)) :=
  resolves_of_check (by decide +kernel)

theorem neg_weak_strong_weak_check :
    checkResolvesB WeakThenStrong "foo" 0 0 0 (fn "foo" .weak (.sec 0)) = false := by
  decide +kernel

theorem neg_weak_strong_weak_not_resolves :
    ¬Resolves WeakThenStrong "foo" 0 0 0 (fn "foo" .weak (.sec 0)) := fun h =>
  absurd (Resolves.unique h weak_strong_strong_resolves).1 (by decide)

/-! ## Weak vs. Weak -/

def WeakWeak : List ExtractedObj :=
  [obj1 "a.o" [fn "foo" .weak (.sec 0)], obj1 "b.o" [fn "foo" .weak (.sec 0)]]

theorem weak_weak_first_resolves :
    Resolves WeakWeak "foo" 0 0 0 (fn "foo" .weak (.sec 0)) :=
  resolves_of_check (by decide +kernel)

theorem weak_weak_find :
    findResolves? WeakWeak "foo" = some (0, 0, 0, fn "foo" .weak (.sec 0)) := by
  decide +kernel

theorem neg_weak_weak_second_check :
    checkResolvesB WeakWeak "foo" 1 0 0 (fn "foo" .weak (.sec 0)) = false := by
  decide +kernel

theorem neg_weak_weak_second_not_resolves :
    ¬Resolves WeakWeak "foo" 1 0 0 (fn "foo" .weak (.sec 0)) := fun h =>
  absurd (Resolves.unique h weak_weak_first_resolves).1 (by decide)

/-! ## Unique Weak Definition -/

def UniqueWeak : List ExtractedObj :=
  [obj1 "a.o" [fn "foo" .weak .undef], obj1 "b.o" [fn "foo" .weak (.sec 0)]]

theorem unique_weak_resolves :
    Resolves UniqueWeak "foo" 1 0 0 (fn "foo" .weak (.sec 0)) :=
  resolves_of_check (by decide +kernel)

/-! ## Fail-Closed Competitors -/

def StrongStrong : List ExtractedObj :=
  [obj1 "a.o" [fn "foo" .global (.sec 0)], obj1 "b.o" [fn "foo" .global (.sec 0)]]

theorem neg_strong_strong_check :
    checkResolvesB StrongStrong "foo" 0 0 0 (fn "foo" .global (.sec 0)) = false ∧
      checkResolvesB StrongStrong "foo" 1 0 0 (fn "foo" .global (.sec 0)) = false := by
  decide +kernel

theorem neg_strong_strong_not_resolves (oi k si : Nat) (sy : RawSym) :
    ¬Resolves StrongStrong "foo" oi k si sy :=
  Resolves.not_of_two_global (o1 := obj1 "a.o" [fn "foo" .global (.sec 0)])
    (o2 := obj1 "b.o" [fn "foo" .global (.sec 0)]) (oi1 := 0) (k1 := 0) (oi2 := 1) (k2 := 0)
    rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (Or.inl (by decide))

/-- A weak definition does not beat an `.other` (e.g. `STB_GNU_UNIQUE`) competitor. -/
def WeakOther : List ExtractedObj :=
  [obj1 "a.o" [fn "foo" .weak (.sec 0)], obj1 "b.o" [fn "foo" .other (.sec 0)]]

theorem neg_weak_other_check :
    checkResolvesB WeakOther "foo" 0 0 0 (fn "foo" .weak (.sec 0)) = false := by
  decide +kernel

/-- A weak definition does not beat an `SHN_ABS`-style (`.other` section) competitor. -/
def WeakAbs : List ExtractedObj :=
  [obj1 "a.o" [fn "foo" .weak (.sec 0)], obj1 "b.o" [fn "foo" .weak .other]]

theorem neg_weak_abs_check :
    checkResolvesB WeakAbs "foo" 0 0 0 (fn "foo" .weak (.sec 0)) = false := by
  decide +kernel

/-! ## COMDAT Duplicate Groups -/

def ComdatDup : List ExtractedObj :=
  [obj1 "a.o" [fn "inl" .weak (.sec 0)] [{ signature := "inl", members := [0] }],
   obj1 "b.o" [fn "inl" .weak (.sec 0)] [{ signature := "inl", members := [0] }]]

theorem comdat_first_kept : ¬Discarded ComdatDup 0 0 := by decide +kernel

theorem comdat_second_discarded : Discarded ComdatDup 1 0 :=
  discarded_iff_check.1 (by decide +kernel)

theorem comdat_first_resolves :
    Resolves ComdatDup "inl" 0 0 0 (fn "inl" .weak (.sec 0)) :=
  resolves_of_check (by decide +kernel)

theorem neg_comdat_second_check :
    checkResolvesB ComdatDup "inl" 1 0 0 (fn "inl" .weak (.sec 0)) = false := by
  decide +kernel

theorem neg_comdat_no_discarded_check : checkNoDiscardedB ComdatDup = false := by
  decide +kernel

def ComdatLib : MultiPlacedLib :=
  { name := "comdat"
    blocks :=
      [ { code := nopBytes 1, align := 4, symbols := [("inl", 0)], relocs := [], externs := [],
          weakRefs := [] } ]
    data := []
    exports := [] }

theorem comdat_kept_slice_accepted :
    checkLabelsFromObjectsB ComdatDup ComdatLib [{ oi := 0, si := 0, start := 0, len := 4 }] []
      = true := by
  decide +kernel

theorem neg_comdat_discarded_slice_rejected :
    checkLabelsFromObjectsB ComdatDup ComdatLib [{ oi := 1, si := 0, start := 0, len := 4 }] []
      = false := by
  decide +kernel

theorem neg_comdat_discarded_text_slice :
    checkValidTextSliceB ComdatDup ComdatLib.blocks[0] { oi := 1, si := 0, start := 0, len := 4 }
      = false := by
  decide +kernel

/-! ## Relocation Targets: Local Branch and Overridden Weak Definitions -/

/-- `a.o` calls its `STB_LOCAL` `helper` (symbol 1) and its `STB_WEAK` `foo` (symbol 2); `b.o`
    defines an `STB_GLOBAL` `helper` and an `STB_GLOBAL` `foo`. The local call stays in `a.o`; the
    weak call resolves to `b.o`'s strong `foo`. -/
def RelocObjs : List ExtractedObj :=
  [ { name := "a.o"
      sections :=
        [ textSec ".text.caller" 2
            [ { off := 0, kind := some .call26, symIdx := 1, addend := 0 }
            , { off := 4, kind := some .call26, symIdx := 2, addend := 0 } ]
        , textSec ".text.helper" 1
        , textSec ".text.weak_foo" 1 ]
      symbols :=
        [ fn "caller" .global (.sec 0) 8
        , fn "helper" .local (.sec 1) 4 "helper [a.o]"
        , fn "foo" .weak (.sec 2) 4 "foo [a.o]" ] }
  , { name := "b.o"
      sections := [textSec ".text.helper" 1, textSec ".text.foo" 1]
      symbols := [fn "helper" .global (.sec 0), fn "foo" .global (.sec 1)] } ]

def RelocLib : MultiPlacedLib :=
  { name := "reloc_targets"
    blocks :=
      [ { code := nopBytes 2, align := 4, symbols := [("caller", 0)]
          relocs :=
            [ { off := 0, kind := .call26, sym := "helper [a.o]", addend := 0 }
            , { off := 4, kind := .call26, sym := "foo", addend := 0 } ]
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("helper [a.o]", 0)], relocs := [],
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("helper", 0)], relocs := [],
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("foo", 0)], relocs := [],
          externs := [], weakRefs := [] } ]
    data := []
    exports := ["caller", "foo"] }

def relocBO : List SliceOrigin :=
  [ { oi := 0, si := 0, start := 0, len := 8 }
  , { oi := 0, si := 1, start := 0, len := 4 }
  , { oi := 1, si := 0, start := 0, len := 4 }
  , { oi := 1, si := 1, start := 0, len := 4 } ]

theorem reloc_targets_direct : ∃ bO dO, LabelsFromObjects RelocObjs RelocLib bO dO :=
  exists_labelsFromObjects_of_check (bO := relocBO) (dO := []) (by decide +kernel)

/-- Binding the weak call to `a.o`'s overridden `foo` is rejected. -/
def RelocBadLib : MultiPlacedLib :=
  { RelocLib with
    blocks :=
      [ { code := nopBytes 2, align := 4, symbols := [("caller", 0)]
          relocs :=
            [ { off := 0, kind := .call26, sym := "helper [a.o]", addend := 0 }
            , { off := 4, kind := .call26, sym := "foo [a.o]", addend := 0 } ]
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("helper [a.o]", 0)], relocs := [],
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("helper", 0)], relocs := [],
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("foo", 0)], relocs := [],
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("foo [a.o]", 0)], relocs := [],
          externs := [], weakRefs := [] } ] }

theorem neg_reloc_overridden_weak_rejected :
    checkLabelsFromObjectsB RelocObjs RelocBadLib
      (relocBO ++ [{ oi := 0, si := 2, start := 0, len := 4 }]) [] = false := by
  decide +kernel

/-- Binding the local call to `b.o`'s same-named global `helper` is rejected. -/
def RelocLocalBadLib : MultiPlacedLib :=
  { RelocLib with
    blocks :=
      [ { code := nopBytes 2, align := 4, symbols := [("caller", 0)]
          relocs :=
            [ { off := 0, kind := .call26, sym := "helper", addend := 0 }
            , { off := 4, kind := .call26, sym := "foo", addend := 0 } ]
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("helper [a.o]", 0)], relocs := [],
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("helper", 0)], relocs := [],
          externs := [], weakRefs := [] }
      , { code := nopBytes 1, align := 4, symbols := [("foo", 0)], relocs := [],
          externs := [], weakRefs := [] } ] }

theorem neg_reloc_local_to_global_rejected :
    checkLabelsFromObjectsB RelocObjs RelocLocalBadLib relocBO [] = false := by
  decide +kernel

/-! ## Conservative Interned Checker -/

-- The interned checker accepts only unique non-local definitions: the overridden in-object weak
-- definition makes it fail closed even though the reference checker accepts `RelocLib`.
/--
error: gen_labels_from_objects: block[0] raw relocation #1 at off=4 has no matching placed RelocEntry
-/
#guard_msgs in
gen_labels_from_objects reloc_targets_lbl RelocObjs RelocLib

-- Duplicate COMDAT signatures fail the interned `checkNoDiscardedB` side condition.
/--
error: (kernel) declaration type mismatch, '_private.ProofLib.Testing.LabelsPrecedence.0.Examples.Testing.LabelsPrecedenceTest.comdat_lbl_groups_ok' has type
  checkNoDiscardedB ComdatDup = checkNoDiscardedB ComdatDup
but it is expected to have type
  checkNoDiscardedB ComdatDup = true
-/
#guard_msgs in
gen_labels_from_objects comdat_lbl ComdatDup ComdatLib

end Examples.Testing.LabelsPrecedenceTest

end
