/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProgramReflection.SortedFresh

/-!
# Sorted Freshness Regression Tests

Regression tests for `ProofLib.ProgramReflection.SortedFresh` (`sortedFreshEntries`,
`isStrictSorted`, `allFreshCharSymbols_of_sorted`, `allFreshCharAssoc_of_sorted`, and
`Arm64.Obj.assignSpans`).
-/

@[expose] public section

namespace Examples.Testing.SortedFreshTest

open ProofLib.ProgramReflection

/-! ## Key order -/

example : keyLt (1, [5]) (2, [0, 0]) = true := by decide
example : keyLt (2, [0, 0]) (1, [5]) = false := by decide
example : keyLt (2, [3, 9]) (2, [4, 0]) = true := by decide
example : keyLt (2, [4, 0]) (2, [3, 9]) = false := by decide
example : keyLt (2, [4, 0]) (2, [4, 0]) = false := by decide

/-! ## Sort sanity -/

example :
    mergeSortFuel keyLt 5 [(2, [4, 0]), (1, [9]), (2, [3, 9]), (1, [1]), (3, [0, 0, 0])] =
      [(1, [1]), (1, [9]), (2, [3, 9]), (2, [4, 0]), (3, [0, 0, 0])] := by decide

example : (mergeSortFuel keyLt 0 [(2, [4, 0]), (1, [9])]) = [(2, [4, 0]), (1, [9])] := by decide

/-! ## Positive -/

example : sortedFreshEntries [(2, [4, 0]), (1, [9]), (2, [3, 9]), (1, [1]), (3, [0, 0, 0])] = true := by
  decide

example : sortedFreshEntries [] = true := by decide
example : sortedFreshEntries [(1, [7])] = true := by decide

def widgetSyms : List (List Char × Nat) :=
  [("widget_init".toList, 0x40), ("widget".toList, 0x0), ("alpha".toList, 0x80),
   ("alphb".toList, 0xc0), ("codec_run".toList, 0x100), ("codec_rún".toList, 0x140),
   ("a".toList, 0x180), ("".toList, 0x1c0)]

theorem widgetSyms_fresh : allFreshCharSymbols widgetSyms = true :=
  allFreshCharSymbols_of_sorted (by rfl_kernel)

def widgetAssoc : List (List Char × (Nat × Nat)) :=
  widgetSyms.map fun (cs, off) => (cs, (off, 16))

theorem widgetAssoc_fresh : allFreshCharAssoc widgetAssoc = true :=
  allFreshCharAssoc_of_sorted (by rfl_kernel)

example : allFreshCharSymbols widgetSyms = true := by decide

/-! ## Strict-sorted `O(n)` check -/

def strictWidgetSyms : List (List Char × Nat) :=
  [("".toList, 0x1c0), ("a".toList, 0x180), ("alpha".toList, 0x80),
   ("alphb".toList, 0xc0), ("codec_run".toList, 0x100), ("codec_rún".toList, 0x140),
   ("widget".toList, 0x0), ("widget_init".toList, 0x40)]

theorem strictWidgetSyms_pairwise : strictWidgetSyms.Pairwise (fun a b => a.1 ≠ b.1) :=
  pairwise_ne_of_strictSorted (by rfl_kernel)

theorem strictWidgetSyms_fresh : allFreshCharSymbols strictWidgetSyms = true :=
  allFreshCharSymbols_of_strictSorted (by rfl_kernel)

def strictWidgetAssoc : List (List Char × (Nat × Nat)) :=
  strictWidgetSyms.map fun (cs, off) => (cs, (off, 16))

theorem strictWidgetAssoc_fresh : allFreshCharAssoc strictWidgetAssoc = true :=
  allFreshCharAssoc_of_strictSorted (by rfl_kernel)

def literalCharSyms : List (List Char × Nat) :=
  [([], 0x1c0), (['a'], 0x180), (['a', 'l', 'p', 'h', 'a'], 0x80),
   (['a', 'l', 'p', 'h', 'b'], 0xc0)]

theorem literalCharSyms_pairwise : literalCharSyms.Pairwise (fun a b => a.1 ≠ b.1) :=
  pairwise_ne_of_strictSorted (by rfl_kernel)

theorem literalCharSyms_fresh : allFreshCharSymbols literalCharSyms = true :=
  allFreshCharSymbols_of_strictSorted (by rfl_kernel)

/-- info: 'Examples.Testing.SortedFreshTest.literalCharSyms_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms literalCharSyms_fresh

/-- info: 'Examples.Testing.SortedFreshTest.literalCharSyms_pairwise' depends on axioms: [propext] -/
#guard_msgs in
#print axioms literalCharSyms_pairwise

/-! ## `Obj.assignSpans` `O(n log n)` span assignment -/

example :
    (Arm64.Obj.assignSpans 0x100
      [(0, ("alpha", 0x0)), (2, ("alpha_alias", 0x0)), (1, ("beta", 0x40))]).2.2 =
      [(0, ("alpha", (0x0, 0x40))), (2, ("alpha_alias", (0x0, 0x40))),
       (1, ("beta", (0x40, 0xc0)))] := by decide

/-! ## Negative (`#guard_msgs`) -/

example : sortedFreshEntries [(1, [1]), (1, [1])] = false := by decide
example : sortedFreshEntries [(2, [4, 0]), (1, [9]), (2, [3, 9]), (1, [1]), (2, [4, 0])] = false := by
  decide
example : isStrictSorted widgetSyms = false := by decide
example : isStrictSorted [("alpha".toList, 0x0), ("alpha".toList, 0x40)] = false := by decide

/--
error: (kernel) application type mismatch
  allFreshCharSymbols_of_strictSorted (Eq.refl (isStrictSorted widgetSyms))
argument has type
  isStrictSorted widgetSyms = isStrictSorted widgetSyms
but function has type
  isStrictSorted widgetSyms = true → allFreshCharSymbols widgetSyms = true
-/
#guard_msgs in
theorem widgetSyms_not_strictSorted : allFreshCharSymbols widgetSyms = true :=
  allFreshCharSymbols_of_strictSorted (by rfl_kernel)

def dupSyms : List (List Char × Nat) :=
  [("alpha".toList, 0x0), ("beta".toList, 0x40), ("gamma".toList, 0x80), ("delta".toList, 0xc0),
   ("alpha".toList, 0x100)]

/--
error: (kernel) application type mismatch
  allFreshCharSymbols_of_sorted (Eq.refl (sortedFreshEntries (prepareCharSymbols dupSyms)))
argument has type
  sortedFreshEntries (prepareCharSymbols dupSyms) = sortedFreshEntries (prepareCharSymbols dupSyms)
but function has type
  sortedFreshEntries (prepareCharSymbols dupSyms) = true → allFreshCharSymbols dupSyms = true
-/
#guard_msgs in
theorem dupSyms_fresh : allFreshCharSymbols dupSyms = true :=
  allFreshCharSymbols_of_sorted (by rfl_kernel)

example : allFreshCharSymbols dupSyms = false := by decide

end Examples.Testing.SortedFreshTest
