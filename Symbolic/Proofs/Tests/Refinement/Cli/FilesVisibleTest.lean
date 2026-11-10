/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import ProofLib.Lemmas
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Filter Invariance of `filesOf` and `InputsFor` under `FilesVisible`

Proves that filtering an input file list to entries visible under `FilesVisible` leaves `filesOf`
unchanged at every path (`filesOf_filter_visible`), and hence turns any input meeting the first
four conjuncts of `InputsFor` into one meeting `InputsFor` (`inputsFor_filter_visible`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession

private def VisibleEntriesEq (a b : Arm64.FsState) : Prop :=
  ∀ q, q ≠ [] → q ∉ stdioPaths.map Arm64.normalizePath → a.entries q = b.entries q

private theorem VisibleEntriesEq.setEntry {a b : Arm64.FsState} (h : VisibleEntriesEq a b)
    (p : Arm64.FsPath) (e : Option Arm64.FsEntry) :
    VisibleEntriesEq (a.setEntry p e) (b.setEntry p e) := by
  intro q hne hstdio
  simp only [Arm64.FsState.setEntry]
  split
  · rfl
  · exact h q hne hstdio

private theorem VisibleEntriesEq.foldl_dir {a b : Arm64.FsState} (h : VisibleEntriesEq a b)
    (l : List Arm64.FsPath) :
    VisibleEntriesEq (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) a)
      (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) b) := by
  induction l generalizing a b with
  | nil => exact h
  | cons x xs ih => exact ih (h.setEntry _ _)

private theorem dropLast_nonEmptyPrefixes_of_invisible {q : Arm64.FsPath}
    (hinv : ¬ (q ≠ [] ∧ q ∉ stdioPaths.map Arm64.normalizePath)) :
    (Arm64.FsPath.nonEmptyPrefixes q).dropLast = [] := by
  by_cases hq : q = []
  · subst hq; rfl
  · by_cases hmem : q ∈ stdioPaths.map Arm64.normalizePath
    · have hstdio : stdioPaths.map Arm64.normalizePath =
          [["<stdin>"], ["<stdout>"], ["<stderr>"]] := rfl
      rw [hstdio] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;> rfl
    · exact False.elim (hinv ⟨hq, hmem⟩)

private theorem VisibleEntriesEq.skip_invisible {a b : Arm64.FsState} (h : VisibleEntriesEq a b)
    {p : String}
    (hinv : ¬ (Arm64.normalizePath p ≠ [] ∧
      Arm64.normalizePath p ∉ stdioPaths.map Arm64.normalizePath))
    (bs : HwBytes) :
    VisibleEntriesEq a
      ((((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) b).setFile p (some (.file bs))) := by
  rw [dropLast_nonEmptyPrefixes_of_invisible hinv]
  change VisibleEntriesEq a (b.setEntry (Arm64.normalizePath p) (some (.file bs)))
  intro q hne hstdio
  simp only [Arm64.FsState.setEntry]
  split
  · rename_i heq
    have hqp : q = Arm64.normalizePath p := beq_iff_eq.mp heq
    exact False.elim (hinv (hqp ▸ ⟨hne, hstdio⟩))
  · exact h q hne hstdio

private theorem filter_cons_pos {α : Type} (q : α → Bool) (x : α) (xs : List α)
    (hx : q x = true) : (x :: xs).filter q = x :: xs.filter q := by
  change (match q x with | true => x :: xs.filter q | false => xs.filter q) = x :: xs.filter q
  rw [hx]

private theorem filter_cons_neg {α : Type} (q : α → Bool) (x : α) (xs : List α)
    (hx : q x = false) : (x :: xs).filter q = xs.filter q := by
  change (match q x with | true => x :: xs.filter q | false => xs.filter q) = xs.filter q
  rw [hx]

private theorem VisibleEntriesEq.filesFold_filter
    (files : List (String × HwBytes)) {a b : Arm64.FsState} (h : VisibleEntriesEq a b) :
    VisibleEntriesEq
      (filesFold (files.filter fun f =>
        decide (Arm64.normalizePath f.1 ≠ [] ∧
          Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath)) a)
      (filesFold files b) := by
  induction files generalizing a b with
  | nil => exact h
  | cons f fs ih =>
    obtain ⟨p, bs⟩ := f
    by_cases hvis : Arm64.normalizePath p ≠ [] ∧
        Arm64.normalizePath p ∉ stdioPaths.map Arm64.normalizePath
    · have hflt :
          ((p, bs) :: fs).filter (fun f : String × HwBytes =>
            decide (Arm64.normalizePath f.1 ≠ [] ∧
              Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath)) =
          (p, bs) :: fs.filter (fun f =>
            decide (Arm64.normalizePath f.1 ≠ [] ∧
              Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath)) :=
        filter_cons_pos
          (fun f : String × HwBytes =>
            decide (Arm64.normalizePath f.1 ≠ [] ∧
              Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath))
          (p, bs) fs (decide_eq_true hvis)
      rw [hflt]
      exact ih ((h.foldl_dir _).setEntry _ _)
    · have hflt :
          ((p, bs) :: fs).filter (fun f : String × HwBytes =>
            decide (Arm64.normalizePath f.1 ≠ [] ∧
              Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath)) =
          fs.filter (fun f =>
            decide (Arm64.normalizePath f.1 ≠ [] ∧
              Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath)) :=
        filter_cons_neg
          (fun f : String × HwBytes =>
            decide (Arm64.normalizePath f.1 ≠ [] ∧
              Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath))
          (p, bs) fs (decide_eq_false hvis)
      rw [hflt]
      exact ih (h.skip_invisible hvis bs)

/-- Filtering `files` to entries whose canonical path is non-empty and not in `stdioPaths`
leaves `filesOf` unchanged at every path. -/
theorem filesOf_filter_visible (files : List (String × HwBytes)) (p : String) :
    filesOf (files.filter (fun f =>
      decide (Arm64.normalizePath f.1 ≠ [] ∧
        Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath))) p =
    filesOf files p := by
  unfold filesOf fsView
  split
  · rfl
  · rename_i hp
    have hfiles :
        (Arm64.Process.initFsState
          { files := files.filter (fun f =>
              decide (Arm64.normalizePath f.1 ≠ [] ∧
                Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath)) }).files p =
          (Arm64.Process.initFsState { files := files }).files p := by
      simp only [Arm64.FsState.files, Arm64.FsState.getEntry]
      split
      · rfl
      · rename_i hemp
        have hne : Arm64.normalizePath p ≠ [] := by
          intro hnil; rw [hnil] at hemp; exact hemp rfl
        rw [initFsState_entries _ _ hp, initFsState_entries _ _ hp]
        exact (VisibleEntriesEq.filesFold_filter files (fun _ _ _ => rfl))
          (Arm64.normalizePath p) hne hp
    rw [hfiles]

/-- Filtering `i.files` to visible entries (assuming visible entries are loader-admissible)
preserves the first four conjuncts of `InputsFor` and establishes `FilesVisible`. -/
theorem inputsFor_filter_visible (c : CliCall) (d : DirectorySnapshot) (i : Inputs)
    (h1 : i.argv = c.cmd.argv)
    (h2 : i.dirs = partyDirs ++ (match c.cmd with | .init _ dir => [dir] | _ => []))
    (h3 : i.stdin = c.stdin)
    (h4 : ∀ p, p ∉ stdioPaths → filesOf i.files p = (filesOf c.extra p).or (d p))
    (hload : ∀ f ∈ i.files,
      Arm64.normalizePath f.1 ≠ [] →
      Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath →
      Arm64.hasLeadingSlash f.1 = false ∧ Arm64.hasDotDot f.1 = false ∧
        f.2.length ≤ Arm64.MAX_LFS_FILESIZE) :
    InputsFor c d
      { i with files := i.files.filter (fun f =>
          decide (Arm64.normalizePath f.1 ≠ [] ∧
            Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath)) } := by
  refine ⟨h1, h2, h3, fun p hp => ?_, fun f hf => ?_⟩
  · rw [filesOf_filter_visible]
    exact h4 p hp
  · obtain ⟨hmem, hdec⟩ := List.mem_filter.mp hf
    obtain ⟨hne, hstdio⟩ := of_decide_eq_true hdec
    exact ⟨hne, hstdio, hload f hmem hne hstdio⟩

#print axioms filesOf_filter_visible
#print axioms inputsFor_filter_visible

end Symbolic.Proofs.Tests.Refinement.Cli
