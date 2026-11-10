/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.Run

@[expose] public section

set_option autoImplicit false

/-!
# Pure `FsState` Fold Lemmas for `Process.initFsState`

Defines `fileOfEntry`, `SameFiles`, `filesFold`, `dirsFold`, and `NoFiles`, and proves
`SameFiles.setEntry`, `NoFiles.base`, `initFsState_entries`, and fold congruence lemmas.
-/

namespace CryptoVerification.SignalSession

open Arm64
/-- The regular-file content of an entry. -/
def fileOfEntry : Option FsEntry → Option (List (BitVec 8))
  | some (.file bs) => some bs
  | _ => none

/-- Two file systems hold the same regular files at every key. -/
def SameFiles (a b : FsState) : Prop := ∀ q, fileOfEntry (a.entries q) = fileOfEntry (b.entries q)

theorem SameFiles.setEntry {a b : FsState} (h : SameFiles a b) (p : FsPath) (e : Option FsEntry) :
    SameFiles (a.setEntry p e) (b.setEntry p e) := by
  intro q
  simp only [FsState.setEntry]
  split
  · rfl
  · exact h q

/-- The loader's files fold (`Process.initFsState`). -/
def filesFold (files : List (String × List (BitVec 8))) (a : FsState) : FsState :=
  files.foldl (fun fs (p, bs) =>
    (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))) a

/-- The loader's directories fold (`Process.initFsState`). -/
def dirsFold (dirs : List String) (a : FsState) : FsState :=
  dirs.foldl (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
    (fun acc pref => acc.setEntry pref (some .dir)) fs) a

/-- A file system that holds no regular file (only directories). -/
def NoFiles (a : FsState) : Prop := ∀ q, fileOfEntry (a.entries q) = none

theorem NoFiles.base : NoFiles ({} : FsState) := by
  intro q
  change fileOfEntry (if q.isEmpty then some .dir else none) = none
  split <;> rfl

/-- The loaded file system is the files fold over the directories fold. -/
theorem initFsState_entries (i : Process.ProcessInputs) (q : FsPath)
    (_hq : q ∉ stdioPaths.map normalizePath) :
    (Process.initFsState i).entries q = (filesFold i.files (dirsFold i.dirs {})).entries q := by
  rfl


/-! ## Fold Congruence Lemmas -/

section MoveCompat
private theorem SameFiles.foldl_dir {a b : FsState} (h : SameFiles a b) (l : List FsPath) :
    SameFiles (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) a)
      (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) b) := by
  induction l generalizing a b with
  | nil => exact h
  | cons x xs ih => exact ih (h.setEntry _ _)

theorem SameFiles.filesFold_same {a b : FsState} (h : SameFiles a b)
    (l : List (String × List (BitVec 8))) : SameFiles (filesFold l a) (filesFold l b) := by
  induction l generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    obtain ⟨p, bs⟩ := x
    exact ih ((h.foldl_dir _).setEntry _ _)

end MoveCompat

end CryptoVerification.SignalSession
