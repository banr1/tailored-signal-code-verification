/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs
import all Init.Data.Repr

/-!
# Path Sets, `filesOf` Folds, and `scrub` Lemmas for Alice's `init` Directory

Partitions Alice's persistent and transient `init` file paths, characterizes
`filesOf` as an option fold on `AlicePathList`, and evaluates `scrub` on each
path class.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession

/-! ## Path sets for Alice's directory and `init` inputs -/

/-- Parent directories of all 2-segment files in Alice's directory and `init` bundle files. -/
def aliceTopDirs : List String := ["identities", "sessions", "bundle"]

/-- Persistent paths of Alice's directory (`commonFiles` and optional session file). -/
def aliceKeepPaths : List String :=
  [addressFile, identityKeyPairFile, registrationIdFile,
   identityFile bobUuid, sessionFile ⟨bobUuid, 1⟩]

/-- Transient paths added by `init` (`coins` and `bundle/*`), removed by `scrub`. -/
def aliceScrubPaths : List String :=
  [coinsFile,
   bundleDir ++ "/identity-key",
   bundleDir ++ "/registration-id",
   bundleDir ++ "/signed-pre-key",
   bundleDir ++ "/kyber-pre-key",
   bundleDir ++ "/one-time-pre-key"]

/-- All 11 file paths appearing in Alice's `encodeDir`, `PublicBundle.files bundleDir`, and `coins`. -/
def aliceAllPaths : List String := aliceKeepPaths ++ aliceScrubPaths

/-- Every file entry in `files` uses one of the 11 canonical Alice/bundle/coins paths. -/
def AlicePathList (files : List (String × HwBytes)) : Prop :=
  ∀ f ∈ files, f.1 ∈ aliceAllPaths

theorem AlicePathList.append {l₁ l₂ : List (String × HwBytes)}
    (h₁ : AlicePathList l₁) (h₂ : AlicePathList l₂) : AlicePathList (l₁ ++ l₂) := by
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact h₁ f h
  · exact h₂ f h

private theorem aliceAllPaths_nonEmpty {s : String} (hs : s ∈ aliceAllPaths) :
    Arm64.normalizePath s ≠ [] := by
  simp only [aliceAllPaths, aliceKeepPaths, aliceScrubPaths, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem aliceAllPaths_not_stdio {s : String} (hs : s ∈ aliceAllPaths) :
    Arm64.normalizePath s ∉ stdioPaths.map Arm64.normalizePath := by
  simp only [aliceAllPaths, aliceKeepPaths, aliceScrubPaths, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem aliceAllPaths_not_topDir {s : String} (hs : s ∈ aliceAllPaths) :
    ∀ d ∈ aliceTopDirs, Arm64.normalizePath s ≠ [d] := by
  simp only [aliceAllPaths, aliceKeepPaths, aliceScrubPaths, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem aliceAllPaths_prefixes {s : String} (hs : s ∈ aliceAllPaths) :
    ∀ pref ∈ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath s)).dropLast,
      ∃ d ∈ aliceTopDirs, pref = [d] := by
  simp only [aliceAllPaths, aliceKeepPaths, aliceScrubPaths, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

/-! ## Fold characterization of `filesOf` on `AlicePathList` -/

private def fileOfEntry : Option Arm64.FsEntry → Option HwBytes
  | some (.file bs) => some bs
  | _ => none

private def filesFold (files : List (String × HwBytes)) (a : Arm64.FsState) : Arm64.FsState :=
  files.foldl (fun fs (p, bs) =>
    (((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))) a

private theorem fileOfEntry_empty_fs (q : Arm64.FsPath) :
    fileOfEntry (({} : Arm64.FsState).entries q) = none := by
  show fileOfEntry (if q.isEmpty then some .dir else none) = none
  split <;> rfl

private theorem initFsState_files_entries (files : List (String × HwBytes)) (q : Arm64.FsPath) :
    (Arm64.Process.initFsState { files := files }).entries q =
      (filesFold files {}).entries q :=
  rfl

private theorem foldl_setDir_noFile (l : List Arm64.FsPath) (q : Arm64.FsPath)
    (a : Arm64.FsState) (ha : fileOfEntry (a.entries q) = none) :
    fileOfEntry
      ((l.foldl (fun acc pref => acc.setEntry pref (some .dir)) a).entries q) = none := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih
    simp only [Arm64.FsState.setEntry]
    split <;> [rfl; exact ha]

private theorem foldl_setDir_other (l : List Arm64.FsPath) (q : Arm64.FsPath)
    (hpref : ∀ pref ∈ l, ∃ d ∈ aliceTopDirs, pref = [d])
    (hnd : ∀ d ∈ aliceTopDirs, q ≠ [d]) (a : Arm64.FsState) :
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) a).entries q = a.entries q := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨d, hd, rfl⟩ := hpref x (List.mem_cons_self ..)
    have hne : (q == [d]) = false := beq_false_of_ne (hnd d hd)
    rw [List.foldl_cons, ih (fun y hy => hpref y (List.mem_cons_of_mem _ hy))]
    unfold Arm64.FsState.setEntry
    dsimp only
    rw [hne]
    rfl

private theorem fileOfEntry_filesFold_topDir {files : List (String × HwBytes)} {q : Arm64.FsPath}
    (hal : AlicePathList files) (hd : ∃ d ∈ aliceTopDirs, q = [d])
    (a : Arm64.FsState) (ha : fileOfEntry (a.entries q) = none) :
    fileOfEntry ((filesFold files a).entries q) = none := by
  rcases hd with ⟨d, hd_mem, rfl⟩
  induction files generalizing a with
  | nil => exact ha
  | cons f fs ih =>
    have hf := hal f (List.mem_cons_self ..)
    have hne : ([d] == Arm64.normalizePath f.1) = false :=
      beq_false_of_ne (Ne.symm (aliceAllPaths_not_topDir hf d hd_mem))
    apply ih (fun x hx => hal x (List.mem_cons_of_mem _ hx))
    have hfold := foldl_setDir_noFile
      ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast) [d] a ha
    unfold Arm64.FsState.setFile Arm64.FsState.setEntry
    dsimp only
    rw [hne]
    exact hfold

private theorem fileOfEntry_filesFold_nonTopDir {files : List (String × HwBytes)} {q : Arm64.FsPath}
    (hal : AlicePathList files) (hnd : ∀ d ∈ aliceTopDirs, q ≠ [d]) (a : Arm64.FsState) :
    fileOfEntry ((filesFold files a).entries q) =
      files.foldl (fun acc f => if q == Arm64.normalizePath f.1 then some f.2 else acc)
        (fileOfEntry (a.entries q)) := by
  induction files generalizing a with
  | nil => rfl
  | cons f fs ih =>
    have hpref := aliceAllPaths_prefixes (hal f (List.mem_cons_self ..))
    have hal' : AlicePathList fs := fun x hx => hal x (List.mem_cons_of_mem _ hx)
    let anc := ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) a
    have hdir_eq : anc.entries q = a.entries q := foldl_setDir_other _ q hpref hnd a
    let step := anc.setFile f.1 (some (.file f.2))
    have hstep : fileOfEntry (step.entries q) =
        if q == Arm64.normalizePath f.1 then some f.2 else fileOfEntry (a.entries q) := by
      dsimp only [step]
      unfold Arm64.FsState.setFile Arm64.FsState.setEntry
      dsimp only
      rw [hdir_eq]
      split <;> rfl
    simpa only [filesFold, List.foldl_cons, ← hstep] using ih hal' step

private theorem optFold_or (files : List (String × HwBytes)) (p : String) (init : Option HwBytes) :
    files.foldl (fun acc f => if SamePath p f.1 then some f.2 else acc) init =
      (files.foldl (fun acc f => if SamePath p f.1 then some f.2 else acc) none).or init := by
  induction files generalizing init with
  | nil => simp
  | cons f fs ih =>
    simp only [List.foldl_cons]
    cases SamePath p f.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih init
    · simp only [↓reduceIte]
      rw [ih (some f.2), Option.or_assoc]
      simp

theorem foldl_false_eq_none (files : List (String × HwBytes)) (p : String)
    (hall : ∀ f ∈ files, SamePath p f.1 = false) :
    files.foldl (fun acc f => if SamePath p f.1 then some f.2 else acc) none = none := by
  induction files with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.foldl_cons, hall f (List.mem_cons_self ..), Bool.false_eq_true, ↓reduceIte]
    exact ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))

theorem filesOf_eq_optFold {files : List (String × HwBytes)}
    (hal : AlicePathList files) (p : String) :
    filesOf files p =
      files.foldl (fun acc f => if SamePath p f.1 then some f.2 else acc) none := by
  unfold filesOf fsView
  by_cases hstd : Arm64.normalizePath p ∈ stdioPaths.map Arm64.normalizePath
  · simp only [hstd, ↓reduceIte]
    symm
    refine foldl_false_eq_none files p fun f hf => ?_
    unfold SamePath
    exact beq_false_of_ne fun he => aliceAllPaths_not_stdio (hal f hf) (he ▸ hstd)
  · simp only [hstd, ↓reduceIte, Arm64.FsState.files, Arm64.FsState.getEntry]
    by_cases hemp : (Arm64.normalizePath p).isEmpty = true
    · simp only [hemp, ↓reduceIte]
      have hnil : Arm64.normalizePath p = [] := List.isEmpty_iff.mp hemp
      symm
      refine foldl_false_eq_none files p fun f hf => ?_
      unfold SamePath
      exact beq_false_of_ne fun he => aliceAllPaths_nonEmpty (hal f hf) (he.symm.trans hnil)
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      change fileOfEntry ((Arm64.Process.initFsState { files := files }).entries (Arm64.normalizePath p)) = _
      rw [initFsState_files_entries files _]
      by_cases hd : ∃ d ∈ aliceTopDirs, Arm64.normalizePath p = [d]
      · rw [fileOfEntry_filesFold_topDir hal hd _ (fileOfEntry_empty_fs _)]
        rcases hd with ⟨d, hd_mem, hpd⟩
        symm
        refine foldl_false_eq_none files p fun f hf => ?_
        unfold SamePath
        exact beq_false_of_ne fun he => aliceAllPaths_not_topDir (hal f hf) d hd_mem (he.symm.trans hpd)
      · have hnd : ∀ d ∈ aliceTopDirs, Arm64.normalizePath p ≠ [d] :=
          fun d hd_mem he => hd ⟨d, hd_mem, he⟩
        rw [fileOfEntry_filesFold_nonTopDir hal hnd, fileOfEntry_empty_fs _]
        rfl

theorem filesOf_append_of_alicePaths {l₁ l₂ : List (String × HwBytes)}
    (h₁ : AlicePathList l₁) (h₂ : AlicePathList l₂) (p : String) :
    filesOf (l₁ ++ l₂) p = (filesOf l₂ p).or (filesOf l₁ p) := by
  rw [filesOf_eq_optFold (h₁.append h₂), filesOf_eq_optFold h₁, filesOf_eq_optFold h₂,
      List.foldl_append, optFold_or]

/-! ## `AlicePathList` membership and `scrub` evaluation -/

theorem sessionPathOf_alice_eq (r : ProtocolSetup) :
    sessionPathOf r r.alice = sessionFile ⟨bobUuid, 1⟩ := by
  simp [sessionPathOf, peerOf, peerNameOf]

theorem aliceKeep_commonFiles (interp : ExternInterpretation) (r : ProtocolSetup) :
    ∀ f ∈ commonFiles interp r r.alice, f.1 ∈ aliceKeepPaths := by
  intro f hf
  unfold commonFiles at hf
  simp only [peerNameOf, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> simp [aliceKeepPaths]

theorem alicePathList_commonFiles (interp : ExternInterpretation) (r : ProtocolSetup) :
    AlicePathList (commonFiles interp r r.alice) :=
  fun f hf => List.mem_append_left _ (aliceKeep_commonFiles interp r f hf)

theorem aliceKeep_encodeDir {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {st : PqParty} (halice : AlicePqParty interp r st) :
    ∀ f ∈ encodeDir P st, f.1 ∈ aliceKeepPaths := by
  rw [encodeDir_of_alicePqParty hagree hEq hwf halice]
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact aliceKeep_commonFiles interp r f h
  · cases hs : st.session with
    | none => simp [hs] at h
    | some xg =>
      simp only [hs, List.mem_singleton] at h
      subst h
      simp [sessionPathOf_alice_eq, aliceKeepPaths]

theorem alicePathList_encodeDir {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {st : PqParty} (halice : AlicePqParty interp r st) :
    AlicePathList (encodeDir P st) :=
  fun f hf => List.mem_append_left _ (aliceKeep_encodeDir hagree hEq hwf halice f hf)

theorem aliceScrub_bundle_files (b : PublicBundle) :
    ∀ f ∈ b.files bundleDir, f.1 ∈ aliceScrubPaths := by
  intro f hf
  unfold PublicBundle.files at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl) | ho
  · simp [aliceScrubPaths]
  · simp [aliceScrubPaths]
  · simp [aliceScrubPaths]
  · simp [aliceScrubPaths]
  · cases hot : b.oneTime with
    | none => simp [hot] at ho
    | some ik =>
      rcases ik with ⟨_, _⟩
      simp only [hot, List.mem_singleton] at ho
      subst ho
      simp [aliceScrubPaths]

theorem aliceScrub_bundle_coins (b : PublicBundle) (coins : HwBytes) :
    ∀ f ∈ b.files bundleDir ++ [(coinsFile, coins)], f.1 ∈ aliceScrubPaths := by
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact aliceScrub_bundle_files b f h
  · rw [List.mem_singleton] at h; subst h; simp [aliceScrubPaths]

theorem alicePathList_bundle_coins (b : PublicBundle) (coins : HwBytes) :
    AlicePathList (b.files bundleDir ++ [(coinsFile, coins)]) :=
  fun f hf => List.mem_append_right _ (aliceScrub_bundle_coins b coins f hf)

theorem pqInitInputs_files_eq (P : PEParams) (st : PqParty) (bE : PreKeyBundleFields)
    (tVec : List.Vector (BitVec 8) initiateTapeLen) :
    (pqInitInputs P st bE tVec).files =
      encodeDir P st ++ ((publicBundleOf bE).files bundleDir ++ [(coinsFile, tVec.toList)]) := by
  simp [pqInitInputs, pqInputs, List.append_assoc]

private def isScrubbedPath (p : String) : Bool :=
  SamePath p coinsFile || (Arm64.normalizePath p).head? == some bundleDir

private theorem isScrubbedPath_of_samePath {p q : String} (h : SamePath p q = true) :
    isScrubbedPath p = isScrubbedPath q := by
  unfold SamePath at h
  have hnorm : Arm64.normalizePath p = Arm64.normalizePath q := beq_iff_eq.mp h
  unfold isScrubbedPath SamePath
  rw [hnorm]

private theorem isScrubbedPath_keep {s : String} (hs : s ∈ aliceKeepPaths) :
    isScrubbedPath s = false := by
  simp only [aliceKeepPaths, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem isScrubbedPath_scrub {s : String} (hs : s ∈ aliceScrubPaths) :
    isScrubbedPath s = true := by
  simp only [aliceScrubPaths, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem scrub_or (d₁ d₂ : DirectorySnapshot) :
    scrub (fun p => (d₂ p).or (d₁ p)) = fun p => (scrub d₂ p).or (scrub d₁ p) := by
  funext p
  unfold scrub
  split <;> simp

theorem scrub_filesOf_keep {files : List (String × HwBytes)}
    (hkeep : ∀ f ∈ files, f.1 ∈ aliceKeepPaths) :
    scrub (filesOf files) = filesOf files := by
  have hal : AlicePathList files := fun f hf => List.mem_append_left _ (hkeep f hf)
  funext p
  unfold scrub
  change (if isScrubbedPath p then none else filesOf files p) = filesOf files p
  split
  · rename_i hsc
    rw [filesOf_eq_optFold hal]
    symm
    refine foldl_false_eq_none files p fun f hf => ?_
    cases hsp : SamePath p f.1
    · rfl
    · have := isScrubbedPath_of_samePath hsp
      rw [hsc, isScrubbedPath_keep (hkeep f hf)] at this
      cases this
  · rfl

theorem scrub_filesOf_scrub {files : List (String × HwBytes)}
    (hscr : ∀ f ∈ files, f.1 ∈ aliceScrubPaths) :
    scrub (filesOf files) = fun _ => none := by
  have hal : AlicePathList files := fun f hf => List.mem_append_right _ (hscr f hf)
  funext p
  unfold scrub
  change (if isScrubbedPath p then none else filesOf files p) = none
  split
  · rfl
  · rename_i hnsc
    rw [filesOf_eq_optFold hal]
    refine foldl_false_eq_none files p fun f hf => ?_
    cases hsp : SamePath p f.1
    · rfl
    · exfalso
      apply hnsc
      rw [isScrubbedPath_of_samePath hsp]
      exact isScrubbedPath_scrub (hscr f hf)

end Symbolic.Swarm.CREF.Cli.Slots
