/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Repr
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import Symbolic.Specifications.Refinement.Statement

/-!
# `RegularFileList` and `filesOf` Lookup Algebra

Defines `RegularFileList` for CLI directory file lists and reduces `filesOf` lookups on regular
file lists to right-biased folds over normalized paths (`filesOf_eq_optFold`,
`filesOf_append_of_regular`, `mem_of_filesOf_eq_some`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli

open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

/-- Directory names under which 2-segment files of `encodeDir`, `initDirs`, and `CliCall.extra` live. -/
def topFileDirs : List String :=
  ["identities", "sessions", "signed-pre-keys", "one-time-pre-keys",
   "one-time-kyber-pre-keys", "last-resort-kyber-pre-keys", "bundle"]

/-- Every file entry is visible (`normalizePath ≠ []`, not in `stdioPaths`), is not one of
`topFileDirs`, and has strict directory prefixes only inside `topFileDirs`. -/
def RegularFileList (files : List (String × HwBytes)) : Prop :=
  ∀ f ∈ files,
    Arm64.normalizePath f.1 ≠ [] ∧
    Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath ∧
    (∀ d ∈ topFileDirs, Arm64.normalizePath f.1 ≠ [d]) ∧
    (∀ pref ∈ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast,
      ∃ d ∈ topFileDirs, pref = [d])

theorem RegularFileList.append {l₁ l₂ : List (String × HwBytes)}
    (h₁ : RegularFileList l₁) (h₂ : RegularFileList l₂) : RegularFileList (l₁ ++ l₂) := by
  intro f hf; rcases List.mem_append.mp hf with h | h <;> [exact h₁ f h; exact h₂ f h]

set_option linter.auxLemma false in
private theorem splitSlash_go_cons_ne {c : Char} (cur rest : List Char) (hc : c ≠ '/') :
    Arm64.splitSlash.go cur (c :: rest) = Arm64.splitSlash.go (c :: cur) rest := by
  delta Arm64.splitSlash.go Arm64.splitSlash.go._f Arm64.splitSlash.go.match_1
  dsimp only [List.brecOn, List.brecOn.go, List.casesOn]
  split_ifs with h
  · exact absurd h hc
  · rfl

private theorem splitSlash_go_noSlash :
    ∀ (cs cur : List Char), '/' ∉ cs →
      Arm64.splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by rw [List.append_nil]; rfl
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.mem_cons_self ..)
    rw [splitSlash_go_cons_ne cur cs hc,
        splitSlash_go_noSlash cs (c :: cur) (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp [List.reverse_cons, List.append_assoc]

private theorem splitSlash_go_append_slash :
    ∀ (cs1 cur cs2 : List Char), '/' ∉ cs1 →
      Arm64.splitSlash.go cur (cs1 ++ '/' :: cs2) =
        String.ofList (cur.reverse ++ cs1) :: Arm64.splitSlash.go [] cs2
  | [], cur, cs2, _ => by rw [List.nil_append, List.append_nil]; rfl
  | c :: cs1, cur, cs2, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.mem_cons_self ..)
    rw [List.cons_append, splitSlash_go_cons_ne cur _ hc,
        splitSlash_go_append_slash cs1 (c :: cur) cs2 (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp [List.reverse_cons, List.append_assoc]

theorem normalizePath_two {d s : String}
    (hd_sl : '/' ∉ d.toList) (hd_emp : d.isEmpty = false) (hd_dot : (d != ".") = true)
    (hs_sl : '/' ∉ s.toList) (hs_emp : s.isEmpty = false) (hs_dot : (s != ".") = true) :
    Arm64.normalizePath (d ++ "/" ++ s) = [d, s] := by
  unfold Arm64.normalizePath Arm64.splitSlash
  have hcs : (d ++ "/" ++ s).toList = d.toList ++ '/' :: s.toList := by simp [String.toList_append]
  rw [hcs, splitSlash_go_append_slash d.toList [] s.toList hd_sl,
      splitSlash_go_noSlash s.toList [] hs_sl]
  simp [String.ofList_toList, hd_emp, hd_dot, hs_emp, hs_dot]

private theorem toDigitsCore_ne_nil :
    ∀ (fuel n : Nat) (acc : List Char), acc ≠ [] → Nat.toDigitsCore 10 fuel n acc ≠ []
  | 0, _, acc, h => by simpa [Nat.toDigitsCore] using h
  | fuel + 1, n, acc, _ => by
    unfold Nat.toDigitsCore; dsimp only; split_ifs
    · simp
    · exact toDigitsCore_ne_nil fuel (n / 10) (_ :: acc) (by simp)

theorem toString_nat_seg (n : Nat) :
    '/' ∉ (toString n).toList ∧ '.' ∉ (toString n).toList ∧
      (toString n).isEmpty = false ∧ (toString n != ".") = true := by
  have hsl : '/' ∉ (toString n).toList := by
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
    intro hm; have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hm; revert this; decide
  have hdot : '.' ∉ (toString n).toList := by
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
    intro hm; have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hm; revert this; decide
  have hne : (toString n).toList ≠ [] := by
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
    unfold Nat.toDigits Nat.toDigitsCore; dsimp only
    split_ifs <;> [simp; exact toDigitsCore_ne_nil _ _ _ (by simp)]
  have hemp : (toString n).isEmpty = false :=
    Bool.eq_false_iff.mpr fun he => hne (by rw [String.isEmpty_iff.mp he]; rfl)
  have hnd : (toString n != ".") = true := by
    rw [bne_iff_ne]; intro he; exact hdot (by rw [he]; decide)
  exact ⟨hsl, hdot, hemp, hnd⟩

theorem normalizePath_dir_nat_suf {d suf : String} (n : Nat)
    (hd_sl : '/' ∉ d.toList) (hd_emp : d.isEmpty = false) (hd_dot : (d != ".") = true)
    (hsuf_sl : '/' ∉ suf.toList) :
    Arm64.normalizePath (d ++ "/" ++ toString n ++ suf) = [d, toString n ++ suf] := by
  obtain ⟨hsl, hdot, hemp, _⟩ := toString_nat_seg n
  have hne_n : (toString n).toList ≠ [] := fun hn => by
    have : toString n = "" := by rw [← String.ofList_toList (s := toString n), hn]
    rw [this] at hemp; cases hemp
  have hcat : d ++ "/" ++ toString n ++ suf = d ++ "/" ++ (toString n ++ suf) := by
    simp [String.append_assoc]
  rw [hcat]
  refine normalizePath_two hd_sl hd_emp hd_dot ?_ ?_ ?_
  · rw [String.toList_append]; intro hm
    rcases List.mem_append.mp hm with h | h <;> [exact hsl h; exact hsuf_sl h]
  · exact Bool.eq_false_iff.mpr fun he => hne_n (by
      have := congrArg String.toList (String.isEmpty_iff.mp he)
      rw [String.toList_append] at this; exact (List.append_eq_nil_iff.mp this).1)
  · rw [bne_iff_ne]; intro he
    have h1 := congrArg String.toList he
    rw [String.toList_append] at h1
    have hmem : '.' ∈ (toString n).toList ++ suf.toList := by rw [h1]; decide
    rcases List.mem_append.mp hmem with h | h
    · exact hdot h
    · cases hs : suf.toList with
      | nil => rw [hs] at h; cases h
      | cons c cs =>
        have hlen := congrArg List.length h1
        have hdot_len : ("." : String).toList.length = 1 := by decide
        have hpos := List.length_pos_iff.mpr hne_n
        rw [List.length_append, hs, List.length_cons, hdot_len] at hlen; omega

theorem regularFile_two {p d s : String} {v : HwBytes}
    (hp : Arm64.normalizePath p = [d, s]) (hd : d ∈ topFileDirs) :
    RegularFileList [(p, v)] := by
  intro f hf; rw [List.mem_singleton] at hf; subst hf
  refine ⟨by simp [hp], ?_,
    fun d' _ h => by have := congrArg List.length (hp.symm.trans h); simp at this, ?_⟩
  · have hstd : stdioPaths.map Arm64.normalizePath = [["<stdin>"], ["<stdout>"], ["<stderr>"]] := by decide
    rw [hp, hstd]; simp
  · rw [hp]; intro pref hpref
    change pref ∈ [[d]] at hpref; rw [List.mem_singleton] at hpref; exact ⟨d, hd, hpref⟩

theorem regularFile_two' {p d : String} {v : HwBytes}
    (hlen : (Arm64.normalizePath p).length = 2)
    (hhd : (Arm64.normalizePath p).head? = some d) (hd : d ∈ topFileDirs) :
    RegularFileList [(p, v)] := by
  cases hn : Arm64.normalizePath p with
  | nil => simp [hn] at hlen
  | cons x xs =>
    cases xs with
    | nil => simp [hn] at hlen
    | cons y ys =>
      cases ys with
      | nil =>
        have hx : x = d := by simpa [hn] using hhd
        exact regularFile_two (hx ▸ hn) hd
      | cons _ _ => simp [hn] at hlen

theorem regularFile_root {p : String} {v : HwBytes}
    (hp : Arm64.normalizePath p = [p]) (_hne : p ≠ "")
    (hnstd : [p] ∉ stdioPaths.map Arm64.normalizePath) (hnd : p ∉ topFileDirs) :
    RegularFileList [(p, v)] := by
  intro f hf; rw [List.mem_singleton] at hf; subst hf
  refine ⟨by simp [hp], by simpa [hp] using hnstd,
    fun d hd h => hnd (by have := List.cons.inj (hp.symm.trans h); exact this.1 ▸ hd), ?_⟩
  rw [hp]; intro _ h; cases h

theorem regularFileList_encodeDir (W : PEParams) (st : PqParty) :
    RegularFileList (encodeDir W st) := by
  intro f hf; unfold encodeDir at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatten, or_assoc] at hf
  rcases hf with rfl | rfl | rfl | h | h | h | h | h | h
  · exact regularFile_root (by decide) (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · exact regularFile_root (by decide) (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · exact regularFile_root (by decide) (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · cases hp : st.peerId with
    | none => simp [hp] at h
    | some k =>
      simp only [hp, List.mem_singleton] at h; subst h
      cases st.party <;>
        exact regularFile_two' (d := "identities") (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · cases hs : st.session with
    | none => simp [hs] at h
    | some xg =>
      simp only [hs, List.mem_singleton] at h; subst h
      cases st.party <;>
        exact regularFile_two' (d := "sessions") (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    exact regularFile_two
      (by simpa [signedPreKeyFile] using normalizePath_dir_nat_suf (d := "signed-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide))
      (by decide) _ (List.mem_singleton.mpr rfl)
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    exact regularFile_two
      (by simpa [oneTimePreKeyFile] using normalizePath_dir_nat_suf (d := "one-time-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide))
      (by decide) _ (List.mem_singleton.mpr rfl)
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    exact regularFile_two
      (by simpa [oneTimeKyberPreKeyFile] using normalizePath_dir_nat_suf (d := "one-time-kyber-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide))
      (by decide) _ (List.mem_singleton.mpr rfl)
  · rcases h with ⟨l, ⟨⟨i, _, _⟩, _, rfl⟩, hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact regularFile_two
        (by simpa [lastResortKyberPreKeyFile] using normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide))
        (by decide) _ (List.mem_singleton.mpr rfl)
    · exact regularFile_two
        (by simpa [baseKeysFile] using normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := ".base-keys") i.toNat (by decide) (by decide) (by decide) (by decide))
        (by decide) _ (List.mem_singleton.mpr rfl)

theorem regularFileList_bundle_files (b : PublicBundle) :
    RegularFileList (b.files bundleDir) := by
  intro f hf; unfold PublicBundle.files at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl) | ho
  · exact regularFile_two' (d := "bundle") (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · exact regularFile_two' (d := "bundle") (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · exact regularFile_two' (d := "bundle") (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · exact regularFile_two' (d := "bundle") (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)
  · cases hot : b.oneTime with
    | none => simp [hot] at ho
    | some ik =>
      rcases ik with ⟨_, _⟩; simp only [hot, List.mem_singleton] at ho; subst ho
      exact regularFile_two' (d := "bundle") (by decide) (by decide) (by decide) _ (List.mem_singleton.mpr rfl)

private def fileOfEntry : Option Arm64.FsEntry → Option HwBytes
  | some (.file bs) => some bs | _ => none

private def filesFold (files : List (String × HwBytes)) (a : Arm64.FsState) : Arm64.FsState :=
  files.foldl (fun fs (p, bs) => (((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
    (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))) a

private theorem fileOfEntry_empty (q : Arm64.FsPath) : fileOfEntry (({} : Arm64.FsState).entries q) = none := by
  show fileOfEntry (if q.isEmpty then some .dir else none) = none; split <;> rfl

private theorem fileOfEntry_filesFold_dirOnly {files : List (String × HwBytes)} {q : Arm64.FsPath}
    (hreg : RegularFileList files) (hd : ∃ d ∈ topFileDirs, q = [d])
    (a : Arm64.FsState) (ha : fileOfEntry (a.entries q) = none) :
    fileOfEntry ((filesFold files a).entries q) = none := by
  rcases hd with ⟨d, hd_mem, rfl⟩
  induction files generalizing a with
  | nil => exact ha
  | cons f fs ih =>
    obtain ⟨_, _, hnd, _⟩ := hreg f (List.mem_cons_self ..)
    have hne : ([d] == Arm64.normalizePath f.1) = false := beq_false_of_ne (Ne.symm (hnd d hd_mem))
    apply ih (fun x hx => hreg x (List.mem_cons_of_mem _ hx))
    have hfold : fileOfEntry ((((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) a).entries [d]) = none := by
      clear ih hreg hnd hne
      induction (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast generalizing a with
      | nil => exact ha
      | cons x xs ih2 => apply ih2; simp only [Arm64.FsState.setEntry]; split <;> [rfl; exact ha]
    change fileOfEntry (if [d] == Arm64.normalizePath f.1 then some (.file f.2) else
      (((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) a).entries [d]) = none
    rw [hne]; exact hfold

private theorem fileOfEntry_filesFold_nonDir {files : List (String × HwBytes)} {q : Arm64.FsPath}
    (hreg : RegularFileList files) (hnd : ∀ d ∈ topFileDirs, q ≠ [d]) (a : Arm64.FsState) :
    fileOfEntry ((filesFold files a).entries q) =
      files.foldl (fun acc f => if q == Arm64.normalizePath f.1 then some f.2 else acc)
        (fileOfEntry (a.entries q)) := by
  induction files generalizing a with
  | nil => rfl
  | cons f fs ih =>
    obtain ⟨_, _, _, hpref⟩ := hreg f (List.mem_cons_self ..)
    have hreg' : RegularFileList fs := fun x hx => hreg x (List.mem_cons_of_mem _ hx)
    have hdir_eq : (((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) a).entries q = a.entries q := by
      clear ih hreg hreg'
      revert hpref
      generalize (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast = ps
      intro hpref
      induction ps generalizing a with
      | nil => rfl
      | cons x xs ih2 =>
        obtain ⟨d, hd, rfl⟩ := hpref x (List.mem_cons_self ..)
        rw [List.foldl_cons, ih2 _ (fun y hy => hpref y (List.mem_cons_of_mem _ hy))]
        simp [Arm64.FsState.setEntry, hnd d hd]
    let step := (((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) a).setFile f.1 (some (.file f.2))
    have hstep : fileOfEntry (step.entries q) =
        if q == Arm64.normalizePath f.1 then some f.2 else fileOfEntry (a.entries q) := by
      change fileOfEntry (if q == Arm64.normalizePath f.1 then some (.file f.2) else
        (((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath f.1)).dropLast).foldl
          (fun acc pref => acc.setEntry pref (some .dir)) a).entries q) = _
      rw [hdir_eq]; split <;> rfl
    simpa only [filesFold, List.foldl_cons, ← hstep] using ih hreg' step

private theorem optFold_or (files : List (String × HwBytes)) (q : Arm64.FsPath) (init : Option HwBytes) :
    files.foldl (fun acc f => if q == Arm64.normalizePath f.1 then some f.2 else acc) init =
      (files.foldl (fun acc f => if q == Arm64.normalizePath f.1 then some f.2 else acc) none).or init := by
  induction files generalizing init with
  | nil => simp
  | cons f fs ih =>
    simp only [List.foldl_cons]
    cases heq : q == Arm64.normalizePath f.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ih init
    · rw [ih (some f.2), Option.or_assoc]; simp

theorem filesOf_eq_optFold {files : List (String × HwBytes)} (hreg : RegularFileList files) (p : String) :
    filesOf files p =
      files.foldl (fun acc f => if Arm64.normalizePath p == Arm64.normalizePath f.1 then some f.2 else acc) none := by
  unfold filesOf fsView
  by_cases hstd : Arm64.normalizePath p ∈ stdioPaths.map Arm64.normalizePath
  · simp only [hstd, ↓reduceIte]; symm
    have hall : ∀ f ∈ files, (Arm64.normalizePath p == Arm64.normalizePath f.1) = false :=
      fun f hf => beq_false_of_ne fun he => (hreg f hf).2.1 (he ▸ hstd)
    induction files with
    | nil => rfl
    | cons f fs ih =>
      simp only [List.foldl_cons, hall f (List.mem_cons_self ..), Bool.false_eq_true, ↓reduceIte]
      exact ih (fun x hx => hreg x (List.mem_cons_of_mem _ hx))
        (fun x hx => hall x (List.mem_cons_of_mem _ hx))
  · simp only [hstd, ↓reduceIte, Arm64.FsState.files, Arm64.FsState.getEntry]
    by_cases hemp : (Arm64.normalizePath p).isEmpty = true
    · simp only [hemp, ↓reduceIte]; symm
      have hnil : Arm64.normalizePath p = [] := List.isEmpty_iff.mp hemp
      have hall : ∀ f ∈ files, (Arm64.normalizePath p == Arm64.normalizePath f.1) = false :=
        fun f hf => beq_false_of_ne fun he => (hreg f hf).1 (he ▸ hnil)
      induction files with
      | nil => rfl
      | cons f fs ih =>
        simp only [List.foldl_cons, hall f (List.mem_cons_self ..), Bool.false_eq_true, ↓reduceIte]
        exact ih (fun x hx => hreg x (List.mem_cons_of_mem _ hx))
          (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      change fileOfEntry ((filesFold files {}).entries (Arm64.normalizePath p)) = _
      by_cases hd : ∃ d ∈ topFileDirs, Arm64.normalizePath p = [d]
      · rw [fileOfEntry_filesFold_dirOnly hreg hd _ (fileOfEntry_empty _)]
        rcases hd with ⟨d, hd_mem, hpd⟩; symm
        have hall : ∀ f ∈ files, (Arm64.normalizePath p == Arm64.normalizePath f.1) = false :=
          fun f hf => beq_false_of_ne fun he => (hreg f hf).2.2.1 d hd_mem (he.symm.trans hpd)
        induction files with
        | nil => rfl
        | cons f fs ih =>
          simp only [List.foldl_cons, hall f (List.mem_cons_self ..), Bool.false_eq_true, ↓reduceIte]
          exact ih (fun x hx => hreg x (List.mem_cons_of_mem _ hx))
            (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      · have hd' : ∀ d ∈ topFileDirs, Arm64.normalizePath p ≠ [d] := fun d h1 h2 => hd ⟨d, h1, h2⟩
        rw [fileOfEntry_filesFold_nonDir hreg hd', fileOfEntry_empty _]

theorem filesOf_append_of_regular {l₁ l₂ : List (String × HwBytes)}
    (h₁ : RegularFileList l₁) (h₂ : RegularFileList l₂) (p : String) :
    filesOf (l₁ ++ l₂) p = (filesOf l₂ p).or (filesOf l₁ p) := by
  rw [filesOf_eq_optFold (h₁.append h₂), filesOf_eq_optFold h₁, filesOf_eq_optFold h₂,
      List.foldl_append, optFold_or]

theorem mem_of_filesOf_eq_some {files : List (String × HwBytes)} {p : String} {b : HwBytes}
    (hreg : RegularFileList files) (h : filesOf files p = some b) :
    ∃ f ∈ files, Arm64.normalizePath f.1 = Arm64.normalizePath p ∧ f.2 = b := by
  rw [filesOf_eq_optFold hreg] at h
  suffices ∀ init, files.foldl (fun acc f =>
      if Arm64.normalizePath p == Arm64.normalizePath f.1 then some f.2 else acc) init = some b →
      init = some b ∨ ∃ f ∈ files, Arm64.normalizePath f.1 = Arm64.normalizePath p ∧ f.2 = b from
    (this none h).resolve_left (by simp)
  clear hreg h
  induction files with
  | nil => intro init h; exact Or.inl h
  | cons f fs ih =>
    intro init h; simp only [List.foldl_cons] at h
    rcases ih _ h with hinit | ⟨g, hg, hp, hb⟩
    · by_cases heq : (Arm64.normalizePath p == Arm64.normalizePath f.1) = true
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hinit
        exact Or.inr ⟨f, List.mem_cons_self .., (beq_iff_eq.mp heq).symm, hinit⟩
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hinit; exact Or.inl hinit
    · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, hp, hb⟩

end Symbolic.Swarm.CREF.Cli
