/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Specifications.SignalSession.SmScheme
import all Init.Data.List.SplitOn.Basic
import all Init.Data.Repr
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run

@[expose] public section

set_option autoImplicit false

/-!
# `WriteOk` and `CoinsReadable` for Game-Constructed Inputs

Proves that every write committed by the SM and PQXDH games (`smWrites`, `encodeDir`) satisfies
`WriteOk`, and every game input satisfies `CoinsReadable` and `InputsLoadable`.
-/

namespace CryptoVerification.SignalSession.Cli

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-! ## Pure `List Char` splitting helpers for 2-segment pre-key paths -/

private theorem splitOnPPrepend_slash_no_slash : ∀ (cs acc : List Char), '/' ∉ cs →
    List.splitOnPPrepend (· == '/') cs acc = [acc.reverse ++ cs]
  | [], acc, _ => by simp [List.splitOnPPrepend]
  | c :: cs, acc, h => by
    have hc : (c == '/') = false := beq_false_of_ne (fun he => h (he ▸ List.Mem.head _))
    have ih := splitOnPPrepend_slash_no_slash cs (c :: acc) (fun hm => h (List.Mem.tail _ hm))
    simp only [List.splitOnPPrepend, hc, Bool.false_eq_true, ↓reduceIte, ih,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem splitOnPPrepend_slash_two : ∀ (cs1 cs2 acc : List Char), '/' ∉ cs1 → '/' ∉ cs2 →
    List.splitOnPPrepend (· == '/') (cs1 ++ ('/' :: cs2)) acc = [acc.reverse ++ cs1, cs2]
  | [], cs2, acc, _, h2 => by
    have ih := splitOnPPrepend_slash_no_slash cs2 [] h2
    simp only [List.reverse_nil, List.nil_append] at ih
    simp only [List.nil_append, List.splitOnPPrepend, beq_self_eq_true, ↓reduceIte, ih,
      List.append_nil]
  | c :: cs1, cs2, acc, h1, h2 => by
    have hc : (c == '/') = false := beq_false_of_ne (fun he => h1 (he ▸ List.Mem.head _))
    have ih := splitOnPPrepend_slash_two cs1 cs2 (c :: acc) (fun hm => h1 (List.Mem.tail _ hm)) h2
    simp only [List.cons_append, List.splitOnPPrepend, hc, Bool.false_eq_true, ↓reduceIte, ih,
      List.reverse_cons, List.append_assoc, List.nil_append]

private theorem splitOn_slash_two (cs1 cs2 : List Char) (h1 : '/' ∉ cs1) (h2 : '/' ∉ cs2) :
    (cs1 ++ ('/' :: cs2)).splitOn '/' = [cs1, cs2] := by
  unfold List.splitOn List.splitOnP
  simpa using splitOnPPrepend_slash_two cs1 cs2 [] h1 h2

private theorem splitSlash_go_no_slash : ∀ (cs cur : List Char), '/' ∉ cs →
    splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by simp [splitSlash.go]
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.Mem.head _)
    have ih := splitSlash_go_no_slash cs (c :: cur) (fun hm => h (List.Mem.tail _ hm))
    have hstep : splitSlash.go cur (c :: cs) = splitSlash.go (c :: cur) cs := by
      rw [splitSlash.go.eq_def]
      split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq
        injection heq with h1 h2
        subst h1 h2
        rfl
    rw [hstep, ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem splitSlash_go_two : ∀ (cs1 : List Char) (cs2 cur : List Char),
    '/' ∉ cs1 → '/' ∉ cs2 →
    splitSlash.go cur (cs1 ++ ('/' :: cs2)) =
      [String.ofList (cur.reverse ++ cs1), String.ofList cs2]
  | [], cs2, cur, _, h2 => by
    have ih := splitSlash_go_no_slash cs2 [] h2
    simp [splitSlash.go, ih]
  | c :: cs1, cs2, cur, h1, h2 => by
    have hc : c ≠ '/' := fun he => h1 (he ▸ List.Mem.head _)
    have ih := splitSlash_go_two cs1 cs2 (c :: cur) (fun hm => h1 (List.Mem.tail _ hm)) h2
    have hstep : splitSlash.go cur (c :: (cs1 ++ '/' :: cs2)) =
        splitSlash.go (c :: cur) (cs1 ++ '/' :: cs2) := by
      rw [splitSlash.go.eq_def]
      split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq
        injection heq with h1' h2'
        subst h1' h2'
        rfl
    simpa [List.cons_append, List.reverse_cons, List.append_assoc] using hstep.trans ih

private theorem toDigitsCore_nonempty : ∀ (fuel n : Nat) (ds : List Char),
    ds ≠ [] → Nat.toDigitsCore 10 fuel n ds ≠ []
  | 0, _, ds, h => h
  | fuel + 1, n, ds, _ => by
    unfold Nat.toDigitsCore
    dsimp only
    split
    · simp
    · exact toDigitsCore_nonempty fuel (n / 10) _ (by simp)

private theorem toString_nat_toList_nonempty (n : Nat) : (toString n).toList ≠ [] := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  unfold Nat.toDigits Nat.toDigitsCore
  dsimp only
  split
  · simp
  · exact toDigitsCore_nonempty n (n / 10) _ (by simp)

private theorem toString_nat_mem_digit {n : Nat} {c : Char} (hc : c ∈ (toString n).toList) :
    Char.isDigit c = true := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

private theorem char_of_isDigit (c : Char) (h : Char.isDigit c = true) :
    c ≠ '/' ∧ c ≠ '\x00' ∧ c ≠ '.' ∧ c ≠ '<' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro rfl <;> cases h

private theorem twoSeg_props (d suf : String)
    (hd_noslash : '/' ∉ d.toList)
    (hd_ok : isUnmodelledPathComponent d.toList = false ∧ '\x00' ∉ d.toList ∧
      d ≠ "<stdin>" ∧ d ≠ "<stdout>" ∧ d ≠ "<stderr>")
    (hd_norm : (!d.isEmpty && d != ".") = true)
    (hs_noslash : '/' ∉ suf.toList)
    (hs_nonul : '\x00' ∉ suf.toList)
    (hs_head : ∃ c cs, suf.toList = c :: cs ∧ Char.isDigit c = true) :
    let p := (d ++ "/") ++ suf
    PathOk p = true ∧
    normalizePath p = [d, suf] ∧
    ancestors p = [d] ∧
    (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast = [[d]] := by
  obtain ⟨c, cs, hsuf, hdig⟩ := hs_head
  obtain ⟨_, _, hnotdot, hnotlt⟩ := char_of_isDigit c hdig
  have hplist : ((d ++ "/") ++ suf).toList = d.toList ++ ('/' :: suf.toList) := by
    rw [String.toList_append, String.toList_append]
    have hslash : "/".toList = ['/'] := by decide
    rw [hslash, List.append_assoc]
    rfl
  have hcomps : pathComps ((d ++ "/") ++ suf) = [d.toList, suf.toList] := by
    unfold pathComps
    rw [hplist]
    exact splitOn_slash_two d.toList suf.toList hd_noslash hs_noslash
  have hsplit : splitSlash ((d ++ "/") ++ suf) = [d, suf] := by
    unfold splitSlash
    rw [hplist, splitSlash_go_two d.toList suf.toList [] hd_noslash hs_noslash]
    simp [String.ofList_toList]
  have hsuf_not_empty : suf.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    have : suf.toList = [] := by
      have h1 : suf = "" := by simpa [String.isEmpty_iff] using he
      subst h1; decide
    rw [hsuf] at this
    cases this
  have hsuf_not_dot : (suf != ".") = true := by
    rw [bne_iff_ne]
    intro he
    subst he
    have hdot : ".".toList = ['.'] := by decide
    rw [hdot] at hsuf
    injection hsuf with h1 _
    exact hnotdot h1.symm
  have hsuf_bad : isUnmodelledPathComponent suf.toList = false := by
    rw [hsuf]
    unfold isUnmodelledPathComponent
    simp [hnotdot]
  have hs_nstdin : suf ≠ "<stdin>" := by
    intro he; subst he
    have h0 : "<stdin>".toList = '<' :: "stdin>".toList := by decide
    rw [h0] at hsuf; injection hsuf with h1 _; exact hnotlt h1.symm
  have hs_nstdout : suf ≠ "<stdout>" := by
    intro he; subst he
    have h0 : "<stdout>".toList = '<' :: "stdout>".toList := by decide
    rw [h0] at hsuf; injection hsuf with h1 _; exact hnotlt h1.symm
  have hs_nstderr : suf ≠ "<stderr>" := by
    intro he; subst he
    have h0 : "<stderr>".toList = '<' :: "stderr>".toList := by decide
    rw [h0] at hsuf; injection hsuf with h1 _; exact hnotlt h1.symm
  have hnorm : normalizePath ((d ++ "/") ++ suf) = [d, suf] := by
    unfold normalizePath
    rw [hsplit]
    simp [hd_norm, hsuf_not_empty, hsuf_not_dot]
  refine ⟨?_, hnorm, ?_, ?_⟩
  · unfold PathOk
    rw [hcomps]
    simp [String.ofList_toList, hsuf_bad, stdioPaths]
    exact ⟨⟨⟨hd_ok.1, hd_ok.2.1⟩, hd_ok.2.2.1, hd_ok.2.2.2.1, hd_ok.2.2.2.2⟩,
      hs_nonul, hs_nstdin, hs_nstdout, hs_nstderr⟩
  · unfold ancestors
    rw [hcomps]
    simp [List.range_succ, List.intercalate, String.ofList_toList]
  · rw [hnorm]
    rfl

private theorem prekey_nat_props (d : String) (n : Nat)
    (hd_noslash : '/' ∉ d.toList)
    (hd_ok : isUnmodelledPathComponent d.toList = false ∧ '\x00' ∉ d.toList ∧
      d ≠ "<stdin>" ∧ d ≠ "<stdout>" ∧ d ≠ "<stderr>")
    (hd_norm : (!d.isEmpty && d != ".") = true) :
    let p := (d ++ "/") ++ toString n
    PathOk p = true ∧
    normalizePath p = [d, toString n] ∧
    ancestors p = [d] ∧
    (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast = [[d]] := by
  apply twoSeg_props d (toString n) hd_noslash hd_ok hd_norm
  · intro hm; exact (char_of_isDigit _ (toString_nat_mem_digit hm)).1 rfl
  · intro hm; exact (char_of_isDigit _ (toString_nat_mem_digit hm)).2.1 rfl
  · cases hl : (toString n).toList with
    | nil => exact absurd hl (toString_nat_toList_nonempty n)
    | cons c cs =>
      exact ⟨c, cs, rfl, toString_nat_mem_digit (hl ▸ List.Mem.head _)⟩

private theorem basekeys_nat_props (d : String) (n : Nat)
    (hd_noslash : '/' ∉ d.toList)
    (hd_ok : isUnmodelledPathComponent d.toList = false ∧ '\x00' ∉ d.toList ∧
      d ≠ "<stdin>" ∧ d ≠ "<stdout>" ∧ d ≠ "<stderr>")
    (hd_norm : (!d.isEmpty && d != ".") = true) :
    let p := ((d ++ "/") ++ toString n) ++ ".base-keys"
    PathOk p = true ∧
    normalizePath p = [d, toString n ++ ".base-keys"] ∧
    ancestors p = [d] ∧
    (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast = [[d]] := by
  have heq : ((d ++ "/") ++ toString n) ++ ".base-keys" =
      (d ++ "/") ++ (toString n ++ ".base-keys") := by
    simp [String.append_assoc]
  rw [heq]
  apply twoSeg_props d (toString n ++ ".base-keys") hd_noslash hd_ok hd_norm
  · rw [String.toList_append]
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact (char_of_isDigit _ (toString_nat_mem_digit h1)).1 rfl
    · revert h2; decide
  · rw [String.toList_append]
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact (char_of_isDigit _ (toString_nat_mem_digit h1)).2.1 rfl
    · revert h2; decide
  · rw [String.toList_append]
    cases hl : (toString n).toList with
    | nil => exact absurd hl (toString_nat_toList_nonempty n)
    | cons c cs =>
      exact ⟨c, cs ++ ".base-keys".toList, rfl, toString_nat_mem_digit (hl ▸ List.Mem.head _)⟩

/-! ## Loaded file-system directory & regular-file invariant -/

private def writeParentDirs : List String :=
  ["identities", "sessions", "signed-pre-keys", "one-time-pre-keys",
   "one-time-kyber-pre-keys", "last-resort-kyber-pre-keys"]

private def rootFileNames : List String :=
  ["address", "identity-key-pair", "registration-id", "coins"]

private def subFileDirs : List String :=
  writeParentDirs ++ ["bundle"]

private theorem dir_beq_root_false (d : String) (hd : d ∈ writeParentDirs)
    (a : String) (ha : a ∈ rootFileNames) : ([d] == [a]) = false := by
  revert a ha
  revert d hd
  decide

private theorem root_not_in_subFileDirs (a : String) (ha : a ∈ rootFileNames) :
    a ∉ subFileDirs := by
  revert a ha; decide

private theorem root_not_stdio (a : String) (ha : a ∈ rootFileNames) :
    [a] ∉ stdioPaths.map normalizePath := by
  revert a ha; decide

private theorem normalizePath_writeParentDir (q : String) (hq : q ∈ writeParentDirs) :
    normalizePath q = [q] := by
  revert q hq; decide

private def IsGameFileKey (k : FsPath) : Prop :=
  (∃ a, k = [a] ∧ a ∈ rootFileNames) ∨
  (∃ d a, k = [d, a] ∧ d ∈ subFileDirs)

private def IsGameInputPath (p : String) : Prop :=
  IsGameFileKey (normalizePath p)

private def IsGameWriteTarget (p : String) : Prop :=
  PathOk p = true ∧
  (normalizePath p).isEmpty = false ∧
  IsGameFileKey (normalizePath p) ∧
  (∀ q ∈ ancestors p, q ∈ writeParentDirs) ∧
  (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast, ∃ d ∈ writeParentDirs, pref = [d])

private def FsDirInv (fs : FsState) : Prop :=
  (∀ d ∈ writeParentDirs, fs.entries [d] = some .dir) ∧
  (∀ k, IsGameFileKey k → fs.entries k ≠ some .dir)

private theorem foldl_setEntry_dir_preserve_not_mem {fs : FsState} {l : List FsPath} {k : FsPath}
    (hnin : k ∉ l) (h : fs.entries k ≠ some .dir) :
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k ≠ some .dir := by
  induction l generalizing fs with
  | nil => exact h
  | cons x xs ih =>
    apply ih (fun hm => hnin (List.Mem.tail _ hm))
    simp only [FsState.setEntry]
    split
    · rename_i heq
      exact absurd (beq_iff_eq.mp heq) (fun he => hnin (he ▸ List.Mem.head _))
    · exact h

private theorem dirsFold_eq_flatten_foldl (dirs : List String) (a : FsState) :
    dirsFold dirs a =
      ((dirs.map fun d => FsPath.nonEmptyPrefixes (normalizePath d)).flatten).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) a := by
  induction dirs generalizing a with
  | nil => rfl
  | cons d ds ih =>
    unfold dirsFold
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons, List.foldl_append]
    exact ih _

private theorem gameFileKey_not_in_partyDirPrefixes {k : FsPath} (hk : IsGameFileKey k) :
    k ∉ ((partyDirs ++ [bundleDir]).map fun d =>
      FsPath.nonEmptyPrefixes (normalizePath d)).flatten := by
  rcases hk with ⟨a, rfl, ha⟩ | ⟨d, a, rfl, hd⟩
  · revert a ha; decide
  · have hpub : d ≠ "public" := by revert d hd; decide
    have hexpand : ((partyDirs ++ [bundleDir]).map fun x =>
        FsPath.nonEmptyPrefixes (normalizePath x)).flatten =
      [["identities"], ["sessions"], ["signed-pre-keys"], ["one-time-pre-keys"],
       ["one-time-kyber-pre-keys"], ["last-resort-kyber-pre-keys"], ["public"],
       ["public"], ["public", "signed-pre-keys"],
       ["public"], ["public", "one-time-pre-keys"],
       ["public"], ["public", "one-time-kyber-pre-keys"],
       ["public"], ["public", "last-resort-kyber-pre-keys"],
       ["bundle"]] := by decide
    rw [hexpand]
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals cases h
    all_goals exact hpub rfl

private theorem fsDirInv_dirsFold_partyDirs : FsDirInv (dirsFold partyDirs {}) := by
  constructor
  · intro d hd; revert d hd; decide
  · intro k hk
    rw [dirsFold_eq_flatten_foldl]
    apply foldl_setEntry_dir_preserve_not_mem
    · intro hm
      apply gameFileKey_not_in_partyDirPrefixes hk
      simp only [List.map_append, List.flatten_append, List.mem_append]
      exact Or.inl hm
    · rcases hk with ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;> intro h <;> cases h

private theorem fsDirInv_dirsFold_partyDirs_bundle :
    FsDirInv (dirsFold (partyDirs ++ [bundleDir]) {}) := by
  constructor
  · intro d hd; revert d hd; decide
  · intro k hk
    rw [dirsFold_eq_flatten_foldl]
    apply foldl_setEntry_dir_preserve_not_mem (gameFileKey_not_in_partyDirPrefixes hk)
    rcases hk with ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;> intro h <;> cases h

private theorem fsDirInv_filesFold {fs : FsState} {files : List (String × List (BitVec 8))}
    (hinv : FsDirInv fs) (hfiles : ∀ f ∈ files, IsGameInputPath f.1) :
    FsDirInv (filesFold files fs) := by
  induction files generalizing fs with
  | nil => exact hinv
  | cons f fs_rest ih =>
    obtain ⟨p, bs⟩ := f
    have hp : IsGameFileKey (normalizePath p) := hfiles (p, bs) (List.Mem.head _)
    have hnext : FsDirInv ((((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some FsEntry.dir)) fs).setFile p (some (FsEntry.file bs))) := by
      rcases hp with ⟨a, ha_eq, ha⟩ | ⟨d0, a0, hd_eq, hd0⟩
      · have hdrop : (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast = [] := by
          rw [ha_eq]; rfl
        rw [hdrop, List.foldl_nil]
        constructor
        · intro d hd
          simp only [FsState.setFile, FsState.setEntry, ha_eq]
          rw [dir_beq_root_false d hd a ha]
          exact hinv.1 d hd
        · intro k hk
          simp only [FsState.setFile, FsState.setEntry, ha_eq]
          split
          · simp
          · exact hinv.2 k hk
      · have hdrop : (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast = [[d0]] := by
          rw [hd_eq]; rfl
        rw [hdrop, List.foldl_cons, List.foldl_nil]
        constructor
        · intro d hd
          simp only [FsState.setFile, FsState.setEntry, hd_eq]
          have hlen : ([d] == [d0, a0]) = false := by simp
          rw [hlen]
          simp only [Bool.false_eq_true, ↓reduceIte]
          split
          · rfl
          · exact hinv.1 d hd
        · intro k hk
          simp only [FsState.setFile, FsState.setEntry, hd_eq]
          split
          · simp
          · have hkne : (k == [d0]) = false := by
              apply beq_false_of_ne
              rcases hk with ⟨a', rfl, ha'⟩ | ⟨d', a', rfl, _⟩
              · intro h; injection h with h1; subst h1
                exact root_not_in_subFileDirs a' ha' hd0
              · intro h; cases h
            rw [hkne]
            exact hinv.2 k hk
    exact ih hnext (fun x hx => hfiles x (List.Mem.tail _ hx))

private theorem writeOk_of_inv {i : Inputs} {p : String}
    (hinv : FsDirInv (filesFold i.files (dirsFold i.dirs {})))
    (ht : IsGameWriteTarget p) : WriteOk i p := by
  obtain ⟨hpok, hnonempty, hfk, hanc, hpref⟩ := ht
  have hdir_entry : ∀ d ∈ writeParentDirs,
      (initFsState (cliInputs i)).entries [d] = some .dir := by
    intro d hd
    have hns : ([d] : FsPath) ∉ stdioPaths.map normalizePath := by
      revert d hd; decide
    exact (initFsState_entries (cliInputs i) [d] hns).trans (hinv.1 d hd)
  refine ⟨hpok, ?_, ?_, ?_⟩
  · rw [files_eq_entries, hnonempty]
    have hs : normalizePath p ∉ stdioPaths.map normalizePath := by
      rcases hfk with ⟨a, ha_eq, ha⟩ | ⟨d, a, hd_eq, _⟩
      · rw [ha_eq]; exact root_not_stdio a ha
      · have hexp : stdioPaths.map normalizePath = [["<stdin>"], ["<stdout>"], ["<stderr>"]] := by
          decide
        rw [hd_eq, hexp]; simp
    rw [initFsState_entries (cliInputs i) (normalizePath p) hs]
    exact hinv.2 (normalizePath p) hfk
  · intro q hq
    have hqd : q ∈ writeParentDirs := hanc q hq
    rw [files_eq_entries, normalizePath_writeParentDir q hqd]
    exact hdir_entry q hqd
  · intro pref hp
    obtain ⟨d, hd, rfl⟩ := hpref pref hp
    exact hdir_entry d hd

/-! ## Classifying every game path shape -/

private theorem target_addressFile : IsGameWriteTarget addressFile :=
  ⟨by decide, by decide, Or.inl ⟨"address", by decide, by decide⟩, by decide, by decide⟩

private theorem target_identityKeyPairFile : IsGameWriteTarget identityKeyPairFile :=
  ⟨by decide, by decide, Or.inl ⟨"identity-key-pair", by decide, by decide⟩, by decide, by decide⟩

private theorem target_registrationIdFile : IsGameWriteTarget registrationIdFile :=
  ⟨by decide, by decide, Or.inl ⟨"registration-id", by decide, by decide⟩, by decide, by decide⟩

private theorem target_identityFile (P : Party) : IsGameWriteTarget (identityFile (partyAddressName P)) := by
  cases P
  · exact ⟨by decide, by decide, Or.inr ⟨"identities", partyAddressName .A, by decide, by decide⟩,
      by decide, by decide⟩
  · exact ⟨by decide, by decide, Or.inr ⟨"identities", partyAddressName .B, by decide, by decide⟩,
      by decide, by decide⟩

private theorem target_sessionFile (P : Party) : IsGameWriteTarget (sessionFile (partyAddress P)) := by
  cases P
  · exact ⟨by decide, by decide, Or.inr ⟨"sessions", (partyAddress .A).text, by decide, by decide⟩,
      by decide, by decide⟩
  · exact ⟨by decide, by decide, Or.inr ⟨"sessions", (partyAddress .B).text, by decide, by decide⟩,
      by decide, by decide⟩

private theorem target_signedPreKeyFile (id : BitVec 32) :
    IsGameWriteTarget (signedPreKeyFile id) := by
  have h := prekey_nat_props "signed-pre-keys" id.toNat (by decide) (by decide) (by decide)
  have heq : signedPreKeyFile id = ("signed-pre-keys" ++ "/") ++ toString id.toNat := rfl
  rw [heq]
  refine ⟨h.1, by rw [h.2.1]; rfl, Or.inr ⟨"signed-pre-keys", _, h.2.1, by decide⟩, ?_, ?_⟩
  · rw [h.2.2.1]; intro q hq; simp at hq; subst hq; decide
  · rw [h.2.2.2]; intro pref hp; simp at hp; exact ⟨"signed-pre-keys", by decide, hp⟩

private theorem target_oneTimePreKeyFile (id : BitVec 32) :
    IsGameWriteTarget (oneTimePreKeyFile id) := by
  have h := prekey_nat_props "one-time-pre-keys" id.toNat (by decide) (by decide) (by decide)
  have heq : oneTimePreKeyFile id = ("one-time-pre-keys" ++ "/") ++ toString id.toNat := rfl
  rw [heq]
  refine ⟨h.1, by rw [h.2.1]; rfl, Or.inr ⟨"one-time-pre-keys", _, h.2.1, by decide⟩, ?_, ?_⟩
  · rw [h.2.2.1]; intro q hq; simp at hq; subst hq; decide
  · rw [h.2.2.2]; intro pref hp; simp at hp; exact ⟨"one-time-pre-keys", by decide, hp⟩

private theorem target_oneTimeKyberPreKeyFile (id : BitVec 32) :
    IsGameWriteTarget (oneTimeKyberPreKeyFile id) := by
  have h := prekey_nat_props "one-time-kyber-pre-keys" id.toNat (by decide) (by decide) (by decide)
  have heq : oneTimeKyberPreKeyFile id =
      ("one-time-kyber-pre-keys" ++ "/") ++ toString id.toNat := rfl
  rw [heq]
  refine ⟨h.1, by rw [h.2.1]; rfl, Or.inr ⟨"one-time-kyber-pre-keys", _, h.2.1, by decide⟩, ?_, ?_⟩
  · rw [h.2.2.1]; intro q hq; simp at hq; subst hq; decide
  · rw [h.2.2.2]; intro pref hp; simp at hp; exact ⟨"one-time-kyber-pre-keys", by decide, hp⟩

private theorem target_lastResortKyberPreKeyFile (id : BitVec 32) :
    IsGameWriteTarget (lastResortKyberPreKeyFile id) := by
  have h := prekey_nat_props "last-resort-kyber-pre-keys" id.toNat
    (by decide) (by decide) (by decide)
  have heq : lastResortKyberPreKeyFile id =
      ("last-resort-kyber-pre-keys" ++ "/") ++ toString id.toNat := rfl
  rw [heq]
  refine ⟨h.1, by rw [h.2.1]; rfl, Or.inr ⟨"last-resort-kyber-pre-keys", _, h.2.1, by decide⟩, ?_, ?_⟩
  · rw [h.2.2.1]; intro q hq; simp at hq; subst hq; decide
  · rw [h.2.2.2]; intro pref hp; simp at hp; exact ⟨"last-resort-kyber-pre-keys", by decide, hp⟩

private theorem target_baseKeysFile (id : BitVec 32) :
    IsGameWriteTarget (baseKeysFile id) := by
  have h := basekeys_nat_props "last-resort-kyber-pre-keys" id.toNat
    (by decide) (by decide) (by decide)
  have heq : baseKeysFile id =
      (("last-resort-kyber-pre-keys" ++ "/") ++ toString id.toNat) ++ ".base-keys" := rfl
  rw [heq]
  refine ⟨h.1, by rw [h.2.1]; rfl, Or.inr ⟨"last-resort-kyber-pre-keys", _, h.2.1, by decide⟩, ?_, ?_⟩
  · rw [h.2.2.1]; intro q hq; simp at hq; subst hq; decide
  · rw [h.2.2.2]; intro pref hp; simp at hp; exact ⟨"last-resort-kyber-pre-keys", by decide, hp⟩

private theorem target_encodeDir (W : PEParams) (st : PqParty) :
    ∀ pw ∈ encodeDir W st, IsGameWriteTarget pw.1 := by
  intro pw hpw
  unfold encodeDir at hpw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatten, or_assoc] at hpw
  rcases hpw with h | h | h | h | h | h | h | h | h
  · subst h; exact target_addressFile
  · subst h; exact target_identityKeyPairFile
  · subst h; exact target_registrationIdFile
  · cases hp : st.peerId <;> simp only [hp, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; exact target_identityFile _
  · cases hs : st.session with
    | none => simp [hs] at h
    | some x =>
      obtain ⟨x, g⟩ := x
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; exact target_sessionFile _
  · obtain ⟨⟨id, _⟩, _, rfl⟩ := h; exact target_signedPreKeyFile id
  · obtain ⟨⟨id, _⟩, _, rfl⟩ := h; exact target_oneTimePreKeyFile id
  · obtain ⟨⟨id, _⟩, _, rfl⟩ := h; exact target_oneTimeKyberPreKeyFile id
  · obtain ⟨l, ⟨⟨id, _, _⟩, _, rfl⟩, hl⟩ := h
    dsimp only at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with h | h <;> subst h
    · exact target_lastResortKyberPreKeyFile id
    · exact target_baseKeysFile id

private theorem inputPath_bundle (b : PublicBundle) :
    ∀ f ∈ b.files bundleDir, IsGameInputPath f.1 := by
  intro f hf
  unfold PublicBundle.files at hf
  cases ho : b.oneTime with
  | none =>
    simp only [ho, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> dsimp only
    · exact Or.inr ⟨"bundle", "identity-key", by decide, by decide⟩
    · exact Or.inr ⟨"bundle", "registration-id", by decide, by decide⟩
    · exact Or.inr ⟨"bundle", "signed-pre-key", by decide, by decide⟩
    · exact Or.inr ⟨"bundle", "kyber-pre-key", by decide, by decide⟩
  | some x =>
    obtain ⟨id, key⟩ := x
    simp only [ho, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · exact Or.inr ⟨"bundle", "identity-key", by decide, by decide⟩
    · exact Or.inr ⟨"bundle", "registration-id", by decide, by decide⟩
    · exact Or.inr ⟨"bundle", "signed-pre-key", by decide, by decide⟩
    · exact Or.inr ⟨"bundle", "kyber-pre-key", by decide, by decide⟩
    · exact Or.inr ⟨"bundle", "one-time-pre-key", by decide, by decide⟩

private theorem inputPath_coinsFile : IsGameInputPath coinsFile :=
  Or.inl ⟨"coins", by decide, by decide⟩

/-! ## `CoinsReadable` when `(coinsFile, coins)` is the last entry of `i.files` -/

private theorem coinsReadable_of_last (i : Inputs) (prefixFiles : List (String × List (BitVec 8)))
    (coins : List (BitVec 8)) (hfiles : i.files = prefixFiles ++ [(coinsFile, coins)])
    (hcap : coins.length ≤ fileCapBytes) :
    CoinsReadable i := by
  unfold CoinsReadable
  rw [files_eq_entries]
  have hne : (normalizePath "coins").isEmpty = false := by decide
  have hns : normalizePath "coins" ∉ stdioPaths.map normalizePath := by decide
  rw [hne, initFsState_entries (cliInputs i) (normalizePath "coins") hns]
  change (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath "coins") ≠ some .dir ∧
    ∀ bs, (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath "coins") = some (.file bs) →
      bs.length ≤ fileCapBytes
  rw [hfiles]
  unfold filesFold
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, FsState.setFile, FsState.setEntry, coinsFile]
  refine ⟨by simp, fun bs h => ?_⟩
  simp at h
  subst h
  exact hcap

/-! ## Public theorems -/

/-- Every write a successful PQ call commits succeeds on its inputs (`encodeDir W st'` for any `st'`),
when `init` passes `bundleDir` (as `pqInitInputs`, `pqSendInputs` and `pqRecvInputs` do). -/
theorem writeOk_pqInputs (W : PEParams) (st st' : PqParty) (cmd : Cmd)
    (extra : List (String × List (BitVec 8))) (coins stdin : List (BitVec 8))
    (hcmd : ∀ peer dir, cmd = .init peer dir → dir = bundleDir)
    (hextra : extra = [] ∨ ∃ b, extra = (publicBundleOf b).files bundleDir) :
    ∀ pw ∈ encodeDir W st', WriteOk (pqInputs W st cmd extra coins stdin) pw.1 := by
  have hdinv : FsDirInv (dirsFold (pqInputs W st cmd extra coins stdin).dirs {}) := by
    cases h : cmd with
    | init peer dir =>
      have hdir := hcmd peer dir h
      subst hdir
      exact fsDirInv_dirsFold_partyDirs_bundle
    | send _ =>
      simpa [pqInputs] using fsDirInv_dirsFold_partyDirs
    | recv _ =>
      simpa [pqInputs] using fsDirInv_dirsFold_partyDirs
  have hfinv : FsDirInv (filesFold (pqInputs W st cmd extra coins stdin).files
      (dirsFold (pqInputs W st cmd extra coins stdin).dirs {})) := by
    apply fsDirInv_filesFold hdinv
    intro f hf
    simp only [pqInputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      or_assoc] at hf
    rcases hf with h1 | h2 | rfl
    · exact (target_encodeDir W st f h1).2.2.1
    · rcases hextra with rfl | ⟨b, rfl⟩
      · cases h2
      · exact inputPath_bundle (publicBundleOf b) f h2
    · exact inputPath_coinsFile
  intro pw hpw
  exact writeOk_of_inv hfinv (target_encodeDir W st' pw hpw)

theorem writeOk_pqInitInputs (W : PEParams) (st st' : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ∀ pw ∈ encodeDir W st', WriteOk (pqInitInputs W st b t) pw.1 :=
  writeOk_pqInputs W st st' _ _ _ _
    (by intro _ _ h; injection h with _ hd; exact hd.symm) (Or.inr ⟨b, rfl⟩)

theorem writeOk_pqSendInputs (W : PEParams) (st st' : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    ∀ pw ∈ encodeDir W st', WriteOk (pqSendInputs W st m r) pw.1 :=
  writeOk_pqInputs W st st' _ _ _ _ (by intro _ _ h; cases h) (Or.inl rfl)

theorem writeOk_pqRecvInputs (W : PEParams) (st st' : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ∀ pw ∈ encodeDir W st', WriteOk (pqRecvInputs W st c rc) pw.1 :=
  writeOk_pqInputs W st st' _ _ _ _ (by intro _ _ h; cases h) (Or.inl rfl)

/-- `CoinsReadable` holds for `pqInputs` because the `coins` file is the final entry of `pqInputs.files`. -/
theorem coinsReadable_pqInputs (W : PEParams) (st : PqParty) (cmd : Cmd)
    (extra : List (String × List (BitVec 8))) (coins stdin : List (BitVec 8))
    (_hextra : extra = [] ∨ ∃ b, extra = (publicBundleOf b).files bundleDir)
    (hcap : coins.length ≤ fileCapBytes := by
      first | decide | simp [HMAC.keyToBytes32, List.Vector.toList_length, initiateTapeLen, fileCapBytes]) :
    CoinsReadable (pqInputs W st cmd extra coins stdin) :=
  coinsReadable_of_last _ (encodeDir W st ++ extra) coins rfl hcap

/-- Every write in `smWrites s.party rec` satisfies `WriteOk` on `binInputs`. -/
theorem writeOk_binInputs (s : BinState) (cmd : Cmd) (coins stdin rec : List (BitVec 8)) :
    ∀ pw ∈ smWrites s.party rec, WriteOk (binInputs s cmd coins stdin) pw.1 := by
  have hfinv : FsDirInv (filesFold (binInputs s cmd coins stdin).files
      (dirsFold (binInputs s cmd coins stdin).dirs {})) := by
    apply fsDirInv_filesFold fsDirInv_dirsFold_partyDirs
    intro f hf
    simp only [binInputs, dirOfE, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with (rfl | rfl | rfl) | rfl
    · exact target_addressFile.2.2.1
    · exact (target_identityFile _).2.2.1
    · exact (target_sessionFile _).2.2.1
    · exact inputPath_coinsFile
  intro pw hpw
  simp only [smWrites, List.mem_cons, List.not_mem_nil, or_false] at hpw
  rcases hpw with rfl | rfl
  · exact writeOk_of_inv hfinv (target_identityFile _)
  · exact writeOk_of_inv hfinv (target_sessionFile _)

theorem coinsReadable_binInputs (s : BinState) (cmd : Cmd) (coins stdin : List (BitVec 8))
    (hcap : coins.length ≤ fileCapBytes := by
      first | decide | simp [HMAC.keyToBytes32, List.Vector.toList_length, initiateTapeLen, fileCapBytes]) :
    CoinsReadable (binInputs s cmd coins stdin) :=
  coinsReadable_of_last _ (dirOfE s.party s.bytes) coins rfl hcap

theorem writeOk_smInputs (g : GhostState Bytes) (cmd : Cmd) (coins stdin rec : List (BitVec 8)) :
    ∀ pw ∈ smWrites g.party rec, WriteOk (smInputs g cmd coins stdin) pw.1 := by
  have hfinv : FsDirInv (filesFold (smInputs g cmd coins stdin).files
      (dirsFold (smInputs g cmd coins stdin).dirs {})) := by
    apply fsDirInv_filesFold fsDirInv_dirsFold_partyDirs
    intro f hf
    simp only [smInputs, dirOfE, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with (rfl | rfl | rfl) | rfl
    · exact target_addressFile.2.2.1
    · exact (target_identityFile _).2.2.1
    · exact (target_sessionFile _).2.2.1
    · exact inputPath_coinsFile
  intro pw hpw
  simp only [smWrites, List.mem_cons, List.not_mem_nil, or_false] at hpw
  rcases hpw with rfl | rfl
  · exact writeOk_of_inv hfinv (target_identityFile _)
  · exact writeOk_of_inv hfinv (target_sessionFile _)

theorem coinsReadable_smInputs (g : GhostState Bytes) (cmd : Cmd) (coins stdin : List (BitVec 8))
    (hcap : coins.length ≤ fileCapBytes := by
      first | decide | simp [HMAC.keyToBytes32, List.Vector.toList_length, initiateTapeLen, fileCapBytes]) :
    CoinsReadable (smInputs g cmd coins stdin) :=
  coinsReadable_of_last _ (dirOfE g.party (encodeRecord g)) coins rfl hcap

private theorem loadable_partyDirs : ∀ d ∈ partyDirs, LoadablePath d := by
  intro d hd
  simp only [partyDirs, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide⟩

/-- `binInputs` satisfies `InputsLoadable` whenever the session record and coins fit `MAX_LFS_FILESIZE`. -/
theorem loadable_binInputs (s : BinState) (cmd : Cmd) (coins stdin : List (BitVec 8))
    (hrec : s.bytes.length ≤ MAX_LFS_FILESIZE) (hcoins : coins.length ≤ MAX_LFS_FILESIZE) :
    InputsLoadable (binInputs s cmd coins stdin) := by
  refine ⟨loadable_partyDirs, ?_⟩
  intro f hf
  simp only [binInputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h
  · refine ⟨loadable_dirOfE _ _ f h, ?_⟩
    simp only [dirOfE, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · cases s.party <;> decide +kernel
    · simp [IdentityKey.serialize, PublicKey.serialize, MAX_LFS_FILESIZE]
    · exact hrec
  · subst h; exact ⟨loadable_coinsFile, hcoins⟩

end CryptoVerification.SignalSession.Cli
