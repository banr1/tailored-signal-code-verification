/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed

/-!
# File-System Extensionality Under Visible Paths

Canonical `FsPath` round-trip lemmas and exact `initFsState` / `cliRunAbortOnPanic` extensionality
under `InputsEquivRaw` and `FilesVisibleRaw`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Parity

open Arm64 Arm64.Process
open CryptoVerification.SignalSession

def FilesVisibleRaw (files : List (String × List (BitVec 8))) : Prop :=
  ∀ f ∈ files, Arm64.normalizePath f.1 ≠ [] ∧
    Arm64.normalizePath f.1 ∉ stdioPaths.map Arm64.normalizePath

def InputsEquivRaw (i i' : Inputs) : Prop :=
  i.argv = i'.argv ∧ i.dirs = i'.dirs ∧ i.stdin = i'.stdin ∧
    ∀ p, filesOf i.files p = filesOf i'.files p

theorem cliRunSig_eq_none_of_loadState_error {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {msg : String} (herr : elf.loadState (cliProcessInputs i) = .error msg) :
    cliRunAbortOnPanic elf W i = none := by
  unfold cliRunAbortOnPanic
  split
  · rename_i hex
    rcases hex with ⟨_, s0, hload, _⟩
    rw [herr] at hload
    cases hload
  · rfl

def LoadableFile (f : String × List (BitVec 8)) : Prop :=
  LoadablePath f.1 ∧ f.2.length ≤ MAX_LFS_FILESIZE

theorem loadState_error_of_not_loadable_files {elf : ElfImage} {i : Inputs}
    (hbad : ¬ ∀ f ∈ i.files, LoadableFile f) :
    ∃ msg, elf.loadState (cliProcessInputs i) = .error msg := by
  have hany : ((cliProcessInputs i).files.any fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = true := by
    rw [List.any_eq_true]
    exact Classical.byContradiction fun hno => hbad fun ⟨p, bs⟩ hf =>
      ⟨⟨by cases h : hasLeadingSlash p
           · rfl
           · exact False.elim (hno ⟨(p, bs), hf, by simp only [h, Bool.true_or]⟩),
        by cases h : hasDotDot p
           · rfl
           · exact False.elim (hno ⟨(p, bs), hf, by simp only [h, Bool.or_true, Bool.true_or]⟩)⟩,
       Classical.byContradiction fun hlen =>
         hno ⟨(p, bs), hf, by simp only [hlen, decide_false, Bool.not_false, Bool.or_true]⟩⟩
  unfold ElfImage.loadState
  by_cases hwf : (!elf.WellFormed) = true
  · simp only [hwf, ↓reduceIte]; exact ⟨_, rfl⟩
  · by_cases hd : ((cliProcessInputs i).dirs.any fun d => hasLeadingSlash d || hasDotDot d) = true
    · simp only [hwf, hd, Bool.false_eq_true, ↓reduceIte]; exact ⟨_, rfl⟩
    · rw [hany]; simp only [hwf, hd, Bool.false_eq_true, ↓reduceIte]; exact ⟨_, rfl⟩

/-! ## Canonical `FsPath` Round-Trip and Prefix Characterization -/

private def CanonSeg (seg : String) : Bool :=
  !seg.isEmpty && seg != "." && decide ('/' ∉ seg.toList)

private def CanonPath (q : FsPath) : Prop :=
  ∀ seg ∈ q, CanonSeg seg = true

set_option linter.auxLemma false in
private theorem splitSlash_go_cons_ne_feb4b3 {c : Char} (cur rest : List Char) (hc : c ≠ '/') :
    splitSlash.go cur (c :: rest) = splitSlash.go (c :: cur) rest := by
  delta splitSlash.go splitSlash.go._f splitSlash.go.match_1
  dsimp only [List.brecOn, List.brecOn.go, List.casesOn]
  split_ifs with h
  · exact absurd h hc
  · rfl

private theorem splitSlash_go_no_slash :
    ∀ (cs cur : List Char), '/' ∉ cur → ∀ seg ∈ splitSlash.go cur cs, '/' ∉ seg.toList
  | [], cur, hcur, seg, hseg => by
    change seg ∈ [String.ofList cur.reverse] at hseg
    rw [List.mem_singleton] at hseg
    subst hseg; rw [String.toList_ofList, List.mem_reverse]; exact hcur
  | c :: cs, cur, hcur, seg, hseg => by
    by_cases hc : c = '/'
    · subst hc
      change seg ∈ String.ofList cur.reverse :: splitSlash.go [] cs at hseg
      rcases List.mem_cons.mp hseg with rfl | hrest
      · rw [String.toList_ofList, List.mem_reverse]; exact hcur
      · exact splitSlash_go_no_slash cs [] (by simp) seg hrest
    · rw [splitSlash_go_cons_ne_feb4b3 cur cs hc] at hseg
      exact splitSlash_go_no_slash cs (c :: cur)
        (by simp [List.mem_cons, Ne.symm hc, hcur]) seg hseg

private theorem canonPath_normalizePath (p : String) : CanonPath (normalizePath p) := by
  intro seg hseg
  unfold normalizePath splitSlash at hseg
  rw [List.mem_filter] at hseg
  have hns := splitSlash_go_no_slash p.toList [] (by simp) seg hseg.1
  simp [CanonSeg, hseg.2, hns]

private theorem splitSlash_go_append_nil :
    ∀ (cs cur : List Char), '/' ∉ cs →
      splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by rw [List.append_nil]; rfl
  | c :: cs, cur, hcs => by
    have hc : c ≠ '/' := fun h => hcs (h ▸ List.mem_cons_self ..)
    have hcs' : '/' ∉ cs := fun h => hcs (List.mem_cons_of_mem _ h)
    rw [splitSlash_go_cons_ne_feb4b3 cur cs hc, splitSlash_go_append_nil cs (c :: cur) hcs']
    simp [List.reverse_cons, List.append_assoc]

theorem splitSlash_go_append_slash :
    ∀ (cs cur rest : List Char), '/' ∉ cs →
      splitSlash.go cur (cs ++ '/' :: rest) =
        String.ofList (cur.reverse ++ cs) :: splitSlash.go [] rest
  | [], cur, rest, _ => by rw [List.nil_append, List.append_nil]; rfl
  | c :: cs, cur, rest, hcs => by
    have hc : c ≠ '/' := fun h => hcs (h ▸ List.mem_cons_self ..)
    have hcs' : '/' ∉ cs := fun h => hcs (List.mem_cons_of_mem _ h)
    rw [List.cons_append, splitSlash_go_cons_ne_feb4b3 cur _ hc,
        splitSlash_go_append_slash cs (c :: cur) rest hcs']
    simp [List.reverse_cons, List.append_assoc]

private theorem splitSlash_go_joinSlashChars :
    ∀ (q : FsPath), q ≠ [] → CanonPath q →
      splitSlash.go [] (joinSlashChars (q.map String.toList)) = q
  | [], hne, _ => absurd rfl hne
  | [seg], _, hcan => by
    have hseg := hcan seg (List.mem_singleton.mpr rfl); unfold CanonSeg at hseg
    have hns : '/' ∉ seg.toList := (Bool.and_eq_true_iff.mp hseg).2 |> of_decide_eq_true
    simp only [List.map_cons, List.map_nil, joinSlashChars]
    rw [splitSlash_go_append_nil seg.toList [] hns]; simp [String.ofList_toList]
  | seg :: seg2 :: rest, _, hcan => by
    have hseg := hcan seg (List.mem_cons_self ..); unfold CanonSeg at hseg
    have hns : '/' ∉ seg.toList := (Bool.and_eq_true_iff.mp hseg).2 |> of_decide_eq_true
    have hcan' : CanonPath (seg2 :: rest) := fun x hx =>
      hcan x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, joinSlashChars]
    rw [splitSlash_go_append_slash seg.toList [] _ hns, List.reverse_nil, List.nil_append,
        String.ofList_toList]
    change seg :: splitSlash.go [] (joinSlashChars ((seg2 :: rest).map String.toList)) =
      seg :: seg2 :: rest
    rw [splitSlash_go_joinSlashChars (seg2 :: rest) (by simp) hcan']

private theorem normalizePath_toPathString_of_canon {q : FsPath}
    (hcan : CanonPath q) (hne : q ≠ []) :
    normalizePath q.toPathString = q := by
  cases q with
  | nil => exact absurd rfl hne
  | cons seg rest =>
    unfold FsPath.toPathString normalizePath splitSlash
    rw [String.toList_ofList, splitSlash_go_joinSlashChars (seg :: rest) hne hcan]
    apply List.filter_eq_self.mpr
    intro x hx
    have hc := hcan x hx
    unfold CanonSeg at hc
    simp only [Bool.and_eq_true] at hc
    simp [hc.1]

private theorem nonEmptyPrefixes_nil : FsPath.nonEmptyPrefixes [] = [] := rfl
private theorem nonEmptyPrefixes_cons (s : String) (tl : FsPath) :
    FsPath.nonEmptyPrefixes (s :: tl) = [s] :: (FsPath.nonEmptyPrefixes tl).map (s :: ·) := rfl

private theorem mem_nonEmptyPrefixes :
    ∀ {q p : FsPath}, q ∈ FsPath.nonEmptyPrefixes p ↔ q ≠ [] ∧ q <+: p
  | q, [] => by simp [nonEmptyPrefixes_nil]
  | [], s :: rest => by simp [nonEmptyPrefixes_cons]
  | t :: qs, s :: rest => by
    simp only [nonEmptyPrefixes_cons, List.mem_cons, List.mem_map, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and, List.cons_prefix_cons]
    constructor
    · rintro (h | ⟨r, hr, hcons⟩)
      · injection h with ht hqs; subst ht hqs; exact ⟨rfl, List.nil_prefix⟩
      · injection hcons with ht hqs; subst ht hqs
        exact ⟨rfl, (mem_nonEmptyPrefixes.mp hr).2⟩
    · rintro ⟨rfl, hpref⟩
      cases qs with
      | nil => exact Or.inl rfl
      | cons u us =>
        exact Or.inr ⟨u :: us, mem_nonEmptyPrefixes.mpr ⟨by simp, hpref⟩, rfl⟩

private theorem dropLast_concat {α : Type} : ∀ (l : List α) (x : α), (l ++ [x]).dropLast = l
  | [], _ => rfl
  | y :: ys, x => by
    have hne : ys ++ [x] ≠ [] := by simp
    simp [List.cons_append, List.dropLast_cons_of_ne_nil hne, dropLast_concat ys x]

private theorem nonEmptyPrefixes_eq_dropLast_append :
    ∀ {p : FsPath}, p ≠ [] →
      FsPath.nonEmptyPrefixes p = (FsPath.nonEmptyPrefixes p).dropLast ++ [p]
  | [], hp => absurd rfl hp
  | [s], _ => rfl
  | s :: t :: rest, _ => by
    have ih := nonEmptyPrefixes_eq_dropLast_append (p := t :: rest) (by simp)
    have hne : (FsPath.nonEmptyPrefixes (t :: rest)).map (s :: ·) ≠ [] := by rw [ih]; simp
    rw [nonEmptyPrefixes_cons s (t :: rest), List.dropLast_cons_of_ne_nil hne]
    conv_lhs => rw [ih]
    conv_rhs => rw [ih]
    rw [List.map_append, List.map_singleton, dropLast_concat]
    rfl

private theorem length_lt_of_mem_dropLast_nonEmptyPrefixes :
    ∀ {q p : FsPath}, q ∈ (FsPath.nonEmptyPrefixes p).dropLast → q.length < p.length
  | _, [], h => by simp [nonEmptyPrefixes_nil] at h
  | _, [_], h => by simp [nonEmptyPrefixes_cons, nonEmptyPrefixes_nil] at h
  | q, s :: t :: rest, h => by
    have ih_eq := nonEmptyPrefixes_eq_dropLast_append (p := t :: rest) (by simp)
    have hne : (FsPath.nonEmptyPrefixes (t :: rest)).map (s :: ·) ≠ [] := by rw [ih_eq]; simp
    have hsub : ((FsPath.nonEmptyPrefixes (t :: rest)).map (s :: ·)).dropLast =
        ((FsPath.nonEmptyPrefixes (t :: rest)).dropLast).map (s :: ·) := by
      conv_lhs => rw [ih_eq]
      rw [List.map_append, List.map_singleton, dropLast_concat]
    rw [nonEmptyPrefixes_cons s (t :: rest), List.dropLast_cons_of_ne_nil hne, hsub,
        List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨r, hr, rfl⟩
    · simp
    · have hlt := length_lt_of_mem_dropLast_nonEmptyPrefixes hr
      simp only [List.length_cons] at hlt ⊢; omega

private theorem mem_dropLast_nonEmptyPrefixes {q p : FsPath} :
    q ∈ (FsPath.nonEmptyPrefixes p).dropLast ↔ q ≠ [] ∧ q <+: p ∧ q ≠ p := by
  by_cases hp : p = []
  · subst hp; simp [nonEmptyPrefixes_nil]
  · constructor
    · intro hq
      have hlen := length_lt_of_mem_dropLast_nonEmptyPrefixes hq
      have hmem : q ∈ FsPath.nonEmptyPrefixes p := by
        rw [nonEmptyPrefixes_eq_dropLast_append hp]; exact List.mem_append_left _ hq
      obtain ⟨hne, hpref⟩ := mem_nonEmptyPrefixes.mp hmem
      exact ⟨hne, hpref, fun he => by subst he; omega⟩
    · rintro ⟨hne, hpref, hne_p⟩
      have hmem : q ∈ FsPath.nonEmptyPrefixes p := mem_nonEmptyPrefixes.mpr ⟨hne, hpref⟩
      rw [nonEmptyPrefixes_eq_dropLast_append hp, List.mem_append, List.mem_singleton] at hmem
      exact hmem.resolve_right hne_p

/-! ## `initFsState` Equality Under `InputsEquivRaw` and `FilesVisibleRaw` -/

private def HasFile (fs : FsState) (q : FsPath) : Prop :=
  ∃ bs, fs.entries q = some (.file bs)

private theorem hasFile_iff_fileOfEntry {fs : FsState} {q : FsPath} :
    HasFile fs q ↔ (fileOfEntry (fs.entries q)).isSome := by
  rcases h : fs.entries q with _ | (_ | bs) <;> simp [HasFile, fileOfEntry, h]

private structure FoldInv (a fs : FsState) : Prop where
  some_imp  : ∀ q, (fs.entries q).isSome → a.entries q ≠ none ∨ ∃ r, q <+: r ∧ HasFile fs r
  base_some : ∀ q, a.entries q ≠ none → (fs.entries q).isSome
  pref_some : ∀ q r, q ≠ [] → q <+: r → HasFile fs r → (fs.entries q).isSome
  file_vis  : ∀ q, HasFile fs q → CanonPath q ∧ q ≠ [] ∧ q ∉ stdioPaths.map normalizePath

private theorem foldl_dir_entries (fs : FsState) (l : List FsPath) (q : FsPath) :
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries q =
      if q ∈ l then some .dir else fs.entries q := by
  induction l generalizing fs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases hqx : q = x
    · subst hqx; simp [FsState.setEntry]
    · simp [FsState.setEntry, hqx]

private theorem foldInv_base (dirs : List String) :
    FoldInv (dirsFold dirs {}) (dirsFold dirs {}) where
  some_imp := fun _ hs => Or.inl (Option.isSome_iff_ne_none.mp hs)
  base_some := fun _ hn => Option.isSome_iff_ne_none.mpr hn
  pref_some := fun _ r _ _ ⟨bs, hbs⟩ => by
    have hno : fileOfEntry ((dirsFold dirs {}).entries r) = none := NoFiles.dirsFold_none dirs r
    rw [hbs] at hno; cases hno
  file_vis := fun r ⟨bs, hbs⟩ => by
    have hno : fileOfEntry ((dirsFold dirs {}).entries r) = none := NoFiles.dirsFold_none dirs r
    rw [hbs] at hno; cases hno

private theorem dirsFold_root_ne_none (dirs : List String) :
    (dirsFold dirs {}).entries [] ≠ none := by
  suffices ∀ a : FsState, a.entries [] ≠ none → (dirsFold dirs a).entries [] ≠ none from
    this {} (by show (if ([] : FsPath).isEmpty then some FsEntry.dir else none) ≠ none; decide)
  unfold dirsFold
  induction dirs with
  | nil => intro a ha; exact ha
  | cons d ds ih =>
    intro a ha; apply ih
    rw [foldl_dir_entries]
    split <;> [simp; exact ha]

private theorem foldInv_step {a fs : FsState} {p : String} {bs : List (BitVec 8)}
    (hinv : FoldInv a fs)
    (hp_ne : normalizePath p ≠ [])
    (hp_nstd : normalizePath p ∉ stdioPaths.map normalizePath) :
    FoldInv a
      ((((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))) := by
  let p₀ := normalizePath p
  let fs' := (((FsPath.nonEmptyPrefixes p₀).dropLast).foldl
    (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))
  have hent : ∀ q, fs'.entries q =
      if q = p₀ then some (.file bs)
      else if q ≠ [] ∧ q <+: p₀ then some .dir
      else fs.entries q := by
    intro q
    change (if q == normalizePath p then some (.file bs)
      else ((((FsPath.nonEmptyPrefixes p₀).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) fs).entries q)) = _
    rw [foldl_dir_entries]
    simp only [beq_iff_eq, mem_dropLast_nonEmptyPrefixes]
    by_cases hqp : q = p₀
    · simp [hqp, p₀]
    · by_cases hpr : q ≠ [] ∧ q <+: p₀
      · simp [hqp, p₀, hpr.1, hpr.2]
      · simp [hqp, p₀, hpr]
  have hp_file : HasFile fs' p₀ := ⟨bs, by rw [hent p₀]; simp⟩
  have hfile_iff : ∀ r, HasFile fs' r ↔ r = p₀ ∨ (¬ (r ≠ [] ∧ r <+: p₀) ∧ HasFile fs r) := by
    intro r
    by_cases hrp : r = p₀
    · subst hrp; simp [hp_file]
    · by_cases hpr : r ≠ [] ∧ r <+: p₀
      · simp [HasFile, hent r, hrp, hpr.1, hpr.2]
      · simp [HasFile, hent r, hrp, hpr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hsome
    change (fs'.entries q).isSome = true at hsome
    by_cases hpr : q ≠ [] ∧ q <+: p₀
    · exact Or.inr ⟨p₀, hpr.2, hp_file⟩
    · have hqp : q ≠ p₀ := fun he => hpr ⟨he ▸ hp_ne, he ▸ List.prefix_refl _⟩
      rw [hent q] at hsome
      simp only [hqp, hpr, ↓reduceIte] at hsome
      rcases hinv.some_imp q hsome with ha | ⟨r, hqr, hrf⟩
      · exact Or.inl ha
      · by_cases hrp0 : r <+: p₀
        · exact Or.inr ⟨p₀, hqr.trans hrp0, hp_file⟩
        · exact Or.inr ⟨r, hqr, (hfile_iff r).mpr (Or.inr ⟨fun h => hrp0 h.2, hrf⟩)⟩
  · intro q ha
    change (fs'.entries q).isSome = true
    rw [hent q]
    by_cases hqp : q = p₀
    · simp [hqp]
    · by_cases hpr : q ≠ [] ∧ q <+: p₀
      · simp [hqp, hpr.1, hpr.2]
      · simp [hqp, hpr, hinv.base_some q ha]
  · intro q r hq_ne hqr hrf
    change (fs'.entries q).isSome = true
    rw [hent q]
    by_cases hqp0 : q <+: p₀
    · by_cases hqp : q = p₀
      · simp [hqp]
      · simp [hqp, hq_ne, hqp0]
    · rcases (hfile_iff r).mp hrf with rfl | ⟨_, hrf_old⟩
      · exact absurd hqr hqp0
      · have hqp : q ≠ p₀ := fun he => hqp0 (he ▸ List.prefix_refl _)
        have hpr : ¬ (q ≠ [] ∧ q <+: p₀) := fun h => hqp0 h.2
        simp [hqp, hpr, hinv.pref_some q r hq_ne hqr hrf_old]
  · intro q hqf
    rcases (hfile_iff q).mp hqf with rfl | ⟨_, hqf_old⟩
    · exact ⟨canonPath_normalizePath p, hp_ne, hp_nstd⟩
    · exact hinv.file_vis q hqf_old

private theorem foldInv_filesFold (dirs : List String) (files : List (String × List (BitVec 8)))
    (hvis : FilesVisibleRaw files) :
    FoldInv (dirsFold dirs {}) (filesFold files (dirsFold dirs {})) := by
  suffices ∀ (fs : FsState), FoldInv (dirsFold dirs {}) fs →
      FoldInv (dirsFold dirs {}) (filesFold files fs) from
    this _ (foldInv_base dirs)
  induction files with
  | nil => intro fs h; exact h
  | cons f fs_tl ih =>
    intro fs h
    obtain ⟨hp_ne, hp_nstd⟩ := hvis f (List.mem_cons_self ..)
    have hvis' : FilesVisibleRaw fs_tl := fun x hx => hvis x (List.mem_cons_of_mem _ hx)
    exact ih hvis' _ (foldInv_step h hp_ne hp_nstd)

private theorem filesFold_stdin_fds (files : List (String × List (BitVec 8))) (a : FsState) :
    (filesFold files a).stdin = a.stdin ∧ (filesFold files a).fds = a.fds := by
  induction files generalizing a with
  | nil => exact ⟨rfl, rfl⟩
  | cons f fs ih =>
    let step := (((FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) a).setFile f.1 (some (.file f.2))
    have hdir : ∀ (l : List FsPath) (b : FsState),
        (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) b).stdin = b.stdin ∧
        (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) b).fds = b.fds := by
      intro l; induction l with
      | nil => intro _; exact ⟨rfl, rfl⟩
      | cons _ xs ih2 => intro b; exact ih2 (b.setEntry _ _)
    obtain ⟨hs, hfds⟩ := hdir ((FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast) a
    obtain ⟨hs', hfds'⟩ := ih step
    exact ⟨hs'.trans hs, hfds'.trans hfds⟩

private theorem fileOfEntry_filesFold_eq_filesOf (dirs : List String)
    (files : List (String × List (BitVec 8))) {q : FsPath}
    (hcan : CanonPath q) (hne : q ≠ []) (hnstd : q ∉ stdioPaths.map normalizePath) :
    fileOfEntry ((filesFold files (dirsFold dirs {})).entries q) = filesOf files q.toPathString := by
  have hnorm := normalizePath_toPathString_of_canon hcan hne
  have hv := congrFun (fsView_initFsState { dirs := dirs, files := files }) q.toPathString
  unfold fsView at hv
  simp only [hnorm, hnstd, ↓reduceIte] at hv
  have hempty : q.isEmpty = false := by cases q with | nil => exact absurd rfl hne | cons _ _ => rfl
  simp only [FsState.files, FsState.getEntry, hnorm, hempty] at hv
  rw [initFsState_entries { dirs := dirs, files := files } q hnstd] at hv
  exact hv

private theorem filesFold_eq_of_filesOf_eq (dirs : List String) {f₁ f₂ : List (String × List (BitVec 8))}
    (hfiles : ∀ p, filesOf f₁ p = filesOf f₂ p)
    (hvis : FilesVisibleRaw f₁) (hvis' : FilesVisibleRaw f₂) :
    filesFold f₁ (dirsFold dirs {}) = filesFold f₂ (dirsFold dirs {}) := by
  let a := dirsFold dirs {}
  let fs₁ := filesFold f₁ a; let fs₂ := filesFold f₂ a
  have hinv₁ : FoldInv a fs₁ := foldInv_filesFold dirs f₁ hvis
  have hinv₂ : FoldInv a fs₂ := foldInv_filesFold dirs f₂ hvis'
  have hsame : SameFiles fs₁ fs₂ := fun q => by
    by_cases hq : CanonPath q ∧ q ≠ [] ∧ q ∉ stdioPaths.map normalizePath
    · rw [fileOfEntry_filesFold_eq_filesOf dirs f₁ hq.1 hq.2.1 hq.2.2,
          fileOfEntry_filesFold_eq_filesOf dirs f₂ hq.1 hq.2.1 hq.2.2, hfiles q.toPathString]
    · have hn1 : ¬ HasFile fs₁ q := fun hf => hq (hinv₁.file_vis q hf)
      have hn2 : ¬ HasFile fs₂ q := fun hf => hq (hinv₂.file_vis q hf)
      rw [hasFile_iff_fileOfEntry, Bool.not_eq_true, Option.isSome_eq_false_iff,
          Option.isNone_iff_eq_none] at hn1 hn2
      rw [hn1, hn2]
  have hhas : ∀ r, HasFile fs₁ r ↔ HasFile fs₂ r := fun r => by
    rw [hasFile_iff_fileOfEntry, hasFile_iff_fileOfEntry, hsame r]
  have hisSome : ∀ q, (fs₁.entries q).isSome = (fs₂.entries q).isSome := fun q => by
    apply Bool.eq_iff_iff.mpr
    by_cases hq0 : q = []
    · subst hq0; exact ⟨fun _ => hinv₂.base_some [] (dirsFold_root_ne_none dirs),
        fun _ => hinv₁.base_some [] (dirsFold_root_ne_none dirs)⟩
    · exact ⟨fun hs1 => (hinv₁.some_imp q hs1).elim (hinv₂.base_some q)
        (fun ⟨r, hqr, hrf⟩ => hinv₂.pref_some q r hq0 hqr ((hhas r).mp hrf)),
        fun hs2 => (hinv₂.some_imp q hs2).elim (hinv₁.base_some q)
        (fun ⟨r, hqr, hrf⟩ => hinv₁.pref_some q r hq0 hqr ((hhas r).mpr hrf))⟩
  have hent_eq : fs₁.entries = fs₂.entries := funext fun q => by
    have hf := hsame q; have hs := hisSome q
    rcases h1 : fs₁.entries q with _ | (_ | bs₁) <;>
      rcases h2 : fs₂.entries q with _ | (_ | bs₂) <;>
      simp [h1, h2, fileOfEntry] at hf hs ⊢
    exact hf
  have hst : fs₁.stdin = fs₂.stdin :=
    (filesFold_stdin_fds f₁ a).1.trans (filesFold_stdin_fds f₂ a).1.symm
  have hfd : fs₁.fds = fs₂.fds :=
    (filesFold_stdin_fds f₁ a).2.trans (filesFold_stdin_fds f₂ a).2.symm
  rcases h1 : fs₁ with ⟨e1, s1, f1⟩; rcases h2 : fs₂ with ⟨e2, s2, f2⟩
  simp only [h1, h2] at hent_eq hst hfd
  change fs₁ = fs₂; rw [h1, h2, hent_eq, hst, hfd]

/-- Under `InputsEquivRaw i i'`, `FilesVisibleRaw i.files`, and `FilesVisibleRaw i'.files`, `initFsState` produces identical file-system states. -/
theorem initFsState_eq_of_inputsEquiv_of_visible {i i' : Inputs}
    (heq : InputsEquivRaw i i') (hvis : FilesVisibleRaw i.files) (hvis' : FilesVisibleRaw i'.files) :
    Arm64.Process.initFsState (cliProcessInputs i) =
      Arm64.Process.initFsState (cliProcessInputs i') := by
  obtain ⟨_, hdirs, hstdin, hfiles⟩ := heq
  have hfs_eq := filesFold_eq_of_filesOf_eq i.dirs hfiles hvis hvis'
  unfold Arm64.Process.initFsState cliProcessInputs processInputs
  simp only [← hdirs, hstdin]
  exact congrArg (fun w : FsState =>
    let w' := ((w.setFd 0#64 (some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio })).setFd
      1#64 (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio })).setFd
      2#64 (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio })
    { w' with stdin := i'.stdin }) hfs_eq

/-! ## `loadState` and `cliRunAbortOnPanic` Extensionality -/

private theorem files_any_bad_false_of_loadable {files : List (String × List (BitVec 8))}
    (hl : ∀ f ∈ files, LoadableFile f) :
    (files.any fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false := by
  rw [List.any_eq_false]
  rintro ⟨p, bs⟩ hf
  obtain ⟨⟨h1, h2⟩, h3⟩ := hl (p, bs) hf
  simp only [h1, h2, h3, Bool.or_self, decide_true, Bool.not_true, Bool.false_eq_true,
    not_false_eq_true]

theorem loadState_eq_of_inputsEquiv_of_visible_of_loadable (elf : ElfImage) {i i' : Inputs}
    (heq : InputsEquivRaw i i') (hvis : FilesVisibleRaw i.files) (hvis' : FilesVisibleRaw i'.files)
    (hload : ∀ f ∈ i.files, LoadableFile f) (hload' : ∀ f ∈ i'.files, LoadableFile f) :
    elf.loadState (cliProcessInputs i) = elf.loadState (cliProcessInputs i') := by
  have hfs := initFsState_eq_of_inputsEquiv_of_visible heq hvis hvis'
  obtain ⟨hargv, hdirs, _, _⟩ := heq
  have hany := files_any_bad_false_of_loadable (files := (cliProcessInputs i).files) hload
  have hany' := files_any_bad_false_of_loadable (files := (cliProcessInputs i').files) hload'
  have hstack : buildInitialStack elf (cliProcessInputs i) = buildInitialStack elf (cliProcessInputs i') := by
    unfold buildInitialStack cliProcessInputs processInputs; simp only [hargv]
  have hdirs_eq : (cliProcessInputs i).dirs = (cliProcessInputs i').dirs := hdirs
  unfold ElfImage.loadState
  rw [hany, hany', hdirs_eq, hstack, hfs]; rfl

/-- Visibility- and loadability-guarded file-extensionality predicate satisfied by `cliRunAbortOnPanic elf W`. -/
def FilesExtVisibleRaw (run : CliRun) : Prop :=
  ∀ i i' : Inputs, InputsEquivRaw i i' → FilesVisibleRaw i.files → FilesVisibleRaw i'.files →
    (∀ f ∈ i'.files, LoadableFile f) → run i = none ∨ run i = run i'

theorem filesExtVisible_cliRunSig (elf : ElfImage) (W : CliHooks) :
    FilesExtVisibleRaw (cliRunAbortOnPanic elf W) := fun i i' heq hvis hvis' hload' => by
  by_cases hload : ∀ f ∈ i.files, LoadableFile f
  · right; have hls := loadState_eq_of_inputsEquiv_of_visible_of_loadable elf heq hvis hvis' hload hload'
    unfold cliRunAbortOnPanic CliRunsTo; rw [hls]
  · obtain ⟨_, herr⟩ := loadState_error_of_not_loadable_files (elf := elf) hload
    exact Or.inl (cliRunSig_eq_none_of_loadState_error herr)

theorem cliRunSig_some_of_inputsEquiv {elf : ElfImage} {W : CliHooks} {i i' : Inputs} {o : Outcome}
    (heq : InputsEquivRaw i i') (hvis : FilesVisibleRaw i.files) (hvis' : FilesVisibleRaw i'.files)
    (hload' : ∀ f ∈ i'.files, LoadableFile f) (hr : cliRunAbortOnPanic elf W i = some o) :
    cliRunAbortOnPanic elf W i' = some o := by
  rcases filesExtVisible_cliRunSig elf W i i' heq hvis hvis' hload' with hnone | hsame
  · rw [hr] at hnone; cases hnone
  · exact hsame.symm.trans hr

theorem normalizePath_head_slash (dir rest : String)
    (hno : '/' ∉ dir.toList) (hne : (!dir.isEmpty && dir != ".") = true) :
    (normalizePath ((dir ++ "/") ++ rest)).head? = some dir := by
  have hsplit : splitSlash ((dir ++ "/") ++ rest) = dir :: splitSlash.go [] rest.toList := by
    unfold splitSlash
    simpa [String.toList_append] using splitSlash_go_append_slash dir.toList [] rest.toList hno
  simp [normalizePath, hsplit, hne]

theorem visible_of_head_slash {p : String} (dir rest : String)
    (hp : p = (dir ++ "/") ++ rest)
    (hno : '/' ∉ dir.toList) (hne : (!dir.isEmpty && dir != ".") = true)
    (hstd : some dir ∉ (stdioPaths.map normalizePath).map List.head?) :
    normalizePath p ≠ [] ∧ normalizePath p ∉ stdioPaths.map normalizePath := by
  subst hp
  have hhd := normalizePath_head_slash dir rest hno hne
  refine ⟨fun hnil => ?_, fun hmem => hstd (List.mem_map.mpr ⟨_, hmem, hhd⟩)⟩
  rw [hnil] at hhd; cases hhd

end LibsignalBinary.Proofs.SignalSession.Cli.Parity
