/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.BundleGeneralParse
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.List.SplitOn.Basic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.InitPaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Direct-Child `FsState` Lookup and Arbitrary-Input Initiate Bridge

Proves direct-child `FsState`/`filesOf` lookup (ruling out `ENOTDIR` and `EISDIR`) and relates
`InitOk₀`, `initDef`, and post-write `filesOf` for arbitrary CLI `Inputs`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Parity

open Arm64 Arm64.Process CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunRefine CryptoVerification.SignalSession.Cli.RunProofs

private theorem ite_pos {α : Type} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := match inst with | isTrue _ => rfl | isFalse h => absurd hc h
private theorem ite_neg {α : Type} {c : Prop} [inst : Decidable c] (hc : c → False) {a b : α} :
    (if c then a else b) = b := match inst with | isTrue h => absurd h hc | isFalse _ => rfl

/-! ## Direct-Child `FsState` and `filesOf` Lookup -/

theorem foldl_setEntry_entries (l : List Arm64.FsPath) (val : Option Arm64.FsEntry)
    (fs : Arm64.FsState) (q : Arm64.FsPath) :
    (l.foldl (fun acc pref => acc.setEntry pref val) fs).entries q =
      if q ∈ l then val else fs.entries q := by
  induction l generalizing fs with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons, ih]; simp only [Arm64.FsState.setEntry, List.mem_cons]
    by_cases hqa : q ∈ as
    · simp [hqa]
    · by_cases hqe : q = a
      · subst hqe; simp [hqa]
      · simp [hqa, hqe, beq_false_of_ne hqe]

def fileStep (fs : Arm64.FsState) (entry : String × List (BitVec 8)) : Arm64.FsState :=
  let (p, bs) := entry
  let withAnc := ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
    (fun acc pref => acc.setEntry pref (some .dir)) fs
  withAnc.setFile p (some (.file bs))

theorem filesFold_eq_foldl_fileStep (f : List (String × List (BitVec 8))) (base : Arm64.FsState) :
    filesFold f base = f.foldl fileStep base := rfl

theorem fileStep_entries (fs : Arm64.FsState) (p : String) (bs : List (BitVec 8)) (q : Arm64.FsPath) :
    (fileStep fs (p, bs)).entries q =
      if q = Arm64.normalizePath p then some (.file bs)
      else if q ∈ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast then some .dir
      else fs.entries q := by
  unfold fileStep Arm64.FsState.setFile Arm64.FsState.setEntry; dsimp only
  by_cases hqp : q = Arm64.normalizePath p
  · subst hqp; simp
  · simp only [beq_false_of_ne hqp, Bool.false_eq_true, ↓reduceIte, hqp]
    exact foldl_setEntry_entries _ _ fs q

private theorem emptyFsState_entries_of_ne_nil (q : Arm64.FsPath) (hq : q ≠ []) :
    ({} : Arm64.FsState).entries q = none := by
  show (if q.isEmpty then some Arm64.FsEntry.dir else none) = none
  rw [List.isEmpty_eq_false_iff.mpr hq]; rfl

theorem filesFold_entries_eq_or (f : List (String × List (BitVec 8))) (base : Arm64.FsState)
    {q : Arm64.FsPath} (hq : q ≠ []) :
    (filesFold f base).entries q = ((filesFold f {}).entries q).or (base.entries q) := by
  rw [filesFold_eq_foldl_fileStep, filesFold_eq_foldl_fileStep]
  induction f generalizing base with
  | nil =>
    show base.entries q = (({} : Arm64.FsState).entries q).or (base.entries q)
    rw [emptyFsState_entries_of_ne_nil q hq]; rfl
  | cons x xs ih =>
    rcases x with ⟨p, bs⟩; simp only [List.foldl_cons]
    rw [ih (fileStep base (p, bs)), ih (fileStep {} (p, bs)),
      fileStep_entries base p bs q, fileStep_entries {} p bs q]
    by_cases h1 : q = Arm64.normalizePath p
    · rw [ite_pos h1, ite_pos h1]; cases (xs.foldl fileStep {}).entries q <;> rfl
    · rw [ite_neg h1, ite_neg h1]
      by_cases h2 : q ∈ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast
      · rw [ite_pos h2, ite_pos h2]; cases (xs.foldl fileStep {}).entries q <;> rfl
      · rw [ite_neg h2, ite_neg h2, emptyFsState_entries_of_ne_nil q hq]
        cases (xs.foldl fileStep {}).entries q <;> rfl

private theorem dropLast_map_eq {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map f).dropLast = l.dropLast.map f
  | [] => rfl | [_] => rfl | _ :: b :: rest => congrArg (f _ :: ·) (dropLast_map_eq f (b :: rest))

theorem mem_dropLast_nonEmptyPrefixes_iff {r q : Arm64.FsPath} :
    q ∈ (Arm64.FsPath.nonEmptyPrefixes r).dropLast ↔ q ≠ [] ∧ q <+: r ∧ q ≠ r := by
  match r, q with
  | [], q =>
    exact ⟨fun h => (by cases h), fun ⟨hne, hpre, _⟩ => absurd (List.prefix_nil.mp hpre) hne⟩
  | [s], q =>
    refine ⟨fun h => (by cases h), fun ⟨hne, ⟨tl, htl⟩, hner⟩ => ?_⟩
    cases q with
    | nil => exact absurd rfl hne
    | cons a as =>
      injection htl with ha has; subst ha
      exact absurd (congrArg (a :: ·) (List.append_eq_nil_iff.mp has).1) hner
  | s :: s2 :: rest, [] =>
    change [] ∈ [s] :: (List.map (s :: ·) (Arm64.FsPath.nonEmptyPrefixes (s2 :: rest))).dropLast ↔ _
    rw [dropLast_map_eq]; refine ⟨?_, fun ⟨hne, _, _⟩ => absurd rfl hne⟩
    simp only [List.mem_cons, List.mem_map]; rintro (h | ⟨_, _, h⟩) <;> cases h
  | s :: s2 :: rest, t :: qs =>
    change (t :: qs) ∈
      [s] :: (List.map (s :: ·) (Arm64.FsPath.nonEmptyPrefixes (s2 :: rest))).dropLast ↔ _
    rw [dropLast_map_eq]; constructor
    · simp only [List.mem_cons, List.mem_map, List.cons.injEq]
      rintro (⟨rfl, rfl⟩ | ⟨u, hu, rfl, rfl⟩)
      · exact ⟨by simp, ⟨s2 :: rest, rfl⟩, by simp⟩
      · obtain ⟨_, hpre, hne⟩ := (mem_dropLast_nonEmptyPrefixes_iff (r := s2 :: rest) (q := u)).mp hu
        exact ⟨by simp, List.cons_prefix_cons.mpr ⟨rfl, hpre⟩, fun h => hne (List.cons.inj h).2⟩
    · rintro ⟨_, hpre, hne⟩; obtain ⟨rfl, hpre'⟩ := List.cons_prefix_cons.mp hpre
      simp only [List.mem_cons, List.mem_map, List.cons.injEq, true_and]
      cases qs with
      | nil => exact .inl rfl
      | cons a as =>
        exact .inr ⟨a :: as, (mem_dropLast_nonEmptyPrefixes_iff (r := s2 :: rest) (q := a :: as)).mpr
          ⟨by simp, hpre', fun h => hne (congrArg (t :: ·) h)⟩, rfl⟩

def SegCanon (seg : String) : Prop :=
  seg.isEmpty = false ∧ (seg != ".") = true ∧ '/' ∉ seg.toList

private theorem splitSlash_go_step {c : Char} {cur cs : List Char} (hc : c ≠ '/') :
    Arm64.splitSlash.go cur (c :: cs) = Arm64.splitSlash.go (c :: cur) cs := by
  rw [Arm64.splitSlash.go.eq_def]; split
  · simp_all
  · simp_all
  · rename_i _ _ _ _ heq; injection heq with h1 h2; subst h1 h2; rfl

private theorem splitSlash_go_no_slash :
    ∀ (cs cur : List Char), '/' ∉ cur → ∀ seg ∈ Arm64.splitSlash.go cur cs, '/' ∉ seg.toList
  | [], cur, hcur => fun seg hseg => by
    simp only [Arm64.splitSlash.go, List.mem_singleton] at hseg; subst hseg
    rw [String.toList_ofList, List.mem_reverse]; exact hcur
  | c :: cs, cur, hcur => by
    by_cases hc : c = '/'
    · subst hc; intro seg hseg; simp only [Arm64.splitSlash.go, List.mem_cons] at hseg
      rcases hseg with rfl | hseg
      · rw [String.toList_ofList, List.mem_reverse]; exact hcur
      · exact splitSlash_go_no_slash cs [] (by simp) seg hseg
    · rw [splitSlash_go_step hc]
      exact splitSlash_go_no_slash cs (c :: cur) (by simp [List.mem_cons, Ne.symm hc, hcur])

theorem segCanon_of_mem_normalizePath {p seg : String} (h : seg ∈ Arm64.normalizePath p) :
    SegCanon seg := by
  unfold Arm64.normalizePath at h; rw [List.mem_filter] at h; obtain ⟨hmem, hfilt⟩ := h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hfilt
  exact ⟨hfilt.1, hfilt.2, splitSlash_go_no_slash p.toList [] (by simp) seg hmem⟩

private theorem splitSlash_go_append_slash :
    ∀ (s cur rest : List Char), '/' ∉ s →
      Arm64.splitSlash.go cur (s ++ '/' :: rest) =
        String.ofList (cur.reverse ++ s) :: Arm64.splitSlash.go [] rest
  | [], _, _, _ => by simp [Arm64.splitSlash.go]
  | c :: cs, cur, rest, hs => by
    simp only [List.cons_append]
    rw [splitSlash_go_step (fun h => hs (h ▸ List.mem_cons_self ..)),
      splitSlash_go_append_slash cs (c :: cur) rest (fun h => hs (List.mem_cons_of_mem _ h)),
      List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem splitSlash_go_single :
    ∀ (s cur : List Char), '/' ∉ s →
      Arm64.splitSlash.go cur s = [String.ofList (cur.reverse ++ s)]
  | [], _, _ => by simp [Arm64.splitSlash.go]
  | c :: cs, cur, hs => by
    rw [splitSlash_go_step (fun h => hs (h ▸ List.mem_cons_self ..)),
      splitSlash_go_single cs (c :: cur) (fun h => hs (List.mem_cons_of_mem _ h)),
      List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem splitSlash_joinSlashChars :
    ∀ (q : Arm64.FsPath), q ≠ [] → (∀ seg ∈ q, '/' ∉ seg.toList) →
      Arm64.splitSlash.go [] (Arm64.joinSlashChars (q.map String.toList)) = q
  | [], hne, _ => absurd rfl hne
  | [seg], _, hno => by
    simp only [List.map_cons, List.map_nil, Arm64.joinSlashChars]
    rw [splitSlash_go_single seg.toList [] (hno seg (List.mem_singleton_self _))]
    simp [String.ofList_toList]
  | seg :: seg2 :: rest, _, hno => by
    simp only [List.map_cons, Arm64.joinSlashChars]
    rw [splitSlash_go_append_slash seg.toList [] _ (hno seg (List.mem_cons_self ..))]
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList]
    exact congrArg (seg :: ·) (splitSlash_joinSlashChars (seg2 :: rest) (by simp)
      (fun x hx => hno x (List.mem_cons_of_mem _ hx)))

theorem normalizePath_toPathString {q : Arm64.FsPath} (hq : q ≠ []) (hcan : ∀ seg ∈ q, SegCanon seg) :
    Arm64.normalizePath (Arm64.FsPath.toPathString q) = q := by
  cases q with
  | nil => exact absurd rfl hq
  | cons seg rest =>
    unfold Arm64.FsPath.toPathString Arm64.normalizePath Arm64.splitSlash
    rw [String.toList_ofList,
      splitSlash_joinSlashChars (seg :: rest) (by simp) (fun x hx => (hcan x hx).2.2),
      List.filter_eq_self]
    intro x hx; obtain ⟨h1, h2, _⟩ := hcan x hx; simp [h1, h2]

private theorem filesFold_support_prefix (f : List (String × List (BitVec 8))) :
    ∀ {q : Arm64.FsPath}, q ≠ [] → (filesFold f {}).entries q ≠ none →
      ∃ e ∈ f, q <+: Arm64.normalizePath e.1 := by
  induction f with
  | nil => intro q hq hne; exact absurd (emptyFsState_entries_of_ne_nil q hq) hne
  | cons x xs ih =>
    rcases x with ⟨p, bs⟩; intro q hq hne
    rw [show filesFold ((p, bs) :: xs) {} = filesFold xs (fileStep {} (p, bs)) from rfl,
      filesFold_entries_eq_or xs _ hq] at hne
    cases hxs : (filesFold xs {}).entries q with
    | some _ =>
      obtain ⟨e, he, hpre⟩ := ih hq (by rw [hxs]; intro hc; cases hc)
      exact ⟨e, List.mem_cons_of_mem _ he, hpre⟩
    | none =>
      rw [hxs, Option.none_or, fileStep_entries] at hne
      by_cases h1 : q = Arm64.normalizePath p
      · subst h1; exact ⟨(p, bs), List.mem_cons_self .., List.prefix_refl _⟩
      · by_cases h2 : q ∈ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast
        · exact ⟨(p, bs), List.mem_cons_self .., (mem_dropLast_nonEmptyPrefixes_iff.mp h2).2.1⟩
        · rw [ite_neg h1, ite_neg h2] at hne; exact absurd (emptyFsState_entries_of_ne_nil q hq) hne

private theorem filesFold_dir_strict_prefix (f : List (String × List (BitVec 8))) :
    ∀ {q : Arm64.FsPath}, q ≠ [] → (filesFold f {}).entries q = some .dir →
      ∃ e ∈ f, q <+: Arm64.normalizePath e.1 ∧ q ≠ Arm64.normalizePath e.1 := by
  induction f with
  | nil =>
    intro q hq hdir
    rw [show (filesFold [] {}).entries q = ({} : Arm64.FsState).entries q from rfl,
      emptyFsState_entries_of_ne_nil q hq] at hdir; cases hdir
  | cons x xs ih =>
    rcases x with ⟨p, bs⟩; intro q hq hdir
    rw [show filesFold ((p, bs) :: xs) {} = filesFold xs (fileStep {} (p, bs)) from rfl,
      filesFold_entries_eq_or xs _ hq] at hdir
    cases hxs : (filesFold xs {}).entries q with
    | some _ =>
      rw [hxs, Option.some_or, Option.some.injEq] at hdir; subst hdir
      obtain ⟨e, he, hpre, hne⟩ := ih hq hxs; exact ⟨e, List.mem_cons_of_mem _ he, hpre, hne⟩
    | none =>
      rw [hxs, Option.none_or, fileStep_entries] at hdir
      by_cases h1 : q = Arm64.normalizePath p
      · rw [ite_pos h1] at hdir; cases hdir
      · by_cases h2 : q ∈ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast
        · obtain ⟨_, hpre, hne⟩ := mem_dropLast_nonEmptyPrefixes_iff.mp h2
          exact ⟨(p, bs), List.mem_cons_self .., hpre, hne⟩
        · rw [ite_neg h1, ite_neg h2, emptyFsState_entries_of_ne_nil q hq] at hdir; cases hdir

private theorem filesFold_some_file_of_no_strict (f : List (String × List (BitVec 8)))
    {q : Arm64.FsPath}
    (hno : ∀ e ∈ f, ¬ (q <+: Arm64.normalizePath e.1 ∧ q ≠ Arm64.normalizePath e.1)) :
    ∀ (base : Arm64.FsState),
      ((∃ e ∈ f, Arm64.normalizePath e.1 = q) ∨ (∃ bs, base.entries q = some (.file bs))) →
      ∃ bs, (filesFold f base).entries q = some (.file bs) := by
  induction f with
  | nil =>
    rintro _ (⟨_, hm, _⟩ | ⟨bs, hbs⟩)
    · cases hm
    · exact ⟨bs, hbs⟩
  | cons x xs ih =>
    rcases x with ⟨p, bs⟩; intro base h
    have hnot_anc : q ∉ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast :=
      fun hm => hno (p, bs) (List.mem_cons_self ..) (mem_dropLast_nonEmptyPrefixes_iff.mp hm).2
    apply ih (fun e he => hno e (List.mem_cons_of_mem _ he)) (fileStep base (p, bs))
    by_cases hqp : q = Arm64.normalizePath p
    · exact .inr ⟨bs, by rw [fileStep_entries, ite_pos hqp]⟩
    · rcases h with ⟨e, he, heq⟩ | ⟨b0, hb0⟩
      · rcases List.mem_cons.mp he with rfl | he'
        · exact absurd heq.symm hqp
        · exact .inl ⟨e, he', heq⟩
      · exact .inr ⟨b0, by rw [fileStep_entries, ite_neg hqp, ite_neg hnot_anc]; exact hb0⟩

private theorem filesFold_ne_none_of_strict_prefix (f : List (String × List (BitVec 8)))
    {q : Arm64.FsPath} (hq : q ≠ [])
    (hex : ∃ e ∈ f, q <+: Arm64.normalizePath e.1 ∧ q ≠ Arm64.normalizePath e.1) :
    ∀ base : Arm64.FsState, (filesFold f base).entries q ≠ none := by
  induction f with
  | nil => obtain ⟨_, hm, _⟩ := hex; cases hm
  | cons x xs ih =>
    rcases x with ⟨p, bs⟩; intro base; rcases hex with ⟨e, he, hpre, hne⟩
    rcases List.mem_cons.mp he with rfl | he'
    · rw [show filesFold ((p, bs) :: xs) base = filesFold xs (fileStep base (p, bs)) from rfl,
        filesFold_entries_eq_or xs _ hq, fileStep_entries, ite_neg hne,
        ite_pos (mem_dropLast_nonEmptyPrefixes_iff.mpr ⟨hq, hpre, hne⟩)]
      cases (filesFold xs {}).entries q <;> intro hc <;> cases hc
    · exact ih ⟨e, he', hpre, hne⟩ (fileStep base (p, bs))

private def maxLenPath : List Arm64.FsPath → Option Arm64.FsPath
  | [] => none
  | x :: xs => match maxLenPath xs with
    | none => some x | some y => if x.length ≤ y.length then some y else some x

private theorem maxLenPath_spec :
    ∀ {l : List Arm64.FsPath}, l ≠ [] →
      ∃ m, maxLenPath l = some m ∧ m ∈ l ∧ ∀ z ∈ l, z.length ≤ m.length
  | [], h => absurd rfl h
  | [x], _ => ⟨x, rfl, List.mem_singleton_self _, fun z hz => by rw [List.mem_singleton.mp hz]⟩
  | x :: x2 :: xs, _ => by
    obtain ⟨y, hy, hy_mem, hy_max⟩ := maxLenPath_spec (l := x2 :: xs) (by simp)
    have hstep : maxLenPath (x :: x2 :: xs) =
        (if x.length ≤ y.length then some y else some x) := by
      change (match maxLenPath (x2 :: xs) with
        | none => some x | some y => if x.length ≤ y.length then some y else some x) = _
      rw [hy]
    by_cases hle : x.length ≤ y.length
    · refine ⟨y, by rw [hstep, ite_pos hle], List.mem_cons_of_mem _ hy_mem, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hle
      · exact hy_max z hz'
    · refine ⟨x, by rw [hstep, ite_neg hle], List.mem_cons_self .., fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact Nat.le_refl _
      · have := hy_max z hz'; omega

private theorem filesOf_eq_match_filesFold (f : List (String × List (BitVec 8))) {p : String}
    (hne : Arm64.normalizePath p ≠ [])
    (hns : Arm64.normalizePath p ∉ stdioPaths.map Arm64.normalizePath) :
    filesOf f p = match (filesFold f {}).entries (Arm64.normalizePath p) with
      | some (.file bs) => some bs | _ => none := by
  unfold filesOf fsView
  rw [ite_neg hns, files_eq_entries,
    ite_neg (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries { files := f } (Arm64.normalizePath p) hns]; rfl

theorem initFsState_entries_eq_of_filesOf_eq
    {P : Arm64.FsPath → Prop} (hP_ne : ∀ q, P q → q ≠ [])
    (hP_stdio : ∀ q, P q → q ∉ stdioPaths.map Arm64.normalizePath)
    (hP_up : ∀ q q', P q → q <+: q' → P q') {f₁ f₂ : List (String × List (BitVec 8))}
    (h_agree : ∀ p : String, P (Arm64.normalizePath p) → filesOf f₁ p = filesOf f₂ p) :
    ∀ q : Arm64.FsPath, P q → (filesFold f₁ {}).entries q = (filesFold f₂ {}).entries q := by
  have hfile_fwd : ∀ {g₁ g₂ : List (String × List (BitVec 8))},
      (∀ p : String, P (Arm64.normalizePath p) → filesOf g₁ p = filesOf g₂ p) →
      ∀ {q : Arm64.FsPath} {bs : List (BitVec 8)}, P q →
        (filesFold g₁ {}).entries q = some (.file bs) →
        (filesFold g₂ {}).entries q = some (.file bs) := by
    intro g₁ g₂ hag q bs hPq h1; have hqne := hP_ne q hPq
    obtain ⟨_, _, hpre⟩ := filesFold_support_prefix g₁ hqne (by rw [h1]; intro hc; cases hc)
    let s := Arm64.FsPath.toPathString q
    have hns : Arm64.normalizePath s = q :=
      normalizePath_toPathString hqne (fun seg hseg => segCanon_of_mem_normalizePath (hpre.subset hseg))
    have hf1 : filesOf g₁ s = some bs := by
      rw [filesOf_eq_match_filesFold g₁ (hns ▸ hqne) (hns ▸ hP_stdio q hPq), hns, h1]
    have hf2 : filesOf g₂ s = some bs := (hag s (hns ▸ hPq)).symm.trans hf1
    rw [filesOf_eq_match_filesFold g₂ (hns ▸ hqne) (hns ▸ hP_stdio q hPq), hns] at hf2
    cases h2 : (filesFold g₂ {}).entries q with
    | none => rw [h2] at hf2; cases hf2
    | some entry =>
      cases entry with
      | dir => rw [h2] at hf2; cases hf2
      | file bs' => rw [h2] at hf2; injection hf2 with heq; subst heq; rfl
  have hdir_fwd : ∀ {g₁ g₂ : List (String × List (BitVec 8))},
      (∀ p : String, P (Arm64.normalizePath p) → filesOf g₁ p = filesOf g₂ p) →
      ∀ {q : Arm64.FsPath}, P q → (filesFold g₁ {}).entries q = some .dir →
        (filesFold g₂ {}).entries q = some .dir := by
    intro g₁ g₂ hag q hPq hdir1; have hqne := hP_ne q hPq
    obtain ⟨e0, he0, hpre0, hne0⟩ := filesFold_dir_strict_prefix g₁ hqne hdir1
    let cands := (g₁.map fun e => Arm64.normalizePath e.1).filter fun r => decide (q <+: r ∧ q ≠ r)
    have hcands_ne : cands ≠ [] := fun hemp => by
      have hm : Arm64.normalizePath e0.1 ∈ cands := by
        simp only [cands, List.mem_filter, List.mem_map, decide_eq_true_eq]
        exact ⟨⟨e0, he0, rfl⟩, hpre0, hne0⟩
      rw [hemp] at hm; cases hm
    obtain ⟨qmax, _, hqmax_mem, hqmax_max⟩ := maxLenPath_spec hcands_ne
    simp only [cands, List.mem_filter, List.mem_map, decide_eq_true_eq] at hqmax_mem
    obtain ⟨⟨emax, hemax, hemax_eq⟩, hq_pre_qmax, hq_ne_qmax⟩ := hqmax_mem
    have hPqmax : P qmax := hP_up q qmax hPq hq_pre_qmax
    have hno_strict :
        ∀ e ∈ g₁, ¬ (qmax <+: Arm64.normalizePath e.1 ∧ qmax ≠ Arm64.normalizePath e.1) := by
      rintro e he ⟨⟨tl, htl⟩, hne_e⟩
      have hlen_lt : qmax.length < (Arm64.normalizePath e.1).length := by
        cases tl with
        | nil => rw [List.append_nil] at htl; exact absurd htl hne_e
        | cons _ _ => rw [← htl, List.length_append, List.length_cons]; omega
      have hqlen := hq_pre_qmax.length_le
      have he_mem : Arm64.normalizePath e.1 ∈ cands := by
        simp only [cands, List.mem_filter, List.mem_map, decide_eq_true_eq]
        exact ⟨⟨e, he, rfl⟩, hq_pre_qmax.trans ⟨tl, htl⟩, fun heq => by rw [heq] at hqlen; omega⟩
      have := hqmax_max _ he_mem; omega
    obtain ⟨_, hbs1⟩ := filesFold_some_file_of_no_strict g₁ hno_strict {} (.inl ⟨emax, hemax, hemax_eq⟩)
    have hbs2 := hfile_fwd hag hPqmax hbs1
    obtain ⟨e2, he2, hpre2⟩ :=
      filesFold_support_prefix g₂ (hP_ne qmax hPqmax) (by rw [hbs2]; intro hc; cases hc)
    have hq_ne_e2 : q ≠ Arm64.normalizePath e2.1 := fun heq => by
      have h1 : qmax.length ≤ q.length := heq ▸ hpre2.length_le
      rcases hq_pre_qmax with ⟨tl, htl⟩
      cases tl with
      | nil => rw [List.append_nil] at htl; exact hq_ne_qmax htl
      | cons _ _ => rw [← htl, List.length_append, List.length_cons] at h1; omega
    cases h2 : (filesFold g₂ {}).entries q with
    | none =>
      exact absurd h2
        (filesFold_ne_none_of_strict_prefix g₂ hqne ⟨e2, he2, hq_pre_qmax.trans hpre2, hq_ne_e2⟩ {})
    | some entry =>
      cases entry with
      | dir => rfl
      | file _ =>
        have h1' := hfile_fwd (fun p hp => (hag p hp).symm) hPq h2; rw [hdir1] at h1'; cases h1'
  intro q hPq; have hag_symm := fun p hp => (h_agree p hp).symm
  cases h1 : (filesFold f₁ {}).entries q with
  | some entry =>
    cases entry with
    | file _ => exact (hfile_fwd h_agree hPq h1).symm
    | dir => exact (hdir_fwd h_agree hPq h1).symm
  | none =>
    cases h2 : (filesFold f₂ {}).entries q with
    | none => rfl
    | some entry =>
      cases entry with
      | file _ => have h1' := hfile_fwd hag_symm hPq h2; rw [h1] at h1'; cases h1'
      | dir => have h1' := hdir_fwd hag_symm hPq h2; rw [h1] at h1'; cases h1'

private theorem stdioPaths_norm_eq :
    stdioPaths.map Arm64.normalizePath = [["<stdin>"], ["<stdout>"], ["<stderr>"]] := by decide

private theorem not_stdio_of_head {q : Arm64.FsPath}
    (h1 : q.head? ≠ some "<stdin>") (h2 : q.head? ≠ some "<stdout>")
    (h3 : q.head? ≠ some "<stderr>") : q ∉ stdioPaths.map Arm64.normalizePath := by
  rw [stdioPaths_norm_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (rfl | rfl | rfl)
  · exact h1 rfl
  · exact h2 rfl
  · exact h3 rfl

private theorem head_bundle_not_stdio {q : Arm64.FsPath} (hq : q.head? = some "bundle") :
    q ∉ stdioPaths.map Arm64.normalizePath :=
  not_stdio_of_head (by rw [hq]; decide) (by rw [hq]; decide) (by rw [hq]; decide)

private theorem filesOf_append_coins_bundle (bundleEntries : List (String × List (BitVec 8)))
    (coins : List (BitVec 8)) {p : String} (hp : (Arm64.normalizePath p).head? = some "bundle") :
    filesOf (bundleEntries ++ [("coins", coins)]) p = filesOf bundleEntries p := by
  have hne : Arm64.normalizePath p ≠ [] := fun h => by rw [h] at hp; cases hp
  have hns := head_bundle_not_stdio hp
  rw [filesOf_eq_match_filesFold _ hne hns, filesOf_eq_match_filesFold _ hne hns]
  have happ : filesFold (bundleEntries ++ [("coins", coins)]) {} =
      fileStep (filesFold bundleEntries {}) ("coins", coins) := by
    rw [filesFold_eq_foldl_fileStep, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
  have hcoins : Arm64.normalizePath "coins" = ["coins"] := by decide
  rw [happ, fileStep_entries,
    ite_neg (by rw [hcoins]; intro heq; rw [heq] at hp; exact absurd hp (by decide)),
    show (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath "coins")).dropLast = [] by
      rw [hcoins]; rfl,
    ite_neg (fun hm => nomatch hm)]

theorem filesOf_bundle_eq_of_directChild
    {i : Inputs} {bundleEntries : List (String × List (BitVec 8))} {coins : List (BitVec 8)}
    {d : String → Option (List (BitVec 8))}
    (hd_scrub : ∀ p, (Arm64.normalizePath p).head? = some "bundle" → d p = none)
    (h_filesOf : ∀ p, Arm64.normalizePath p ∉ stdioPaths.map Arm64.normalizePath →
      filesOf i.files p = (filesOf (bundleEntries ++ [("coins", coins)]) p).or (d p)) :
    ∀ p : String, (Arm64.normalizePath p).head? = some "bundle" →
      filesOf i.files p = filesOf bundleEntries p := fun p hp => by
  rw [h_filesOf p (head_bundle_not_stdio hp), hd_scrub p hp, Option.or_none,
    filesOf_append_coins_bundle bundleEntries coins hp]

private theorem filesFold_directChild_bundle_not_file
    (bundleEntries : List (String × List (BitVec 8)))
    (hb : ∀ e ∈ bundleEntries, ∃ name, name ≠ "" ∧ Arm64.normalizePath e.1 = ["bundle", name]) :
    ∀ bs, (filesFold bundleEntries {}).entries ["bundle"] ≠ some (.file bs) := by
  induction bundleEntries with
  | nil =>
    intro bs h
    rw [show (filesFold [] {}).entries ["bundle"] = ({} : Arm64.FsState).entries ["bundle"] from rfl,
      emptyFsState_entries_of_ne_nil ["bundle"] (by simp)] at h; cases h
  | cons e es ih =>
    rcases e with ⟨p, ebs⟩; intro bs h
    rw [show filesFold ((p, ebs) :: es) {} = filesFold es (fileStep {} (p, ebs)) from rfl,
      filesFold_entries_eq_or es _ (by simp)] at h
    cases hes : (filesFold es {}).entries ["bundle"] with
    | some _ =>
      rw [hes, Option.some_or] at h
      exact ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) bs (hes.trans h)
    | none =>
      rw [hes, Option.none_or, fileStep_entries] at h
      obtain ⟨_, _, hnm⟩ := hb (p, ebs) (List.mem_cons_self ..)
      rw [ite_neg (by rw [hnm]; simp)] at h
      by_cases hanc : ["bundle"] ∈ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast
      · rw [ite_pos hanc] at h; cases h
      · rw [ite_neg hanc, emptyFsState_entries_of_ne_nil ["bundle"] (by simp)] at h; cases h

private theorem filesFold_directChild_len2_not_dir
    (bundleEntries : List (String × List (BitVec 8)))
    (hb : ∀ e ∈ bundleEntries, ∃ name, name ≠ "" ∧ Arm64.normalizePath e.1 = ["bundle", name])
    (name : String) : (filesFold bundleEntries {}).entries ["bundle", name] ≠ some .dir := by
  intro hdir
  obtain ⟨e, he, ⟨tl, htl⟩, hne⟩ := filesFold_dir_strict_prefix bundleEntries (by simp) hdir
  obtain ⟨_, _, hnm⟩ := hb e he; rw [hnm] at htl hne
  have hlen := congrArg List.length htl
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have htl0 : tl = [] := List.length_eq_zero_iff.mp (by omega)
  rw [htl0, List.append_nil] at htl; exact hne htl

private theorem dirsFold_partyDirs_bundle :
    (dirsFold (partyDirs ++ ["bundle"]) {}).entries ["bundle"] = some .dir ∧
    ∀ name : String, (dirsFold (partyDirs ++ ["bundle"]) {}).entries ["bundle", name] = none := by
  refine ⟨by decide, fun name => ?_⟩
  have hall_dirs : ∀ d ∈ partyDirs ++ ["bundle"],
      (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath d)).all
        (fun pref => pref.head? != some "bundle" || decide (pref.length = 1)) = true := by decide
  have hfold : ∀ (ds : List String) (fs : Arm64.FsState),
      (∀ d ∈ ds, (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath d)).all
        (fun pref => pref.head? != some "bundle" || decide (pref.length = 1)) = true) →
      (dirsFold ds fs).entries ["bundle", name] = fs.entries ["bundle", name] := by
    intro ds; induction ds with
    | nil => intro _ _; rfl
    | cons d ds ih =>
      intro fs hds; unfold dirsFold; rw [List.foldl_cons]
      change (dirsFold ds _).entries ["bundle", name] = fs.entries ["bundle", name]
      rw [ih _ (fun x hx => hds x (List.mem_cons_of_mem _ hx)), foldl_setEntry_entries, ite_neg]
      intro hm
      have hp := List.all_eq_true.mp (hds d (List.mem_cons_self ..)) ["bundle", name] hm; simp at hp
  rw [hfold (partyDirs ++ ["bundle"]) {} hall_dirs]
  exact emptyFsState_entries_of_ne_nil ["bundle", name] (by simp)

/-- Every bundle directory entry read by `readBundleV` (`RunCompose.bundleNames`) has size at most `fileCapBytes` (`2 ^ 21`). -/
def BundleReadWithinCap (d : String → Option (List (BitVec 8))) (dirName : String) : Prop :=
  ∀ name ∈ RunCompose.bundleNames, ((d (dirName ++ "/" ++ name)).getD []).length ≤ fileCapBytes

instance instDecidableBundleReadWithinCap (d : String → Option (List (BitVec 8))) (dirName : String) :
    Decidable (BundleReadWithinCap d dirName) := by
  unfold BundleReadWithinCap; infer_instance

private theorem readBundleV_eq_none_of_bundleFile_eq_none {F : FsFiles} {dir : List (BitVec 8)}
    {name : String} (hname : name ∈ RunCompose.bundleNames)
    (hnone : RunCompose.bundleFile F dir name = none) :
    RunCompose.readBundleV F dir 1#8 = none := by
  unfold RunCompose.readBundleV
  dsimp only [Bind.bind, Option.bind]
  simp only [RunCompose.bundleNames, List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl
  · simp [hnone]
  · cases RunCompose.bundleFile F dir "identity-key" with
    | none => rfl
    | some ikBs =>
      dsimp only
      cases exceptOpt (decodeIdentityKey ikBs) with
      | none => rfl
      | some _ => simp [hnone]
  · cases RunCompose.bundleFile F dir "identity-key" with
    | none => rfl
    | some ikBs =>
      dsimp only
      cases exceptOpt (decodeIdentityKey ikBs) with
      | none => rfl
      | some _ =>
        dsimp only
        cases RunCompose.bundleFile F dir "registration-id" with
        | none => rfl
        | some regBs =>
          dsimp only
          cases RunCompose.readU32LE regBs with
          | none => rfl
          | some _ => simp [hnone]
  · cases RunCompose.bundleFile F dir "identity-key" with
    | none => rfl
    | some ikBs =>
      dsimp only
      cases exceptOpt (decodeIdentityKey ikBs) with
      | none => rfl
      | some _ =>
        dsimp only
        cases RunCompose.bundleFile F dir "registration-id" with
        | none => rfl
        | some regBs =>
          dsimp only
          cases RunCompose.readU32LE regBs with
          | none => rfl
          | some _ =>
            dsimp only
            cases RunCompose.bundleFile F dir "signed-pre-key" with
            | none => rfl
            | some spkBs =>
              dsimp only
              cases splitSigned spkBs with
              | none => rfl
              | some _ => simp [hnone]
  · cases RunCompose.bundleFile F dir "identity-key" with
    | none => rfl
    | some ikBs =>
      dsimp only
      cases exceptOpt (decodeIdentityKey ikBs) with
      | none => rfl
      | some _ =>
        dsimp only
        cases RunCompose.bundleFile F dir "registration-id" with
        | none => rfl
        | some regBs =>
          dsimp only
          cases RunCompose.readU32LE regBs with
          | none => rfl
          | some _ =>
            dsimp only
            cases RunCompose.bundleFile F dir "signed-pre-key" with
            | none => rfl
            | some spkBs =>
              dsimp only
              cases splitSigned spkBs with
              | none => rfl
              | some _ =>
                dsimp only
                cases RunCompose.bundleFile F dir "kyber-pre-key" with
                | none => rfl
                | some kpkBs =>
                  dsimp only
                  cases splitSigned kpkBs with
                  | none => rfl
                  | some _ => simp [hnone]

theorem bundleFile_runFiles_of_directChild_general
    {i : Inputs} {bundleEntries : List (String × List (BitVec 8))} {coins : List (BitVec 8)}
    {d : String → Option (List (BitVec 8))} (hdirs : i.dirs = partyDirs ++ ["bundle"])
    (hb : ∀ e ∈ bundleEntries, ∃ name, name ≠ "" ∧ Arm64.normalizePath e.1 = ["bundle", name])
    (hd_scrub : ∀ p, (Arm64.normalizePath p).head? = some "bundle" → d p = none)
    (h_filesOf : ∀ p, Arm64.normalizePath p ∉ stdioPaths.map Arm64.normalizePath →
      filesOf i.files p = (filesOf (bundleEntries ++ [("coins", coins)]) p).or (d p)) :
    ∀ name ∈ RunCompose.bundleNames,
      RunCompose.bundleFile (RunCompose.runFiles i) (bytesOfString "bundle") name =
        if ((filesOf bundleEntries ("bundle/" ++ name)).getD []).length ≤ fileCapBytes then
          some ((filesOf bundleEntries ("bundle/" ++ name)).getD [])
        else
          none := by
  have hentries_eq : ∀ q : Arm64.FsPath, q.head? = some "bundle" →
      (filesFold i.files {}).entries q = (filesFold bundleEntries {}).entries q :=
    initFsState_entries_eq_of_filesOf_eq (P := fun q => q.head? = some "bundle")
      (fun q hq h => by rw [h] at hq; cases hq) (fun _ hq => head_bundle_not_stdio hq)
      (fun q _ hq hpre => by rcases hpre with ⟨_, rfl⟩; cases q with | nil => cases hq | cons _ _ => exact hq)
      (filesOf_bundle_eq_of_directChild hd_scrub h_filesOf)
  have ⟨hdirs_bun, hdirs_child⟩ := dirsFold_partyDirs_bundle
  have hrf_bundle : RunCompose.runFiles i "bundle" = some .dir := by
    have hnorm : Arm64.normalizePath "bundle" = ["bundle"] := by decide
    unfold RunCompose.runFiles
    rw [files_eq_entries, hnorm, ite_neg (by decide),
      initFsState_entries (cliInputs i) ["bundle"] (head_bundle_not_stdio rfl)]
    change (filesFold i.files (dirsFold i.dirs {})).entries ["bundle"] = some .dir
    rw [filesFold_entries_eq_or i.files _ (by simp), hentries_eq ["bundle"] rfl, hdirs, hdirs_bun]
    cases hfb : (filesFold bundleEntries {}).entries ["bundle"] with
    | none => rfl
    | some entry =>
      cases entry with
      | dir => rfl
      | file bs => exact absurd hfb (filesFold_directChild_bundle_not_file bundleEntries hb bs)
  have hchild : ∀ (name full : String), full = "bundle/" ++ name →
      ((RunCompose.bundlePath (bytesOfString "bundle") name).map fun x => Char.ofNat x.toNat) =
        full.toList →
      ancestors full = ["bundle"] → Arm64.normalizePath full = ["bundle", name] →
      RunCompose.bundleFile (RunCompose.runFiles i) (bytesOfString "bundle") name =
        if ((filesOf bundleEntries full).getD []).length ≤ fileCapBytes then
          some ((filesOf bundleEntries full).getD [])
        else
          none := by
    intro name full _ hp hanc hnorm
    have hp' : pathStr (RunCompose.bundlePath (bytesOfString "bundle") name) = full :=
      String.toList_inj.mp (by unfold pathStr; rw [String.toList_ofList]; exact hp)
    have hblock : blockingAncestorF (RunCompose.runFiles i) full = none := by
      unfold blockingAncestorF; rw [hanc, List.find?_cons, hrf_bundle]; rfl
    have hns : Arm64.normalizePath full ∉ stdioPaths.map Arm64.normalizePath := by
      rw [hnorm]; exact head_bundle_not_stdio rfl
    have hrf_full : RunCompose.runFiles i full =
        (filesFold bundleEntries {}).entries ["bundle", name] := by
      unfold RunCompose.runFiles
      rw [files_eq_entries, ite_neg (by rw [hnorm]; simp),
        initFsState_entries (cliInputs i) (Arm64.normalizePath full) hns]
      change (filesFold i.files (dirsFold i.dirs {})).entries (Arm64.normalizePath full) = _
      rw [hnorm, filesFold_entries_eq_or i.files _ (by simp),
        hentries_eq ["bundle", name] rfl, hdirs, hdirs_child name, Option.or_none]
    have hfo_full := filesOf_eq_match_filesFold bundleEntries (by rw [hnorm]; simp) hns
    rw [hnorm] at hfo_full; unfold RunCompose.bundleFile
    show exceptOpt (cliRd (RunCompose.runFiles i)
      (RunCompose.bundlePath (bytesOfString "bundle") name)) = _
    unfold cliRd readViewF; rw [hp', hblock]; dsimp only; rw [hrf_full, hfo_full]
    cases hfb : (filesFold bundleEntries {}).entries ["bundle", name] with
    | none => simp [exceptOpt, fileCapBytes]
    | some entry =>
      cases entry with
      | file bs =>
        dsimp only [Option.getD]
        by_cases hc : bs.length ≤ fileCapBytes <;> simp [hc, exceptOpt]
      | dir => exact absurd hfb (filesFold_directChild_len2_not_dir bundleEntries hb name)
  intro name hname
  simp only [RunCompose.bundleNames, List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl <;>
    exact hchild _ ("bundle/" ++ _) rfl
      (by unfold RunCompose.bundlePath; rw [InitS0.utf8_eq_flatMap]; decide) (by decide) (by decide)

theorem bundleFile_runFiles_of_directChild_minimal
    {i : Inputs} {bundleEntries : List (String × List (BitVec 8))} {coins : List (BitVec 8)}
    {d : String → Option (List (BitVec 8))} (hdirs : i.dirs = partyDirs ++ ["bundle"])
    (hb : ∀ e ∈ bundleEntries, ∃ name, name ≠ "" ∧ Arm64.normalizePath e.1 = ["bundle", name])
    (hd_scrub : ∀ p, (Arm64.normalizePath p).head? = some "bundle" → d p = none)
    (h_filesOf : ∀ p, Arm64.normalizePath p ∉ stdioPaths.map Arm64.normalizePath →
      filesOf i.files p = (filesOf (bundleEntries ++ [("coins", coins)]) p).or (d p))
    (hcap : BundleReadWithinCap (filesOf bundleEntries) "bundle") :
    ∀ name ∈ RunCompose.bundleNames,
      RunCompose.bundleFile (RunCompose.runFiles i) (bytesOfString "bundle") name =
        some ((filesOf bundleEntries ("bundle/" ++ name)).getD []) := by
  intro name hname
  have hc := hcap name hname
  rw [show ("bundle" ++ "/" : String) = "bundle/" by decide] at hc
  rw [bundleFile_runFiles_of_directChild_general hdirs hb hd_scrub h_filesOf name hname]
  simp only [hc, ↓reduceIte]

theorem readBundleV_runFiles_eq_none_of_not_withinCap
    {i : Inputs} {bundleEntries : List (String × List (BitVec 8))} {coins : List (BitVec 8)}
    {d : String → Option (List (BitVec 8))} (hdirs : i.dirs = partyDirs ++ ["bundle"])
    (hb : ∀ e ∈ bundleEntries, ∃ name, name ≠ "" ∧ Arm64.normalizePath e.1 = ["bundle", name])
    (hd_scrub : ∀ p, (Arm64.normalizePath p).head? = some "bundle" → d p = none)
    (h_filesOf : ∀ p, p ∉ stdioPaths →
      filesOf i.files p = (filesOf (bundleEntries ++ [("coins", coins)]) p).or (d p))
    (hover : ¬ BundleReadWithinCap (filesOf bundleEntries) "bundle") :
    RunCompose.readBundleV (RunCompose.runFiles i) (bytesOfString "bundle") 1#8 = none := by
  have hgen := bundleFile_runFiles_of_directChild_general hdirs hb hd_scrub
    (fun p hp => h_filesOf p (fun hm => hp (List.mem_map_of_mem hm)))
  unfold BundleReadWithinCap at hover
  push Not at hover
  obtain ⟨name, hname, hgt⟩ := hover
  rw [show ("bundle" ++ "/" : String) = "bundle/" by decide] at hgt
  have hnone : RunCompose.bundleFile (RunCompose.runFiles i) (bytesOfString "bundle") name = none := by
    rw [hgen name hname]
    simp only [Nat.not_le.mpr hgt, ↓reduceIte]
  exact readBundleV_eq_none_of_bundleFile_eq_none hname hnone

theorem readBundleV_runFiles_eq_some_iff_bundleE
    {i : Inputs} {bundleEntries : List (String × List (BitVec 8))} {coins : List (BitVec 8)}
    {d : String → Option (List (BitVec 8))} (hdirs : i.dirs = partyDirs ++ ["bundle"])
    (hb : ∀ e ∈ bundleEntries, ∃ name, name ≠ "" ∧ Arm64.normalizePath e.1 = ["bundle", name])
    (hd_scrub : ∀ p, (Arm64.normalizePath p).head? = some "bundle" → d p = none)
    (h_filesOf : ∀ p, p ∉ stdioPaths →
      filesOf i.files p = (filesOf (bundleEntries ++ [("coins", coins)]) p).or (d p))
    (hcap : BundleReadWithinCap (filesOf bundleEntries) "bundle") :
    (RunCompose.readBundleV (RunCompose.runFiles i) (bytesOfString "bundle") 1#8 = none ↔
      parseBundleDir (filesOf bundleEntries) "bundle" = none) ∧
    (∀ bv, RunCompose.readBundleV (RunCompose.runFiles i) (bytesOfString "bundle") 1#8 = some bv →
      ∃! b_e : PreKeyBundleFields, bv = RunRefine.bundleVE b_e ∧ RunProofs.bundleEOf? bv = some b_e ∧
        parseBundleDir (filesOf bundleEntries) "bundle" = some (publicBundleOf b_e)) ∧
    (∀ pb, parseBundleDir (filesOf bundleEntries) "bundle" = some pb →
      ∃ b_e : PreKeyBundleFields, publicBundleOf b_e = pb ∧
        RunCompose.readBundleV (RunCompose.runFiles i) (bytesOfString "bundle") 1#8 =
          some (RunRefine.bundleVE b_e) ∧
        publicBundleBytes pb = b_e.bytes ∧
        (publicBundleBytes pb).length = 1813) := by
  have hF := bundleFile_runFiles_of_directChild_minimal hdirs hb hd_scrub
    (fun p hp => h_filesOf p (fun hm => hp (List.mem_map_of_mem hm))) hcap
  exact ⟨readBundleV_eq_none_iff hF, (readBundleV_eq_some_iff_bundleE hF).1,
    (readBundleV_eq_some_iff_bundleE hF).2⟩

theorem readBundleV_runFiles_eq_none_of_parseBundleDir_eq_none
    {i : Inputs} {bundleEntries : List (String × List (BitVec 8))} {coins : List (BitVec 8)}
    {d : String → Option (List (BitVec 8))} (hdirs : i.dirs = partyDirs ++ ["bundle"])
    (hb : ∀ e ∈ bundleEntries, ∃ name, name ≠ "" ∧ Arm64.normalizePath e.1 = ["bundle", name])
    (hd_scrub : ∀ p, (Arm64.normalizePath p).head? = some "bundle" → d p = none)
    (h_filesOf : ∀ p, p ∉ stdioPaths →
      filesOf i.files p = (filesOf (bundleEntries ++ [("coins", coins)]) p).or (d p))
    (hp : parseBundleDir (filesOf bundleEntries) "bundle" = none) :
    RunCompose.readBundleV (RunCompose.runFiles i) (bytesOfString "bundle") 1#8 = none := by
  by_cases hcap : BundleReadWithinCap (filesOf bundleEntries) "bundle"
  · exact (readBundleV_runFiles_eq_some_iff_bundleE hdirs hb hd_scrub h_filesOf hcap).1.mpr hp
  · exact readBundleV_runFiles_eq_none_of_not_withinCap hdirs hb hd_scrub h_filesOf hcap

/-! ## Arbitrary-Input `InitOk₀`, `initDef`, and Post-`observe` Agreement -/

def NonBundleCoinsStdio (q : Arm64.FsPath) : Prop :=
  q ≠ [] ∧ q.head? ≠ some "bundle" ∧ q.head? ≠ some "coins" ∧ q ∉ stdioPaths.map Arm64.normalizePath

theorem nonBundleCoinsStdio_upward {q q' : Arm64.FsPath}
    (hq : NonBundleCoinsStdio q) (hpre : q <+: q') : NonBundleCoinsStdio q' := by
  obtain ⟨hne, hbun, hcoins, hstdio⟩ := hq; rcases hpre with ⟨tl, rfl⟩
  cases q with
  | nil => exact absurd rfl hne
  | cons s rest =>
    refine ⟨by simp, hbun, hcoins, ?_⟩; rw [stdioPaths_norm_eq] at hstdio ⊢; intro hm
    have hlen : ((s :: rest) ++ tl).length = 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h <;> (rw [h]; rfl)
    rw [List.length_append, List.length_cons] at hlen
    have hrest : rest = [] := List.length_eq_zero_iff.mp (by omega)
    have htl : tl = [] := List.length_eq_zero_iff.mp (by omega)
    subst hrest htl; rw [List.append_nil] at hm; exact hstdio hm

theorem runFiles_eq_of_nonBundleCoins {i₁ i₂ : Inputs} (hdirs : i₁.dirs = i₂.dirs)
    (hag : ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) →
      filesOf i₁.files p = filesOf i₂.files p) :
    ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) →
      RunCompose.runFiles i₁ p = RunCompose.runFiles i₂ p := by
  have hentries := initFsState_entries_eq_of_filesOf_eq
    (P := NonBundleCoinsStdio) (fun _ h => h.1) (fun _ h => h.2.2.2)
    (fun _ _ h hpre => nonBundleCoinsStdio_upward h hpre) hag
  intro p hp
  have hemp : ¬ (Arm64.normalizePath p).isEmpty = true := by
    rw [List.isEmpty_eq_false_iff.mpr hp.1]; decide
  unfold RunCompose.runFiles
  rw [files_eq_entries, files_eq_entries, ite_neg hemp, ite_neg hemp,
    initFsState_entries (cliInputs i₁) (Arm64.normalizePath p) hp.2.2.2,
    initFsState_entries (cliInputs i₂) (Arm64.normalizePath p) hp.2.2.2]
  change (filesFold i₁.files (dirsFold i₁.dirs {})).entries (Arm64.normalizePath p) =
    (filesFold i₂.files (dirsFold i₂.dirs {})).entries (Arm64.normalizePath p)
  rw [filesFold_entries_eq_or i₁.files _ hp.1, filesFold_entries_eq_or i₂.files _ hp.1,
    hentries (Arm64.normalizePath p) hp, hdirs]

theorem filesOf_append_writes_eq_of_nonBundleCoins
    {f₁ f₂ writes : List (String × List (BitVec 8))}
    (hag : ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) →
      filesOf f₁ p = filesOf f₂ p) :
    ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) →
      filesOf (f₁ ++ writes) p = filesOf (f₂ ++ writes) p := by
  have hentries := initFsState_entries_eq_of_filesOf_eq
    (P := NonBundleCoinsStdio) (fun _ h => h.1) (fun _ h => h.2.2.2)
    (fun _ _ h hpre => nonBundleCoinsStdio_upward h hpre) hag
  intro p hp
  rw [filesOf_eq_match_filesFold (f₁ ++ writes) hp.1 hp.2.2.2,
    filesOf_eq_match_filesFold (f₂ ++ writes) hp.1 hp.2.2.2]
  have happ : ∀ g : List (String × List (BitVec 8)),
      filesFold (g ++ writes) {} = filesFold writes (filesFold g {}) := fun _ => List.foldl_append
  rw [happ f₁, happ f₂,
    filesFold_entries_eq_or writes (filesFold f₁ {}) hp.1,
    filesFold_entries_eq_or writes (filesFold f₂ {}) hp.1,
    hentries (Arm64.normalizePath p) hp]

private theorem cliRd_eq_of_agree {F₁ F₂ : FsFiles} {bs : List (BitVec 8)}
    (hp : F₁ (pathStr bs) = F₂ (pathStr bs))
    (ha : ∀ q ∈ ancestors (pathStr bs), F₁ q = F₂ q) :
    cliIo.rd F₁ bs = cliIo.rd F₂ bs := by
  have hblk : blockingAncestorF F₁ (pathStr bs) = blockingAncestorF F₂ (pathStr bs) := by
    unfold blockingAncestorF; rw [List.find?_congr (fun q hq => by rw [ha q hq])]
    generalize hf : List.find? _ (ancestors (pathStr bs)) = r
    cases r with
    | none => rfl
    | some q => exact congrArg some (ha q (List.mem_of_find?_eq_some hf))
  show cliRd F₁ bs = cliRd F₂ bs; unfold cliRd readViewF; rw [hblk, hp]

private theorem nonBundleCoins_of_head {p seg : String}
    (hhd : (Arm64.normalizePath p).head? = some seg) (hb : seg ≠ "bundle") (hc : seg ≠ "coins")
    (hs1 : seg ≠ "<stdin>") (hs2 : seg ≠ "<stdout>") (hs3 : seg ≠ "<stderr>") :
    NonBundleCoinsStdio (Arm64.normalizePath p) := by
  refine ⟨?_, ?_, ?_, not_stdio_of_head ?_ ?_ ?_⟩
  · intro h; rw [h] at hhd; cases hhd
  · rw [hhd]; exact Option.some.inj.mt hb
  · rw [hhd]; exact Option.some.inj.mt hc
  · rw [hhd]; exact Option.some.inj.mt hs1
  · rw [hhd]; exact Option.some.inj.mt hs2
  · rw [hhd]; exact Option.some.inj.mt hs3

private theorem store_paths_nonBundleCoins (P : Party) :
    NonBundleCoinsStdio (Arm64.normalizePath (pathStr (utf8 "address"))) ∧
    (∀ q ∈ ancestors (pathStr (utf8 "address")), NonBundleCoinsStdio (Arm64.normalizePath q)) ∧
    NonBundleCoinsStdio (Arm64.normalizePath (pathStr (utf8 "identity-key-pair"))) ∧
    (∀ q ∈ ancestors (pathStr (utf8 "identity-key-pair")),
      NonBundleCoinsStdio (Arm64.normalizePath q)) ∧
    NonBundleCoinsStdio (Arm64.normalizePath (pathStr (utf8 "registration-id"))) ∧
    (∀ q ∈ ancestors (pathStr (utf8 "registration-id")),
      NonBundleCoinsStdio (Arm64.normalizePath q)) ∧
    NonBundleCoinsStdio
      (Arm64.normalizePath (pathStr (pathOf (utf8 "identities") (RunRefine.addrValE P).name))) ∧
    (∀ q ∈ ancestors (pathStr (pathOf (utf8 "identities") (RunRefine.addrValE P).name)),
      NonBundleCoinsStdio (Arm64.normalizePath q)) ∧
    NonBundleCoinsStdio
      (Arm64.normalizePath (pathStr (pathOf (utf8 "sessions") (addressText (RunRefine.addrValE P))))) ∧
    (∀ q ∈ ancestors (pathStr (pathOf (utf8 "sessions") (addressText (RunRefine.addrValE P)))),
      NonBundleCoinsStdio (Arm64.normalizePath q)) := by
  have hp_addr : pathStr (utf8 "address") = "address" :=
    String.toList_inj.mp (by unfold pathStr; rw [String.toList_ofList, InitS0.utf8_eq_flatMap]; decide)
  have hp_ikp : pathStr (utf8 "identity-key-pair") = "identity-key-pair" :=
    String.toList_inj.mp (by unfold pathStr; rw [String.toList_ofList, InitS0.utf8_eq_flatMap]; decide)
  have hp_reg : pathStr (utf8 "registration-id") = "registration-id" :=
    String.toList_inj.mp (by unfold pathStr; rw [String.toList_ofList, InitS0.utf8_eq_flatMap]; decide)
  have hp_id : pathStr (pathOf (utf8 "identities") (RunRefine.addrValE P).name) =
      "identities/" ++ partyAddressName P := by
    cases P <;> exact String.toList_inj.mp (by
      unfold pathStr pathOf RunRefine.addrValE partyAddressName
      simp only [String.toList_ofList, InitS0.utf8_eq_flatMap]; decide)
  have hp_sess : pathStr (pathOf (utf8 "sessions") (addressText (RunRefine.addrValE P))) =
      "sessions/" ++ (partyAddress P).text := by
    cases P <;> exact String.toList_inj.mp (by
      unfold pathStr pathOf addressText decimalText RunRefine.addrValE partyAddress Address.text partyAddressName
      simp only [String.toList_ofList, InitS0.utf8_eq_flatMap]; decide)
  have ha_addr : ancestors "address" = [] := by decide
  have ha_ikp : ancestors "identity-key-pair" = [] := by decide
  have ha_reg : ancestors "registration-id" = [] := by decide
  have ha_id : ancestors ("identities/" ++ partyAddressName P) = ["identities"] := by cases P <;> decide
  have ha_sess : ancestors ("sessions/" ++ (partyAddress P).text) = ["sessions"] := by cases P <;> decide
  rw [hp_addr, hp_ikp, hp_reg, hp_id, hp_sess, ha_addr, ha_ikp, ha_reg, ha_id, ha_sess]
  exact ⟨nonBundleCoins_of_head (seg := "address") (by decide)
           (by decide) (by decide) (by decide) (by decide) (by decide),
         fun _ hq => (by cases hq),
         nonBundleCoins_of_head (seg := "identity-key-pair") (by decide)
           (by decide) (by decide) (by decide) (by decide) (by decide),
         fun _ hq => (by cases hq),
         nonBundleCoins_of_head (seg := "registration-id") (by decide)
           (by decide) (by decide) (by decide) (by decide) (by decide),
         fun _ hq => (by cases hq),
         nonBundleCoins_of_head (seg := "identities") (by cases P <;> decide)
           (by decide) (by decide) (by decide) (by decide) (by decide),
         fun q hq => by
           rw [List.mem_singleton] at hq; subst hq
           exact nonBundleCoins_of_head (seg := "identities") (by decide)
             (by decide) (by decide) (by decide) (by decide) (by decide),
         nonBundleCoins_of_head (seg := "sessions") (by cases P <;> decide)
           (by decide) (by decide) (by decide) (by decide) (by decide),
         fun q hq => by
           rw [List.mem_singleton] at hq; subst hq
           exact nonBundleCoins_of_head (seg := "sessions") (by decide)
             (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem initOk₀_iff_of_nonBundleCoins {W : PEParams} {F₁ F₂ : FsFiles} (P : Party) (me : AddrVal)
    (hF : ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) → F₁ p = F₂ p) :
    RunProofs.InitOk₀ W F₁ (RunRefine.addrValE P) me ↔
      RunProofs.InitOk₀ W F₂ (RunRefine.addrValE P) me := by
  obtain ⟨_, _, hikp, hikpA, _, _, hid, hidA, hsess, hsessA⟩ := store_paths_nonBundleCoins P
  have hget_ikp : StoresGhost.opened.identity.own.get cliIo.rd F₁ (utf8 "identity-key-pair") =
      StoresGhost.opened.identity.own.get cliIo.rd F₂ (utf8 "identity-key-pair") :=
    cliRd_eq_of_agree (hF _ hikp) (fun q hq => hF q (hikpA q hq))
  have hget_id : StoresGhost.opened.identity.peers.get cliIo.rd F₁ (RunRefine.addrValE P).name =
      StoresGhost.opened.identity.peers.get cliIo.rd F₂ (RunRefine.addrValE P).name :=
    cliRd_eq_of_agree (hF _ hid) (fun q hq => hF q (hidA q hq))
  have hget_sess :
      StoresGhost.opened.sessions.get cliIo.rd F₁ (addressText (RunRefine.addrValE P)) =
      StoresGhost.opened.sessions.get cliIo.rd F₂ (addressText (RunRefine.addrValE P)) :=
    cliRd_eq_of_agree (hF _ hsess) (fun q hq => hF q (hsessA q hq))
  have hkp : StoresGhost.opened.identity.keyPair cliIo.rd F₁ =
      StoresGhost.opened.identity.keyPair cliIo.rd F₂ := by unfold IdGhost.keyPair; rw [hget_ikp]
  refine ⟨fun h => ⟨h.nameLt, h.textLt, h.sessPathOk, h.idPathOk, h.sessPathLt, h.idPathLt,
            fun bs hbs => h.keyPairLt bs (hget_ikp.trans hbs),
            hget_id ▸ h.idGet, hget_sess.symm.trans h.noSession, h.distinctAcct,
            fun kp hkp' => h.idPairDerived kp (hkp.trans hkp')⟩,
          fun h => ⟨h.nameLt, h.textLt, h.sessPathOk, h.idPathOk, h.sessPathLt, h.idPathLt,
            fun bs hbs => h.keyPairLt bs (hget_ikp.symm.trans hbs),
            hget_id.symm ▸ h.idGet, hget_sess.trans h.noSession, h.distinctAcct,
            fun kp hkp' => h.idPairDerived kp (hkp.symm.trans hkp')⟩⟩

theorem initDef_eq_of_nonBundleCoins (X : UnreachedPqxdhPrimitives) (W : PEParams) {F₁ F₂ : FsFiles}
    (P : Party) (me : AddrVal) (bv : BundleV) (coins : List (BitVec 8))
    (hF : ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) → F₁ p = F₂ p) :
    StoresGhost.opened.identity.own.get cliIo.rd F₁ (utf8 "address") =
      StoresGhost.opened.identity.own.get cliIo.rd F₂ (utf8 "address") ∧
    RunProofs.initDef X W F₁ (RunRefine.addrValE P) me bv coins =
      RunProofs.initDef X W F₂ (RunRefine.addrValE P) me bv coins := by
  obtain ⟨haddr, haddrA, hikp, hikpA, hreg, hregA, hid, hidA, _, _⟩ := store_paths_nonBundleCoins P
  have hrd_addr : StoresGhost.opened.identity.own.get cliIo.rd F₁ (utf8 "address") =
      StoresGhost.opened.identity.own.get cliIo.rd F₂ (utf8 "address") :=
    cliRd_eq_of_agree (hF _ haddr) (fun q hq => hF q (haddrA q hq))
  have hrd_ikp : StoresGhost.opened.identity.own.get cliIo.rd F₁ (utf8 "identity-key-pair") =
      StoresGhost.opened.identity.own.get cliIo.rd F₂ (utf8 "identity-key-pair") :=
    cliRd_eq_of_agree (hF _ hikp) (fun q hq => hF q (hikpA q hq))
  have hrd_reg : StoresGhost.opened.identity.own.get cliIo.rd F₁ (utf8 "registration-id") =
      StoresGhost.opened.identity.own.get cliIo.rd F₂ (utf8 "registration-id") :=
    cliRd_eq_of_agree (hF _ hreg) (fun q hq => hF q (hregA q hq))
  have hrd_id : StoresGhost.opened.identity.peers.get cliIo.rd F₁ (RunRefine.addrValE P).name =
      StoresGhost.opened.identity.peers.get cliIo.rd F₂ (RunRefine.addrValE P).name :=
    cliRd_eq_of_agree (hF _ hid) (fun q hq => hF q (hidA q hq))
  have hpeer : StoresGhost.opened.identity.peer cliIo.rd F₁ (RunRefine.addrValE P) =
      StoresGhost.opened.identity.peer cliIo.rd F₂ (RunRefine.addrValE P) := by
    unfold IdGhost.peer; rw [hrd_id]
  have htr : ∀ k, StoresGhost.opened.identity.trusted cliIo.rd F₁ (RunRefine.addrValE P) k =
      StoresGhost.opened.identity.trusted cliIo.rd F₂ (RunRefine.addrValE P) k := fun _ => by
    unfold IdGhost.trusted; rw [hpeer]
  have hsave : ∀ k, StoresGhost.opened.identity.saveUpd cliIo.rd F₁ (RunRefine.addrValE P) k =
      StoresGhost.opened.identity.saveUpd cliIo.rd F₂ (RunRefine.addrValE P) k := fun _ => by
    unfold IdGhost.saveUpd; rw [hpeer]
  have hkp : StoresGhost.opened.identity.keyPair cliIo.rd F₁ =
      StoresGhost.opened.identity.keyPair cliIo.rd F₂ := by
    unfold IdGhost.keyPair; rw [hrd_ikp]
  have hregG : StoresGhost.opened.identity.regId cliIo.rd F₁ =
      StoresGhost.opened.identity.regId cliIo.rd F₂ := by
    unfold IdGhost.regId; rw [hrd_reg]
  refine ⟨hrd_addr, ?_⟩; unfold RunProofs.initDef
  cases RunProofs.bundleEOf? bv with
  | none => rfl
  | some _ => simp only [htr, hkp, hregG, hsave]

theorem initOk₀_and_initDef_of_nonBundleCoins
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) (b_e : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) {i : Inputs}
    (hdirs : i.dirs = partyDirs ++ ["bundle"])
    (hag : ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) →
      filesOf i.files p = filesOf (encodeDir W st) p)
    (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none) :
    RunProofs.InitOk₀ W (RunCompose.runFiles i)
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) ∧
    RunProofs.initDef X W (RunCompose.runFiles i)
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party)
      (RunRefine.bundleVE b_e) t.toList =
      RunProofs.initDef X W (RunCompose.runFiles (pqInitInputs W st b_e t))
        (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party)
        (RunRefine.bundleVE b_e) t.toList ∧
    (∀ (writes : List (String × List (BitVec 8))) (p : String),
      NonBundleCoinsStdio (Arm64.normalizePath p) →
      filesOf (i.files ++ writes) p = filesOf (encodeDir W st ++ writes) p) := by
  have hpq_ag : ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) →
      filesOf (pqInitInputs W st b_e t).files p = filesOf (encodeDir W st) p := by
    intro p hp
    rw [filesOf_eq_match_filesFold _ hp.1 hp.2.2.2, filesOf_eq_match_filesFold _ hp.1 hp.2.2.2,
      show (pqInitInputs W st b_e t).files =
        encodeDir W st ++ ((publicBundleOf b_e).files bundleDir ++ [(coinsFile, t.toList)]) by
        simp [pqInitInputs, pqInputs, List.append_assoc],
      show filesFold (encodeDir W st ++
        ((publicBundleOf b_e).files bundleDir ++ [(coinsFile, t.toList)])) {} =
        filesFold ((publicBundleOf b_e).files bundleDir ++ [(coinsFile, t.toList)])
          (filesFold (encodeDir W st) {}) from List.foldl_append,
      filesFold_entries_eq_or _ _ hp.1]
    have htail_none :
        (filesFold ((publicBundleOf b_e).files bundleDir ++ [(coinsFile, t.toList)]) {}).entries
          (Arm64.normalizePath p) = none := by
      by_contra hne; obtain ⟨e, he, ⟨tl, htl⟩⟩ := filesFold_support_prefix _ hp.1 hne
      cases hq : Arm64.normalizePath p with
      | nil => exact hp.1 hq
      | cons s rest =>
        rw [hq, List.cons_append] at htl
        have hhead : (Arm64.normalizePath e.1).head? = some s := by rw [← htl]; rfl
        rcases List.mem_append.mp he with hbun_mem | hcoins_mem
        · have hb_hd : (Arm64.normalizePath e.1).head? = some "bundle" := by
            simp only [publicBundleOf, PublicBundle.files, bundleDir, List.mem_append,
              List.mem_cons, List.not_mem_nil, or_false] at hbun_mem
            rcases hbun_mem with (rfl | rfl | rfl | rfl) | h5
            · dsimp only; decide
            · dsimp only; decide
            · dsimp only; decide
            · dsimp only; decide
            · cases hopk : b_e.opk with
              | none => rw [hopk] at h5; cases h5
              | some opk =>
                rcases opk with ⟨_, _⟩; rw [hopk] at h5
                simp only [Option.map_some, List.mem_singleton] at h5; subst h5; dsimp only; decide
          exact hp.2.1 (by rw [hq, List.head?_cons, Option.some.inj (hhead.symm.trans hb_hd)])
        · rw [List.mem_singleton] at hcoins_mem; subst hcoins_mem
          have hc_hd : (Arm64.normalizePath coinsFile).head? = some "coins" := by decide
          exact hp.2.2.1 (by rw [hq, List.head?_cons, Option.some.inj (hhead.symm.trans hc_hd)])
    rw [htail_none, Option.none_or]
  have hrf : ∀ p : String, NonBundleCoinsStdio (Arm64.normalizePath p) →
      RunCompose.runFiles i p = RunCompose.runFiles (pqInitInputs W st b_e t) p :=
    runFiles_eq_of_nonBundleCoins hdirs (fun p hp => (hag p hp).trans (hpq_ag p hp).symm)
  exact ⟨(initOk₀_iff_of_nonBundleCoins st.party.other (RunRefine.addrValE st.party) hrf).mpr
           (InitS0.initOk₀_pqInit_proof W st b_e t hwf hs),
         (initDef_eq_of_nonBundleCoins X W st.party.other (RunRefine.addrValE st.party)
           (RunRefine.bundleVE b_e) t.toList hrf).2,
         fun _ => filesOf_append_writes_eq_of_nonBundleCoins hag⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Parity
