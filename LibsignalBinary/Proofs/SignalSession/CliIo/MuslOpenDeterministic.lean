/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Process.FsLemmas
public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import LibsignalBinary.Specifications.SignalSession.CliRun
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose

/-!
# Deterministic `musl` `open(..., O_CLOEXEC)` Contract on `PathOk` Paths

Proves path-component invariants and deterministic `open` classification over `muslSysPlacedLib`:
1. On any `PathOk p = true` path with `p.toList.length < PATH_MAX` and Latin-1/ASCII code points,
   `ValidRelCPath p` holds, `normalizePath p = (pathComps p).map String.ofList ≠ []`, and
   `Arm64.ancestorWalkErrno? fs p` agrees with `CliRun.blockingAncestor? fs p`.
2. `muslOpenRdonlyDet_block_ok` / `muslOpenRdonlyDet_ok` classify `open(cstr, O_CLOEXEC_W32)` into
   `classifyOpenRdonly s0.fs path` across all VFS states (`ENOTDIR = 20`, `ENOENT = 2`, `EMFILE = 24`,
   or `.ok fd (.localDir | .localFile)` with `3 ≤ fd.toNat < 1024`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic

open Arm64
open Arm64.Obj
open Arm64.Process
open ProofLib
open ProofLib.StdStartup
open VerifiedLibraries.Musl (
  ValidRelCPath MuslSysPlacement muslSysPlacedLib muslSysMpl
)
open CryptoVerification.SignalSession (
  pathComps isUnmodelledPathComponent PathOk ancestors blockingAncestor? stdioPaths
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  OpenatLocalOutcome OpenatLocalExecSpec
  muslOpenNoCreatCloexecLocalExecSpec
  muslOpenNoCreatCloexecLocalExec_block_ok
  muslOpenNoCreatCloexecLocalExec_ok
  execOpenat_rdonly_cloexec_dir
)

/-! ## 1. `List.splitOn '/'` and `PathOk` Component Invariants -/

/-- Well-formed single path component from `PathOk`: non-empty, not `"."` or `".."`, NUL-free,
    and `'/'`-free. -/
def GoodComp (c : List Char) : Prop :=
  c ≠ [] ∧ c ≠ ['.'] ∧ c ≠ ['.', '.'] ∧ '\x00' ∉ c ∧ '/' ∉ c

private theorem not_mem_of_contains_false :
    ∀ {x : Char} {cs : List Char}, cs.contains x = false → x ∉ cs
  | _, [], _, hm => absurd hm List.not_mem_nil
  | x, c :: cs, h, hm => by
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    rcases List.mem_cons.mp hm with rfl | hrest
    · exact h.1 rfl
    · exact not_mem_of_contains_false h.2 hrest

theorem slash_not_mem_of_mem_splitOn :
    ∀ (cs : List Char) (c : List Char), c ∈ cs.splitOn '/' → '/' ∉ c
  | [], c, hc => by
    rw [List.splitOn_nil] at hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact List.not_mem_nil
  | x :: xs, c, hc => by
    rw [List.splitOn_cons_eq_ite_modifyHead] at hc
    by_cases hx : (x == '/') = true
    · simp only [hx, ↓reduceIte] at hc
      rcases List.mem_cons.mp hc with rfl | htl
      · exact List.not_mem_nil
      · exact slash_not_mem_of_mem_splitOn xs c htl
    · rw [Bool.not_eq_true] at hx
      have hne : x ≠ '/' := beq_eq_false_iff_ne.mp hx
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at hc
      rcases hsp : xs.splitOn '/' with _ | ⟨hd, tl⟩
      · exact absurd hsp (List.splitOn_ne_nil '/' xs)
      · rw [hsp] at hc
        change c ∈ (x :: hd) :: tl at hc
        rcases List.mem_cons.mp hc with rfl | htl
        · intro hm
          rcases List.mem_cons.mp hm with h1 | h2
          · exact hne h1.symm
          · exact slash_not_mem_of_mem_splitOn xs hd (by rw [hsp]; exact List.mem_cons_self ..) h2
        · exact slash_not_mem_of_mem_splitOn xs c (by rw [hsp]; exact List.mem_cons_of_mem _ htl)

theorem intercalate_splitOn :
    ∀ (cs : List Char), ['/'].intercalate (cs.splitOn '/') = cs
  | [] => by rw [List.splitOn_nil]; rfl
  | x :: xs => by
    rw [List.splitOn_cons_eq_ite_modifyHead]
    have ih := intercalate_splitOn xs
    rcases hsp : xs.splitOn '/' with _ | ⟨hd, tl⟩
    · exact absurd hsp (List.splitOn_ne_nil '/' xs)
    · rw [hsp] at ih
      by_cases hx : (x == '/') = true
      · have hxeq : x = '/' := beq_iff_eq.mp hx
        subst hxeq
        simp only [beq_self_eq_true, ↓reduceIte, List.intercalate_cons_cons, List.nil_append,
          List.singleton_append, List.cons.injEq, true_and]
        exact ih
      · rw [Bool.not_eq_true] at hx
        simp only [hx, Bool.false_eq_true, ↓reduceIte]
        change ['/'].intercalate ((x :: hd) :: tl) = x :: xs
        cases tl with
        | nil =>
          rw [List.intercalate_singleton] at ih ⊢
          rw [ih]
        | cons b tl' =>
          simp only [List.intercalate_cons_cons, List.cons_append, List.cons.injEq, true_and]
          simpa only [List.intercalate_cons_cons] using ih

theorem pathComps_ne_nil (p : String) : pathComps p ≠ [] :=
  List.splitOn_ne_nil '/' p.toList

theorem goodComp_of_mem_pathComps {p : String} (hp : PathOk p = true)
    {c : List Char} (hc : c ∈ pathComps p) : GoodComp c := by
  have hall := List.all_eq_true.mp hp c hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', isUnmodelledPathComponent,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hall
  refine ⟨?_, hall.1.1.1.2, hall.1.1.2, not_mem_of_contains_false hall.1.2,
    slash_not_mem_of_mem_splitOn p.toList c hc⟩
  intro he
  subst he
  exact Bool.noConfusion hall.1.1.1.1

/-! ## 2. `strOfComps`, `splitSlash`, `normalizePath`, and Trailing-Slash Lemmas -/

/-- Reassemble slash-separated `List Char` components into a `String`. -/
def strOfComps (ds : List (List Char)) : String :=
  String.ofList (['/'].intercalate ds)

theorem strOfComps_pathComps (p : String) : strOfComps (pathComps p) = p := by
  unfold strOfComps pathComps
  rw [intercalate_splitOn, String.ofList_toList]

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

theorem splitSlash_strOfComps :
    ∀ {ds : List (List Char)}, ds ≠ [] → (∀ c ∈ ds, GoodComp c) →
      splitSlash (strOfComps ds) = ds.map String.ofList
  | [], hne, _ => absurd rfl hne
  | [c], _, hg => by
    unfold splitSlash strOfComps
    rw [String.toList_ofList, List.intercalate_singleton,
      splitSlash_go_noSlash c [] (hg c (List.mem_cons_self ..)).2.2.2.2, List.reverse_nil,
      List.nil_append]
    rfl
  | c :: d :: rest, _, hg => by
    unfold splitSlash strOfComps
    rw [String.toList_ofList, List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
      splitSlash_go_append_slash c [] _ (hg c (List.mem_cons_self ..)).2.2.2.2,
      List.reverse_nil, List.nil_append]
    have ih := splitSlash_strOfComps (ds := d :: rest) (List.cons_ne_nil _ _)
      (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    unfold splitSlash strOfComps at ih
    rw [String.toList_ofList] at ih
    rw [ih]
    rfl

private theorem goodComp_isEmpty_false {c : List Char} (hc : GoodComp c) :
    (String.ofList c).isEmpty = false := by
  refine Bool.eq_false_iff.mpr fun he => hc.1 ?_
  have := congrArg String.toList (String.isEmpty_iff.mp he)
  simpa using this

private theorem goodComp_bne_dot {c : List Char} (hc : GoodComp c) :
    (String.ofList c != ".") = true := by
  rw [bne_iff_ne]
  intro he
  apply hc.2.1
  have := congrArg String.toList he
  simpa using this

private theorem goodComp_beq_dot_false {c : List Char} (hc : GoodComp c) :
    (String.ofList c == ".") = false := by
  rw [beq_eq_false_iff_ne]
  exact bne_iff_ne.mp (goodComp_bne_dot hc)

private theorem goodComp_ne_dotdot {c : List Char} (hc : GoodComp c) :
    String.ofList c ≠ ".." := by
  intro he
  apply hc.2.2.1
  have := congrArg String.toList he
  simpa using this

theorem normalizePath_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    normalizePath (strOfComps ds) = ds.map String.ofList := by
  unfold normalizePath
  rw [splitSlash_strOfComps hne hg, List.filter_eq_self]
  intro seg hseg
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hseg
  have hgc := hg c hc
  simp [goodComp_isEmpty_false hgc, goodComp_bne_dot hgc]

theorem filter_nonEmpty_splitSlash_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    (splitSlash (strOfComps ds)).filter (!·.isEmpty) = ds.map String.ofList := by
  rw [splitSlash_strOfComps hne hg, List.filter_eq_self]
  intro seg hseg
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hseg
  simp [goodComp_isEmpty_false (hg c hc)]

theorem hasDotDot_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    hasDotDot (strOfComps ds) = false := by
  unfold hasDotDot
  rw [splitSlash_strOfComps hne hg]
  refine Bool.eq_false_iff.mpr fun htr => ?_
  have hm : ".." ∈ ds.map String.ofList := by
    rw [List.contains_iff_exists_mem_beq] at htr
    obtain ⟨a, ha, hab⟩ := htr
    rwa [← beq_iff_eq.mp hab] at ha
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
  exact goodComp_ne_dotdot (hg c hc) he

private theorem head_intercalate_good {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    ∃ a tl, ['/'].intercalate ds = a :: tl ∧ a ≠ '/' := by
  rcases ds with _ | ⟨c, rest⟩
  · exact absurd rfl hne
  · have hgc := hg c (List.mem_cons_self ..)
    rcases c with _ | ⟨a, cs⟩
    · exact absurd rfl hgc.1
    · have ha : a ≠ '/' := fun he => hgc.2.2.2.2 (he ▸ List.mem_cons_self ..)
      cases rest with
      | nil => exact ⟨a, cs, List.intercalate_singleton .., ha⟩
      | cons d rest' =>
        exact ⟨a, cs ++ '/' :: ['/'].intercalate (d :: rest'), by simp [List.intercalate_cons_cons], ha⟩

theorem isEmpty_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    (strOfComps ds).isEmpty = false := by
  obtain ⟨a, tl, heq, _⟩ := head_intercalate_good hne hg
  refine Bool.eq_false_iff.mpr fun he => ?_
  have h1 := congrArg String.toList (String.isEmpty_iff.mp he)
  unfold strOfComps at h1
  rw [String.toList_ofList, heq] at h1
  simp at h1

theorem hasLeadingSlash_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    hasLeadingSlash (strOfComps ds) = false := by
  obtain ⟨a, tl, heq, ha⟩ := head_intercalate_good hne hg
  unfold hasLeadingSlash strOfComps
  rw [String.toList_ofList, heq]
  simp [ha]

private def NoTrailDirRev (r : List Char) : Prop :=
  ∃ z1 zs, r = z1 :: zs ∧ z1 ≠ '/' ∧ (z1 ≠ '.' ∨ ∃ z2 zs', zs = z2 :: zs' ∧ z2 ≠ '/')

private theorem NoTrailDirRev.append {r : List Char} (hr : NoTrailDirRev r) (suf : List Char) :
    NoTrailDirRev (r ++ suf) := by
  rcases hr with ⟨z1, zs, rfl, hz1, hdisj⟩
  refine ⟨z1, zs ++ suf, List.cons_append, hz1, ?_⟩
  rcases hdisj with hnd | ⟨z2, zs', rfl, hz2⟩
  · exact Or.inl hnd
  · exact Or.inr ⟨z2, zs' ++ suf, List.cons_append, hz2⟩

private theorem noTrailDirRev_goodComp {c : List Char} (hc : GoodComp c) :
    NoTrailDirRev c.reverse := by
  rcases hrev : c.reverse with _ | ⟨z1, zs⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hrev) hc.1
  · have hz1_mem : z1 ∈ c := List.mem_reverse.mp (hrev ▸ List.mem_cons_self ..)
    have hz1 : z1 ≠ '/' := fun he => hc.2.2.2.2 (he ▸ hz1_mem)
    rcases zs with _ | ⟨z2, zs'⟩
    · refine ⟨z1, [], rfl, hz1, Or.inl fun hdot => hc.2.1 ?_⟩
      subst hdot
      have := congrArg List.reverse hrev
      simpa using this
    · have hz2_mem : z2 ∈ c :=
        List.mem_reverse.mp (hrev ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
      exact ⟨z1, z2 :: zs', rfl, hz1, Or.inr ⟨z2, zs', rfl, fun he => hc.2.2.2.2 (he ▸ hz2_mem)⟩⟩

private theorem noTrailDirRev_intercalate :
    ∀ {ds : List (List Char)}, ds ≠ [] → (∀ c ∈ ds, GoodComp c) →
      NoTrailDirRev (['/'].intercalate ds).reverse
  | [], hne, _ => absurd rfl hne
  | [c], _, hg => by
    rw [List.intercalate_singleton]
    exact noTrailDirRev_goodComp (hg c (List.mem_cons_self ..))
  | c :: d :: rest, _, hg => by
    rw [List.intercalate_cons_cons, List.reverse_append]
    exact (noTrailDirRev_intercalate (ds := d :: rest) (List.cons_ne_nil _ _)
      (fun x hx => hg x (List.mem_cons_of_mem _ hx))).append _

theorem hasTrailingSlash_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    hasTrailingSlash (strOfComps ds) = false := by
  obtain ⟨z1, zs, hrev, hz1, _⟩ := noTrailDirRev_intercalate hne hg
  unfold hasTrailingSlash strOfComps
  rw [String.toList_ofList, hrev]
  simp [hz1]

theorem endsWithSlashDot_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    endsWithSlashDot (strOfComps ds) = false := by
  obtain ⟨z1, zs, hrev, _, hdisj⟩ := noTrailDirRev_intercalate hne hg
  unfold endsWithSlashDot strOfComps
  rw [String.toList_ofList, hrev]
  rcases zs with _ | ⟨z2, zs'⟩
  · simp
  · by_cases h1 : z1 = '.'
    · subst h1
      rcases hdisj with hnd | ⟨z2', zs'', heq, hz2⟩
      · exact absurd rfl hnd
      · injection heq with hz2_eq _
        subst hz2_eq
        split
        · next h => injection h with _ h'; injection h' with hsl _; exact absurd hsl hz2
        · rfl
    · split
      · next h => injection h with hdot _; exact absurd hdot h1
      · rfl

theorem beq_dot_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    (strOfComps ds == ".") = false := by
  rw [beq_eq_false_iff_ne]
  intro he
  have h1 := congrArg String.toList he
  unfold strOfComps at h1
  rw [String.toList_ofList] at h1
  rcases ds with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · exact hne rfl
  · rw [List.intercalate_singleton] at h1
    exact (hg c (List.mem_cons_self ..)).2.1 (by simpa using h1)
  · rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append] at h1
    have hsl : '/' ∈ c ++ '/' :: ['/'].intercalate (d :: rest) := by simp
    rw [h1] at hsl
    revert hsl; decide

theorem trailingDir_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    trailingDir (strOfComps ds) = false := by
  unfold trailingDir
  rw [beq_dot_strOfComps hne hg, hasTrailingSlash_strOfComps hne hg,
    endsWithSlashDot_strOfComps hne hg]
  rfl

theorem trailingNormSlash_strOfComps {ds : List (List Char)} (hne : ds ≠ [])
    (hg : ∀ c ∈ ds, GoodComp c) :
    trailingNormSlash (strOfComps ds) = false := by
  unfold trailingNormSlash
  rw [hasTrailingSlash_strOfComps hne hg]
  rfl

theorem nul_not_mem_intercalate :
    ∀ {ds : List (List Char)}, (∀ c ∈ ds, GoodComp c) → '\x00' ∉ ['/'].intercalate ds
  | [], _, hm => absurd hm List.not_mem_nil
  | [c], hg, hm => by
    rw [List.intercalate_singleton] at hm
    exact (hg c (List.mem_cons_self ..)).2.2.2.1 hm
  | c :: d :: rest, hg, hm => by
    rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append] at hm
    rcases List.mem_append.mp hm with hc | htl
    · exact (hg c (List.mem_cons_self ..)).2.2.2.1 hc
    · rcases List.mem_cons.mp htl with hsl | hrest
      · exact absurd hsl (by decide)
      · exact nul_not_mem_intercalate (fun x hx => hg x (List.mem_cons_of_mem _ hx)) hrest

/-! ## 3. Corollaries on `PathOk` Paths and Exact `ancestorWalkErrno?` Agreement -/

theorem validRelCPath_of_pathOk {p : String} (hp : PathOk p = true)
    (hlen : p.toList.length < PATH_MAX) (hlat : ∀ c ∈ p.toList, c.toNat < 256) :
    ValidRelCPath p := by
  have hcs_ne := pathComps_ne_nil p
  have hg : ∀ c ∈ pathComps p, GoodComp c := fun c hc => goodComp_of_mem_pathComps hp hc
  have hp_eq := strOfComps_pathComps p
  refine ⟨⟨hlen, fun c hc => ⟨hlat c hc, ?_⟩⟩, ?_, ?_⟩
  · intro h0
    have hc0 : c = '\x00' := by
      cases c with
      | mk val valid =>
        cases val with
        | ofBitVec bv =>
          simp only [Char.toNat, UInt32.toNat] at h0
          have hbv : bv = 0#32 := BitVec.eq_of_toNat_eq h0
          subst hbv
          rfl
    subst hc0
    have hnul := nul_not_mem_intercalate hg
    unfold pathComps at hnul
    rw [intercalate_splitOn] at hnul
    exact hnul hc
  · rw [← hp_eq]; exact hasLeadingSlash_strOfComps hcs_ne hg
  · rw [← hp_eq]; exact hasDotDot_strOfComps hcs_ne hg

theorem isEmpty_false_of_pathOk {p : String} (hp : PathOk p = true) :
    p.isEmpty = false := by
  rw [← strOfComps_pathComps p]
  exact isEmpty_strOfComps (pathComps_ne_nil p) (fun c hc => goodComp_of_mem_pathComps hp hc)

theorem normalizePath_of_pathOk {p : String} (hp : PathOk p = true) :
    normalizePath p = (pathComps p).map String.ofList := by
  conv => lhs; rw [← strOfComps_pathComps p]
  exact normalizePath_strOfComps (pathComps_ne_nil p) (fun c hc => goodComp_of_mem_pathComps hp hc)

theorem normalizePath_ne_nil_of_pathOk {p : String} (hp : PathOk p = true) :
    normalizePath p ≠ [] := by
  rw [normalizePath_of_pathOk hp]
  intro h
  exact pathComps_ne_nil p (List.map_eq_nil_iff.mp h)

theorem trailingDir_false_of_pathOk {p : String} (hp : PathOk p = true) :
    trailingDir p = false := by
  rw [← strOfComps_pathComps p]
  exact trailingDir_strOfComps (pathComps_ne_nil p) (fun c hc => goodComp_of_mem_pathComps hp hc)

theorem trailingNormSlash_false_of_pathOk {p : String} (hp : PathOk p = true) :
    trailingNormSlash p = false := by
  rw [← strOfComps_pathComps p]
  exact trailingNormSlash_strOfComps (pathComps_ne_nil p)
    (fun c hc => goodComp_of_mem_pathComps hp hc)

theorem blockingAncestor?_ne_some_dir (fs : FsState) (p : String) :
    blockingAncestor? fs p ≠ some (some .dir) := by
  unfold blockingAncestor?
  intro h
  obtain ⟨q, hfind, hq⟩ := Option.map_eq_some_iff.mp h
  have hp_q := List.find?_some hfind
  rw [hq] at hp_q
  exact Bool.noConfusion hp_q

private theorem dropLast_map {α β : Type} (f : α → β) :
    ∀ (xs : List α), (xs.map f).dropLast = xs.dropLast.map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp only [List.map_cons, List.dropLast_cons_cons, List.cons.injEq, true_and]
    exact dropLast_map f (b :: rest)

private def blockingToErrno : Option (Option FsEntry) → Option (BitVec 64)
  | none => none
  | some none => some ENOENT
  | some (some (.file _)) => some ENOTDIR
  | some (some .dir) => none

private theorem ancestorWalk_eq_find_aux (fs : FsState) :
    ∀ (rem : List (List Char)) (pref : List (List Char)),
      rem ≠ [] →
      (∀ c ∈ pref, GoodComp c) →
      (∀ c ∈ rem, GoodComp c) →
      (∀ c ∈ rem, c.length ≤ NAME_MAX) →
      ancestorWalkErrno?.walk fs (pref.map String.ofList) (rem.dropLast.map String.ofList) =
        blockingToErrno ((((List.range (rem.length - 1)).map fun i =>
            strOfComps (pref ++ rem.take (i + 1))).find? fun q =>
              match fs.files q with | some .dir => false | _ => true).map fs.files)
  | [], _, hne, _, _, _ => absurd rfl hne
  | [_], _, _, _, _, _ => rfl
  | c :: d :: tl, pref, _, hg_pref, hg_rem, hmax_rem => by
    have hgc : GoodComp c := hg_rem c (List.mem_cons_self ..)
    have hcmax : ¬ ((String.ofList c).length > NAME_MAX) := by
      rw [String.length_ofList]
      exact Nat.not_lt.mpr (hmax_rem c (List.mem_cons_self ..))
    have hdot : (String.ofList c == ".") = false := goodComp_beq_dot_false hgc
    have hg_pref' : ∀ x ∈ pref ++ [c], GoodComp x := by
      intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact hg_pref x h1
      · rw [List.mem_singleton] at h2; subst h2; exact hgc
    have hg_rem' : ∀ x ∈ d :: tl, GoodComp x :=
      fun x hx => hg_rem x (List.mem_cons_of_mem _ hx)
    have hmax_rem' : ∀ x ∈ d :: tl, x.length ≤ NAME_MAX :=
      fun x hx => hmax_rem x (List.mem_cons_of_mem _ hx)
    have hne_pc : pref ++ [c] ≠ [] := by simp
    have hnorm_pc : normalizePath (strOfComps (pref ++ [c])) = (pref ++ [c]).map String.ofList :=
      normalizePath_strOfComps hne_pc hg_pref'
    have hfiles_pc : fs.files (strOfComps (pref ++ [c])) =
        fs.getEntry (pref.map String.ofList ++ [String.ofList c]) := by
      unfold FsState.files
      rw [hnorm_pc, List.map_append, List.map_singleton]
    have hlen_eq : (c :: d :: tl).length - 1 = ((d :: tl).length - 1) + 1 := by
      simp
    have hrange :
        ((List.range ((c :: d :: tl).length - 1)).map fun i =>
            strOfComps (pref ++ (c :: d :: tl).take (i + 1))) =
          strOfComps (pref ++ [c]) ::
            ((List.range ((d :: tl).length - 1)).map fun j =>
              strOfComps ((pref ++ [c]) ++ (d :: tl).take (j + 1))) := by
      rw [hlen_eq, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, true_and]
      refine List.map_congr_left fun j _ => ?_
      simp [List.append_assoc]
    simp only [List.dropLast_cons_cons, List.map_cons, ancestorWalkErrno?.walk, hcmax, hdot,
      Bool.false_eq_true, ↓reduceIte, hrange, List.find?_cons, hfiles_pc]
    cases hge : fs.getEntry (pref.map String.ofList ++ [String.ofList c]) with
    | none => simp [blockingToErrno, hfiles_pc, hge]
    | some e =>
      cases e with
      | file bs => simp [blockingToErrno, hfiles_pc, hge]
      | dir =>
        dsimp only
        have ih := ancestorWalk_eq_find_aux fs (d :: tl) (pref ++ [c]) (List.cons_ne_nil _ _)
          hg_pref' hg_rem' hmax_rem'
        rw [List.map_append, List.map_singleton] at ih
        exact ih

private theorem getLast_map_length_gt_false :
    ∀ (cs : List (List Char)), (∀ c ∈ cs, c.length ≤ NAME_MAX) →
      (cs.map String.ofList).getLast?.any (·.length > NAME_MAX) = false
  | [], _ => rfl
  | [c], h => by
    simp only [List.map_cons, List.map_nil, List.getLast?_singleton, Option.any_some,
      String.length_ofList]
    exact decide_eq_false (Nat.not_lt.mpr (h c (List.mem_singleton.mpr rfl)))
  | c :: d :: tl, h => by
    simp only [List.map_cons, List.getLast?_cons_cons]
    exact getLast_map_length_gt_false (d :: tl) (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Exact agreement between `Arm64.ancestorWalkErrno? fs p` and `CliRun.blockingAncestor? fs p`
    on any `PathOk` path `p` whose components fit in `NAME_MAX`. -/
theorem ancestorWalkErrno?_eq_of_pathOk (fs : FsState) {p : String} (hp : PathOk p = true)
    (hmax : ((pathComps p).all fun c => decide (c.length ≤ NAME_MAX)) = true) :
    ancestorWalkErrno? fs p =
      match blockingAncestor? fs p with
      | none => none
      | some none => some ENOENT
      | some (some (.file _)) => some ENOTDIR
      | some (some .dir) => none := by
  have hcs_ne := pathComps_ne_nil p
  have hg : ∀ c ∈ pathComps p, GoodComp c := fun c hc => goodComp_of_mem_pathComps hp hc
  have hcm : ∀ c ∈ pathComps p, c.length ≤ NAME_MAX := fun c hc =>
    of_decide_eq_true (List.all_eq_true.mp hmax c hc)
  have hfilt : (splitSlash p).filter (!·.isEmpty) = (pathComps p).map String.ofList := by
    conv => lhs; rw [← strOfComps_pathComps p]
    exact filter_nonEmpty_splitSlash_strOfComps hcs_ne hg
  have haux := ancestorWalk_eq_find_aux fs (pathComps p) [] hcs_ne
    (fun _ h => absurd h List.not_mem_nil) hg hcm
  rw [List.map_nil] at haux
  have hanc_list :
      ((List.range ((pathComps p).length - 1)).map fun i =>
          strOfComps ([] ++ (pathComps p).take (i + 1))) =
        ancestors p := by
    unfold ancestors
    refine List.map_congr_left fun i _ => ?_
    simp [strOfComps]
  have hba :
      (((ancestors p).find? fun q =>
          match fs.files q with | some .dir => false | _ => true).map fs.files) =
        blockingAncestor? fs p := by
    unfold blockingAncestor?
    congr 2
  rw [hanc_list, hba] at haux
  have hlast := getLast_map_length_gt_false (pathComps p) hcm
  unfold ancestorWalkErrno?
  dsimp only
  rw [hfilt, dropLast_map, haux, hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases blockingAncestor? fs p with
  | none => rfl
  | some a =>
    cases a with
    | none => rfl
    | some e => cases e <;> rfl

/-! ## 4. `FsState.allocFd` Bounds & Deterministic `execOpenat` Characterization -/

private theorem find_fds_none_spec {fs : FsState} :
    ∀ (l : List Nat) {i : Nat},
      l.find? (fun i => fs.fds (BitVec.ofNat 64 (i + 3)) == none) = some i →
      i ∈ l ∧ fs.fds (BitVec.ofNat 64 (i + 3)) = none
  | [], _, h => by cases h
  | a :: as, i, h => by
    rw [List.find?_cons] at h
    cases hf : fs.fds (BitVec.ofNat 64 (a + 3)) with
    | none =>
      have htrue : ((none : Option FdEntry) == none) = true := rfl
      rw [hf, htrue] at h
      dsimp only at h
      injection h with hi
      subst hi
      exact ⟨List.mem_cons_self .., hf⟩
    | some val =>
      have hfalse : (some val == (none : Option FdEntry)) = false := rfl
      rw [hf, hfalse] at h
      dsimp only at h
      obtain ⟨hm, heq⟩ := find_fds_none_spec as h
      exact ⟨List.mem_cons_of_mem _ hm, heq⟩

theorem allocFd_spec {fs : FsState} {fd : BitVec 64} (h : fs.allocFd = some fd) :
    3 ≤ fd.toNat ∧ fd.toNat < FsState.maxOpenFds ∧ fs.fds fd = none := by
  unfold FsState.allocFd at h
  obtain ⟨i, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hmem, hfds_eq⟩ := find_fds_none_spec (List.range (FsState.maxOpenFds - 3)) hfind
  clear h hfind
  rw [List.mem_range] at hmem
  have hmmax : FsState.maxOpenFds = 1024 := rfl
  rw [hmmax] at hmem ⊢
  have hlt1024 : i + 3 < 1024 := by omega
  have h1024_lt : (1024 : Nat) < 2 ^ 64 := by decide
  have hlt64 : i + 3 < 2 ^ 64 := Nat.lt_trans hlt1024 h1024_lt
  have htoNat : (BitVec.ofNat 64 (i + 3)).toNat = i + 3 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  exact ⟨by omega, by omega, hfds_eq⟩

theorem setFd_none_setFd_of_fds_none {fs : FsState} {fd : BitVec 64} {d : Option FdEntry}
    (h : fs.fds fd = none) :
    (fs.setFd fd d).setFd fd none = fs := by
  cases fs with
  | mk entries stdin fds =>
    dsimp only at h
    simp only [FsState.setFd, FsState.mk.injEq, true_and]
    funext k
    by_cases hk : (k == fd) = true
    · rw [eq_of_beq hk]; simp [h]
    · simp [hk]

/-- Deterministic outcome of `open(cstr, O_CLOEXEC_W32)` on a `PathOk` path. -/
inductive OpenRdonlyDetResult where
  | err (errno : Nat)
  | ok (fd : BitVec 64) (kind : FdKind)
  deriving DecidableEq, Repr

/-- Deterministic VFS classifier for `open(cstr, O_CLOEXEC_W32)` matching `CliRun.blockingAncestor?`,
    `FsState.files`, and `FsState.allocFd`. -/
def classifyOpenRdonly (fs : FsState) (path : String) : OpenRdonlyDetResult :=
  match blockingAncestor? fs path with
  | some (some _) => .err 20
  | some none     => .err 2
  | none =>
    match fs.files path with
    | none => .err 2
    | some .dir =>
      match fs.allocFd with
      | none    => .err 24
      | some fd => .ok fd .localDir
    | some (.file _) =>
      match fs.allocFd with
      | none    => .err 24
      | some fd => .ok fd .localFile

theorem classifyOpenRdonly_err_cases {fs : FsState} {path : String} {errno : Nat}
    (h : classifyOpenRdonly fs path = .err errno) :
    errno = 2 ∨ errno = 20 ∨ errno = 24 := by
  unfold classifyOpenRdonly at h
  cases hb : blockingAncestor? fs path with
  | some a =>
    rw [hb] at h
    cases a with
    | none => injection h with he; exact Or.inl he.symm
    | some _ => injection h with he; exact Or.inr (Or.inl he.symm)
  | none =>
    rw [hb] at h
    cases hf : fs.files path with
    | none => rw [hf] at h; injection h with he; exact Or.inl he.symm
    | some e =>
      rw [hf] at h
      cases e with
      | dir =>
        cases ha : fs.allocFd with
        | none => rw [ha] at h; injection h with he; exact Or.inr (Or.inr he.symm)
        | some _ => rw [ha] at h; cases h
      | file _ =>
        cases ha : fs.allocFd with
        | none => rw [ha] at h; injection h with he; exact Or.inr (Or.inr he.symm)
        | some _ => rw [ha] at h; cases h

theorem classifyOpenRdonly_err_ne_eintr {fs : FsState} {path : String} {errno : Nat}
    (h : classifyOpenRdonly fs path = .err errno) :
    BitVec.ofNat 32 errno ≠ 4#32 := by
  rcases classifyOpenRdonly_err_cases h with rfl | rfl | rfl <;> decide

private theorem classifyOpenRdonly_err_of_none_some (fs : FsState) (path : String) (e : FsEntry)
    {errno : Nat}
    (hb : blockingAncestor? fs path = none)
    (hf : fs.files path = some e)
    (hcl : classifyOpenRdonly fs path = .err errno) :
    fs.allocFd = none ∧ errno = 24 := by
  unfold classifyOpenRdonly at hcl
  rw [hb, hf] at hcl
  cases e with
  | dir =>
    cases ha : fs.allocFd with
    | none => rw [ha] at hcl; injection hcl with he; exact ⟨rfl, he.symm⟩
    | some _ => rw [ha] at hcl; cases hcl
  | file _ =>
    cases ha : fs.allocFd with
    | none => rw [ha] at hcl; injection hcl with he; exact ⟨rfl, he.symm⟩
    | some _ => rw [ha] at hcl; cases hcl

theorem classifyOpenRdonly_ok_spec {fs : FsState} {path : String} {fd : BitVec 64} {kind : FdKind}
    (h : classifyOpenRdonly fs path = .ok fd kind) :
    blockingAncestor? fs path = none ∧
    fs.allocFd = some fd ∧
    3 ≤ fd.toNat ∧ fd.toNat < FsState.maxOpenFds ∧ fs.fds fd = none ∧
    ((kind = .localDir ∧ fs.files path = some .dir) ∨
      (kind = .localFile ∧ ∃ bs, fs.files path = some (.file bs))) := by
  unfold classifyOpenRdonly at h
  cases hb : blockingAncestor? fs path with
  | some a =>
    rw [hb] at h; cases a <;> cases h
  | none =>
    rw [hb] at h
    cases hf : fs.files path with
    | none => rw [hf] at h; cases h
    | some e =>
      rw [hf] at h
      cases e with
      | dir =>
        cases ha : fs.allocFd with
        | none => rw [ha] at h; cases h
        | some fd' =>
          rw [ha] at h
          injection h with hfd hk
          subst hfd hk
          obtain ⟨hge, hlt, hfds⟩ := allocFd_spec ha
          exact ⟨rfl, rfl, hge, hlt, hfds, Or.inl ⟨rfl, rfl⟩⟩
      | file bs =>
        cases ha : fs.allocFd with
        | none => rw [ha] at h; cases h
        | some fd' =>
          rw [ha] at h
          injection h with hfd hk
          subst hfd hk
          obtain ⟨hge, hlt, hfds⟩ := allocFd_spec ha
          exact ⟨rfl, rfl, hge, hlt, hfds, Or.inr ⟨rfl, bs, rfl⟩⟩

private theorem execOpenat_rdonly_cloexec_err_anc {s : State} {path : String} {err : BitVec 64}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = some err) :
    execOpenat s = (s.writeReg64 .x0 (-err)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  rw [ancestorWalkErrno_eq_strict] at hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_cr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres]
  cases hsanc : strictAncestorWalkErrno? s.fs path with
  | some e =>
    rw [hsanc] at hanc
    injection hanc with he; subst he; rfl
  | none =>
    rw [hsanc] at hanc
    cases hlast : ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
    | true =>
      rw [hlast] at hanc
      simp only [↓reduceIte, Option.some.injEq] at hanc
      subst hanc; rfl
    | false =>
      rw [hlast] at hanc; cases hanc

private theorem execOpenat_rdonly_cloexec_missing {s : State} {path : String}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hnone : s.fs.files path = none) :
    execOpenat s = (s.writeReg64 .x0 (-ENOENT)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = none := hnone
  obtain ⟨hsanc, hlast⟩ := strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_cr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge]
  simp

private theorem execOpenat_rdonly_cloexec_emfile_dir {s : State} {path : String}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hdir : s.fs.files path = some .dir)
    (halloc : s.fs.allocFd = none) :
    execOpenat s = (s.writeReg64 .x0 (-EMFILE)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hrd_ne : (FdAccessMode.rdonly != FdAccessMode.rdonly) = false := rfl
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some .dir := hdir
  obtain ⟨hsanc, hlast⟩ := strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_tr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, hrd_ne, halloc]
  simp

private theorem execOpenat_rdonly_cloexec_file_or_emfile {s : State} {path : String}
    {bs : List (BitVec 8)}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (htd : trailingDir path = false)
    (hnorm_ne : normalizePath path ≠ [])
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hfile : s.fs.files path = some (.file bs)) :
    execOpenat s =
      match s.fs.allocFd with
      | none => (s.writeReg64 .x0 (-EMFILE)).advancePC
      | some fd =>
        ((s.setFs (s.fs.setFd fd (some
            { path := path, accMode := .rdonly, append := false, cloexec := true,
              offset := 0, kind := .localFile }))).writeReg64 .x0 fd).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hf_ap : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_APPEND_W32 != 0#32) = false := by decide
  have hf_dr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_DIRECTORY_W32 != 0#32) = false := by decide
  have hf_cl : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CLOEXEC_W32 != 0#32) = true := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some (.file bs) := hfile
  have hself : s.fs.setEntry (normalizePath path) (some (.file bs)) = s.fs :=
    FsState.setEntry_self_of_nonEmpty hnorm_ne hge
  obtain ⟨hsanc, hlast⟩ := strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_tr, hf_ap, hf_dr, hf_cl, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, Bool.and_false, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, htd]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  cases s.fs.allocFd with
  | none => rfl
  | some fd => simp [hself]

/-! ## 5. Placement-Generic `muslOpenRdonlyDet` Contract (`blk08`, `112`-byte stack frame) -/

/-- Deterministic contract for `int open(const char *path, O_CLOEXEC, mode)` (`blk08`, `112`-byte
    stack frame) on any `PathOk` path (`path.toList.length < PATH_MAX`, `NAME_MAX`, Latin-1/ASCII). -/
def muslOpenRdonlyDetSpec : Spec (BitVec 64 × String × BitVec 32) where
  pre := fun (cstr, path, e0) s0 =>
    ⌜s0.readReg64 .x0 = cstr ∧
      s0.readReg32 .x1 = O_CLOEXEC_W32 ∧
      PathOk path = true ∧
      ((pathComps path).all fun c => decide (c.length ≤ NAME_MAX)) = true ∧
      path.toList.length < PATH_MAX ∧
      (∀ c ∈ path.toList, c.toNat < 256)⌝ ∗
    (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (cstr, path, e0) s0 sf =>
    match classifyOpenRdonly s0.fs path with
    | .ok fd kind =>
      ⌜sf.readReg32 .x0 = fd.truncate 32 ∧
        sf.fs = s0.fs.setFd fd
          (some { path := path, accMode := .rdonly, append := false, cloexec := true,
                  offset := 0, kind := kind }) ∧
        sf.trace = s0.trace ∧
        SyscallPreserved s0 sf⌝ ∗
      (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ e0))
    | .err errno =>
      ⌜sf.readReg32 .x0 = 0xffffffff#32 ∧
        sf.fs = s0.fs ∧
        sf.trace = s0.trace ∧
        SyscallPreserved s0 sf⌝ ∗
      (stackAt s0.sp 112 ∗ (cstr ↦ₛ cstrBytes path) ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 errno))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem setFs_appendTrace_nil (s : State) (fs' : FsState) :
    (s.setFs fs').appendTrace [] = s.setFs fs' := by
  cases s; simp [State.setFs, State.appendTrace]

private theorem execOpenat_of_classifyOpenRdonly_err {s : State} {path : String} {errno : Nat}
    (hpok : PathOk path = true)
    (hmax : ((pathComps path).all fun c => decide (c.length ≤ NAME_MAX)) = true)
    (hcl : classifyOpenRdonly s.fs path = .err errno)
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path) :
    execOpenat s = (s.writeReg64 .x0 (-BitVec.ofNat 64 errno)).advancePC := by
  have hcs_ne := pathComps_ne_nil path
  have hg : ∀ c ∈ pathComps path, GoodComp c := fun c hc => goodComp_of_mem_pathComps hpok hc
  have hp_eq := strOfComps_pathComps path
  have hne : path.isEmpty = false := isEmpty_false_of_pathOk hpok
  have hlead : hasLeadingSlash path = false := by
    rw [← hp_eq]; exact hasLeadingSlash_strOfComps hcs_ne hg
  have hdot : hasDotDot path = false := by
    rw [← hp_eq]; exact hasDotDot_strOfComps hcs_ne hg
  have htd : trailingDir path = false := trailingDir_false_of_pathOk hpok
  have hnorm_ne : normalizePath path ≠ [] := normalizePath_ne_nil_of_pathOk hpok
  have hanc_eq := ancestorWalkErrno?_eq_of_pathOk s.fs hpok hmax
  have hcl0 := hcl
  unfold classifyOpenRdonly at hcl
  cases hb : blockingAncestor? s.fs path with
  | some a =>
    rw [hb] at hcl hanc_eq
    cases a with
    | none =>
      have he : errno = 2 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
      subst he
      exact execOpenat_rdonly_cloexec_err_anc hdfd hflags hcs hne hlead hdot hanc_eq
    | some e =>
      cases e with
      | dir => exact absurd hb (blockingAncestor?_ne_some_dir s.fs path)
      | file _ =>
        have he : errno = 20 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
        subst he
        exact execOpenat_rdonly_cloexec_err_anc hdfd hflags hcs hne hlead hdot hanc_eq
  | none =>
    rw [hb] at hcl hanc_eq
    cases hf : s.fs.files path with
    | none =>
      rw [hf] at hcl
      have he : errno = 2 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
      subst he
      exact execOpenat_rdonly_cloexec_missing hdfd hflags hcs hne hlead hdot hanc_eq hf
    | some e =>
      obtain ⟨ha, rfl⟩ := classifyOpenRdonly_err_of_none_some s.fs path e hb hf hcl0
      cases e with
      | dir =>
        exact execOpenat_rdonly_cloexec_emfile_dir hdfd hflags hcs hne hlead hdot hanc_eq hf ha
      | file bs =>
        have hexec := execOpenat_rdonly_cloexec_file_or_emfile hdfd hflags hcs hne hlead hdot
          htd hnorm_ne hanc_eq hf
        rw [ha] at hexec
        exact hexec

theorem muslOpenRdonlyDet_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 8)
      (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslOpenRdonlyDetSpec) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨cstr, path, e0⟩ R s0 hpc hrun hpre hsp _hL
  simp only [MultiPlacedLib.withCodeLoaded, muslOpenRdonlyDetSpec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpok, hmax, hlen, hlat⟩, hm⟩
  obtain ⟨hcp, hlead, hdot⟩ := validRelCPath_of_pathOk hpok hlen hlat
  have hne := isEmpty_false_of_pathOk hpok
  have htd := trailingDir_false_of_pathOk hpok
  have hnorm_ne := normalizePath_ne_nil_of_pathOk hpok
  have hb6 : O_CLOEXEC_W32.getLsbD 6 = false := by decide
  have htmp : O_CLOEXEC_W32 &&& 0x00404000#32 = 0#32 := by decide
  have hb19 : O_CLOEXEC_W32.getLsbD 19 = true := by decide
  have hfl_eq : O_CLOEXEC_W32 ||| O_LARGEFILE_W32 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  cases hcl : classifyOpenRdonly s0.fs path with
  | ok fd kind =>
    obtain ⟨hb_none, halloc, _, hfd_max, _, hkind_cases⟩ := classifyOpenRdonly_ok_spec hcl
    have hfd_lt : fd.toNat < 2 ^ 31 := by
      have hmmax : FsState.maxOpenFds = 1024 := rfl
      rw [hmmax] at hfd_max
      have h1024_lt : (1024 : Nat) < 2 ^ 31 := by decide
      exact Nat.lt_trans hfd_max h1024_lt
    have hanc_none : ancestorWalkErrno? s0.fs path = none := by
      rw [ancestorWalkErrno?_eq_of_pathOk s0.fs hpok hmax, hb_none]
    let desc : FdEntry :=
      { path := path, accMode := .rdonly, append := false, cloexec := true,
        offset := 0, kind := kind }
    let fs' : FsState := s0.fs.setFd fd (some desc)
    refine muslOpenNoCreatCloexecLocalExec_block_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .ok fd desc fs' []) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      rcases hkind_cases with ⟨rfl, hdir⟩ | ⟨rfl, bs, hfile⟩
      · have hexec := execOpenat_rdonly_cloexec_dir hs_x0 (hfl_eq ▸ hs_x2) hcs hne hlead hdot
          (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hdir) (hs_fs.symm ▸ halloc)
        rw [hs_fs] at hexec
        refine ⟨hfd_lt, by simp [fs', FsState.setFd], Or.inr rfl, rfl, ?_⟩
        rw [setFs_appendTrace_nil]; exact hexec
      · have hexec := execOpenat_rdonly_cloexec_file_or_emfile hs_x0 (hfl_eq ▸ hs_x2) hcs hne
          hlead hdot htd hnorm_ne (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hfile)
        rw [hs_fs, halloc] at hexec
        refine ⟨hfd_lt, by simp [fs', FsState.setFd], Or.inl rfl, rfl, ?_⟩
        rw [setFs_appendTrace_nil]; exact hexec
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simpa only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec,
          muslOpenRdonlyDetSpec, hcl, List.append_nil] using hq
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))
  | err errno =>
    have herr_cases := classifyOpenRdonly_err_cases hcl
    have herr_bounds : 1 ≤ errno ∧ errno ≤ 4095 := by
      rcases herr_cases with rfl | rfl | rfl <;> decide
    refine muslOpenNoCreatCloexecLocalExec_block_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .err (· = errno)) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      refine ⟨errno, herr_bounds.1, herr_bounds.2, rfl, ?_⟩
      exact execOpenat_of_classifyOpenRdonly_err hpok hmax (hs_fs.symm ▸ hcl) hs_x0
        (hfl_eq ▸ hs_x2) hcs
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec,
          muslOpenRdonlyDetSpec, hcl, sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
          satisfies_pure_sepConj] at hq ⊢
        rcases hq with ⟨errno', ⟨_, _, rfl, hx0', hfs', htr', hpres'⟩, hm_cells⟩
        exact ⟨⟨hx0', hfs', htr', hpres'⟩, hm_cells⟩
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))

theorem muslOpenRdonlyDet_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "open")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslOpenRdonlyDetSpec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 8) (by decide) muslOpenRdonlyDet_block_ok hext hsvc

end LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
