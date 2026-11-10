/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Provisioned CLI Directory Session-Path Absence

Proves path-normalization head-segment lemmas for `filesOf` and shows that `initDirs` contains no
session files, so `CliTurn.init (initDirs interp r)` starts with empty `records` and `leakRecords`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (filesOf fsView identityFile signedPreKeyFile
  oneTimePreKeyFile lastResortKyberPreKeyFile baseKeysFile)
open DY.Libsignal.Composed.Refinement.Cli (CliTurn initDirs commonFiles bobPreKeyFiles
  sessionPathOf peerOf peerNameOf)

set_option linter.auxLemma false in
private theorem splitSlash_go_cons_ne {c : Char} (cur rest : List Char) (hc : c ≠ '/') :
    Arm64.splitSlash.go cur (c :: rest) = Arm64.splitSlash.go (c :: cur) rest := by
  delta Arm64.splitSlash.go Arm64.splitSlash.go._f Arm64.splitSlash.go.match_1
  dsimp only [List.brecOn, List.brecOn.go, List.casesOn]
  split_ifs with h
  · exact absurd h hc
  · rfl

private theorem splitSlash_go_append_slash :
    ∀ (pref cur cs : List Char), '/' ∉ pref → Arm64.splitSlash.go cur (pref ++ '/' :: cs) =
      String.ofList (cur.reverse ++ pref) :: Arm64.splitSlash.go [] cs
  | [], cur, cs, _ => by rw [List.nil_append, List.append_nil]; rfl
  | c :: pref, cur, cs, h => by
    have hc : c ≠ '/' := fun heq => h (heq ▸ List.mem_cons_self ..)
    have h' : '/' ∉ pref := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [List.cons_append, splitSlash_go_cons_ne cur _ hc,
        splitSlash_go_append_slash pref (c :: cur) cs h']
    simp [List.reverse_cons, List.append_assoc]

theorem normalizePath_head_slash (dir rest : String)
    (hno : '/' ∉ dir.toList) (hne : (!dir.isEmpty && dir != ".") = true) :
    (Arm64.normalizePath ((dir ++ "/") ++ rest)).head? = some dir := by
  have hsplit : Arm64.splitSlash ((dir ++ "/") ++ rest) =
      dir :: Arm64.splitSlash.go [] rest.toList := by
    unfold Arm64.splitSlash
    simpa [String.toList_append] using splitSlash_go_append_slash dir.toList [] rest.toList hno
  simp [Arm64.normalizePath, hsplit, hne]

private theorem head?_of_mem_nonEmptyPrefixes :
    ∀ {segs pref : Arm64.FsPath}, pref ∈ Arm64.FsPath.nonEmptyPrefixes segs →
      pref.head? = segs.head?
  | [], _, h => nomatch h
  | s :: rest, pref, h => by
    change pref ∈ [s] :: (Arm64.FsPath.nonEmptyPrefixes rest).map (s :: ·) at h
    rw [List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, _, rfl⟩ <;> rfl

private theorem entries_foldl_anc_of_head_ne {target : Arm64.FsPath} {d : String}
    (ht : target.head? = some d) :
    ∀ (prefs : List Arm64.FsPath) (fs : Arm64.FsState),
      (∀ pref ∈ prefs, pref.head? ≠ some d) →
      (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries target =
        fs.entries target
  | [], fs, _ => rfl
  | pref :: prefs, fs, hne => by
    have hne0 : target ≠ pref := fun heq =>
      hne pref (List.mem_cons_self ..) (heq ▸ ht)
    rw [List.foldl_cons, entries_foldl_anc_of_head_ne ht prefs _
      (fun q hq => hne q (List.mem_cons_of_mem _ hq))]
    simp [Arm64.FsState.setEntry, hne0]

private theorem entries_foldl_files_of_head_ne {target : Arm64.FsPath} {d : String}
    (ht : target.head? = some d) :
    ∀ (files : List (String × HwBytes)) (fs : Arm64.FsState),
      (∀ f ∈ files, (Arm64.normalizePath f.1).head? ≠ some d) →
      (files.foldl (fun fs (p, bs) =>
        let withAnc := ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
          (fun acc pref => acc.setEntry pref (some .dir)) fs
        withAnc.setFile p (some (.file bs))) fs).entries target = fs.entries target
  | [], fs, _ => rfl
  | (p, bs) :: rest, fs, hne => by
    have hp_ne : (Arm64.normalizePath p).head? ≠ some d :=
      hne (p, bs) (List.mem_cons_self ..)
    have hanc : ∀ pref ∈ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast,
        pref.head? ≠ some d := by
      intro pref hpref
      rw [head?_of_mem_nonEmptyPrefixes (List.dropLast_subset _ hpref)]
      exact hp_ne
    have hfile_ne : (target == Arm64.normalizePath p) = false := beq_false_of_ne fun heq =>
      hp_ne (heq ▸ ht)
    rw [List.foldl_cons, entries_foldl_files_of_head_ne ht rest _
      (fun f hf => hne f (List.mem_cons_of_mem _ hf))]
    simp only [Arm64.FsState.setFile, Arm64.FsState.setEntry, hfile_ne]
    exact entries_foldl_anc_of_head_ne ht _ fs hanc

private theorem initFsState_entries_of_head_ne {inp : Arm64.Process.ProcessInputs}
    {target : Arm64.FsPath} {d : String}
    (ht : target.head? = some d) (hdirs : inp.dirs = [])
    (hfiles : ∀ f ∈ inp.files, (Arm64.normalizePath f.1).head? ≠ some d) :
    (Arm64.Process.initFsState inp).entries target = ({} : Arm64.FsState).entries target := by
  unfold Arm64.Process.initFsState
  rw [hdirs, List.foldl_nil]
  exact entries_foldl_files_of_head_ne ht inp.files ({} : Arm64.FsState) hfiles

theorem filesOf_eq_none_of_head_ne {files : List (String × HwBytes)} {p d : String}
    (hp : (Arm64.normalizePath p).head? = some d)
    (hfiles : ∀ f ∈ files, (Arm64.normalizePath f.1).head? ≠ some d) :
    filesOf files p = none := by
  unfold filesOf fsView
  split
  · rfl
  · have hne_empty : (Arm64.normalizePath p).isEmpty = false := by
      cases hn : Arm64.normalizePath p with
      | nil => rw [hn] at hp; cases hp
      | cons _ _ => rfl
    simp only [Arm64.FsState.files, Arm64.FsState.getEntry, hne_empty, Bool.false_eq_true, ↓reduceIte]
    rw [initFsState_entries_of_head_ne hp rfl hfiles]
    simp [hne_empty]

theorem normalizePath_sessionPathOf_head (r : ProtocolSetup) (p : Participant) :
    (Arm64.normalizePath (sessionPathOf r p)).head? = some "sessions" :=
  normalizePath_head_slash "sessions" (peerOf r p).text (by decide) (by decide)

theorem normalizePath_oneTimePreKeyFile_head (id : BitVec 32) :
    (Arm64.normalizePath (oneTimePreKeyFile id)).head? = some "one-time-pre-keys" :=
  normalizePath_head_slash "one-time-pre-keys" (toString id.toNat) (by decide) (by decide)

private theorem commonFiles_head_ne_sessions (interp : ExternInterpretation) (r : ProtocolSetup)
    (p : Participant) :
    ∀ f ∈ commonFiles interp r p, (Arm64.normalizePath f.1).head? ≠ some "sessions" := by
  intro f hf
  simp only [commonFiles, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only
    rw [show identityFile (peerNameOf r p) = ("identities" ++ "/") ++ peerNameOf r p from rfl,
      normalizePath_head_slash "identities" (peerNameOf r p) (by decide) (by decide)]
    decide

private theorem bobPreKeyFiles_head_ne_sessions (interp : ExternInterpretation) (r : ProtocolSetup) :
    ∀ f ∈ bobPreKeyFiles interp r, (Arm64.normalizePath f.1).head? ≠ some "sessions" := by
  intro f hf
  unfold bobPreKeyFiles at hf
  rw [List.mem_append] at hf
  rcases hf with hf | hf
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · dsimp only
      rw [show signedPreKeyFile r.spkId = ("signed-pre-keys" ++ "/") ++ toString r.spkId.toNat from rfl,
        normalizePath_head_slash "signed-pre-keys" _ (by decide) (by decide)]
      decide
    · dsimp only
      rw [show lastResortKyberPreKeyFile r.kpkId =
          ("last-resort-kyber-pre-keys" ++ "/") ++ toString r.kpkId.toNat from rfl,
        normalizePath_head_slash "last-resort-kyber-pre-keys" _ (by decide) (by decide)]
      decide
    · dsimp only
      rw [show baseKeysFile r.kpkId =
          ("last-resort-kyber-pre-keys" ++ "/") ++ (toString r.kpkId.toNat ++ ".base-keys") from rfl,
        normalizePath_head_slash "last-resort-kyber-pre-keys" _ (by decide) (by decide)]
      decide
  · cases hw : r.withOpk
    · simp [hw] at hf
    · simp only [hw, ↓reduceIte, List.mem_singleton] at hf
      subst hf
      dsimp only
      rw [normalizePath_oneTimePreKeyFile_head]
      decide

theorem initDirs_sessionPathOf_eq_none (interp : ExternInterpretation) (r : ProtocolSetup)
    (p q : Participant) :
    initDirs interp r p (sessionPathOf r q) = none := by
  unfold initDirs
  split
  · exact filesOf_eq_none_of_head_ne (normalizePath_sessionPathOf_head r q)
      (commonFiles_head_ne_sessions interp r p)
  · split
    · refine filesOf_eq_none_of_head_ne (normalizePath_sessionPathOf_head r q) fun f hf => ?_
      rcases List.mem_append.mp hf with h1 | h2
      · exact commonFiles_head_ne_sessions interp r p f h1
      · exact bobPreKeyFiles_head_ne_sessions interp r f h2
    · rfl

@[simp] theorem cliInit_records_eq_none (interp : ExternInterpretation) (r : ProtocolSetup) :
    (CliTurn.init (initDirs interp r)).records r = fun _ => none := by
  funext p
  unfold CliTurn.init CliTurn.records
  simp [initDirs_sessionPathOf_eq_none]

@[simp] theorem cliInit_leakRecords_eq_none (interp : ExternInterpretation) (r : ProtocolSetup) :
    (CliTurn.init (initDirs interp r)).leakRecords r = fun _ => none := by
  funext p
  unfold CliTurn.leakRecords
  rw [cliInit_records_eq_none]
  simp [CliTurn.init]

end Symbolic.Swarm.CREF.CliPure
