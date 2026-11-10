/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.FilesExtParity
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Input Extensionality for Two-Placement `cliRunPlacedSig`

Input-visibility predicates (`FilesVisibleRaw`) and `InputsEquivRaw` extensionality lemmas for
`Placed.cliRunPlacedSig mpl mmpl elf W` and `CliReachesOOMPlaced mpl mmpl elf W`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3

open Arm64 (hasDotDot hasLeadingSlash)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.E2E (PEParams PreKeyBundleFields initiateTapeLen)
open CryptoVerification.SignalSession (
  CliHooks CliReachesOOMPlaced Cmd Inputs Outcome OutcomeOrExcusedAbort PqParty PublicBundle
  baseKeysFile bundleDir cliProcessInputs encodeDir pqInitInputs pqInputs
  pqRecvInputs pqSendInputs publicBundleOf stdioPaths
)
open CryptoVerification.SignalSession.Placed (CliRunsToPlaced cliRunPlacedSig)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity (
  FilesExtVisibleRaw FilesVisibleRaw InputsEquivRaw LoadableFile
  loadState_eq_of_inputsEquiv_of_visible_of_loadable loadState_error_of_not_loadable_files
  visible_of_head_slash
)

private theorem visible_of_slash_prefix (seg rest : String) (hns : '/' ∉ seg.toList)
    (hok : (!seg.isEmpty && seg != ".") = true)
    (hstd : some seg ∉ (stdioPaths.map Arm64.normalizePath).map List.head?) :
    Arm64.normalizePath ((seg ++ "/") ++ rest) ≠ [] ∧
      Arm64.normalizePath ((seg ++ "/") ++ rest) ∉ stdioPaths.map Arm64.normalizePath :=
  visible_of_head_slash seg rest rfl hns hok hstd

theorem filesVisibleRaw_encodeDir (P : PEParams) (st : PqParty) :
    FilesVisibleRaw (encodeDir P st) := by
  intro x hx
  unfold encodeDir at hx
  simp only [List.mem_append] at hx
  rcases hx with ((((((hpre | hpeer) | hsess) | hsigned) | hot) | hkot) | hklr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpre
    rcases hpre with rfl | rfl | rfl <;> exact ⟨by dsimp only; decide, by dsimp only; decide⟩
  · cases hp : st.peerId <;> simp only [hp, List.not_mem_nil, List.mem_singleton] at hpeer
    subst hpeer
    exact visible_of_slash_prefix "identities" _ (by decide) (by decide) (by decide)
  · rcases hs : st.session with _ | ⟨_, _⟩ <;>
      simp only [hs, List.not_mem_nil, List.mem_singleton] at hsess
    subst hsess
    exact visible_of_slash_prefix "sessions" _ (by decide) (by decide) (by decide)
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp hsigned
    exact visible_of_slash_prefix "signed-pre-keys" _ (by decide) (by decide) (by decide)
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp hot
    exact visible_of_slash_prefix "one-time-pre-keys" _ (by decide) (by decide) (by decide)
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp hkot
    exact visible_of_slash_prefix "one-time-kyber-pre-keys" _ (by decide) (by decide) (by decide)
  · obtain ⟨_, hl, hp⟩ := List.mem_flatten.mp hklr
    obtain ⟨⟨_, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact visible_of_slash_prefix "last-resort-kyber-pre-keys" _ (by decide) (by decide) (by decide)
    · dsimp only
      unfold baseKeysFile
      rw [String.append_assoc]
      exact visible_of_slash_prefix "last-resort-kyber-pre-keys" _ (by decide) (by decide) (by decide)

theorem filesVisibleRaw_bundle_files (b : PublicBundle) :
    FilesVisibleRaw (b.files bundleDir) := by
  intro f hf
  unfold PublicBundle.files at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl) | hot
  · exact ⟨by dsimp only; decide, by dsimp only; decide⟩
  · exact ⟨by dsimp only; decide, by dsimp only; decide⟩
  · exact ⟨by dsimp only; decide, by dsimp only; decide⟩
  · exact ⟨by dsimp only; decide, by dsimp only; decide⟩
  · rcases hopk : b.oneTime with _ | ⟨_, _⟩ <;>
      simp only [hopk, List.not_mem_nil, List.mem_singleton] at hot
    subst hot
    exact ⟨by dsimp only; decide, by dsimp only; decide⟩

theorem filesVisibleRaw_pqInputs (P : PEParams) (st : PqParty) (cmd : Cmd)
    (extra : List (String × List (BitVec 8))) (coins stdin : List (BitVec 8))
    (hextra : FilesVisibleRaw extra) :
    FilesVisibleRaw (pqInputs P st cmd extra coins stdin).files := by
  intro f hf
  unfold pqInputs at hf
  dsimp only at hf
  simp only [List.mem_append, List.mem_singleton] at hf
  rcases hf with (he | hx) | rfl
  · exact filesVisibleRaw_encodeDir P st f he
  · exact hextra f hx
  · exact ⟨by dsimp only; decide, by dsimp only; decide⟩

theorem filesVisibleRaw_pqInitInputs (P : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    FilesVisibleRaw (pqInitInputs P st b t).files :=
  filesVisibleRaw_pqInputs P st _ _ _ _ (filesVisibleRaw_bundle_files (publicBundleOf b))

theorem filesVisibleRaw_pqSendInputs (P : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    FilesVisibleRaw (pqSendInputs P st m r).files :=
  filesVisibleRaw_pqInputs P st _ [] _ _ (fun _ h => nomatch h)

theorem filesVisibleRaw_pqRecvInputs (P : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    FilesVisibleRaw (pqRecvInputs P st c rc).files :=
  filesVisibleRaw_pqInputs P st _ [] _ _ (fun _ h => nomatch h)

theorem cliRunPlacedSig_eq_none_of_loadState_error {mpl mmpl : MultiPlacement}
    {elf : ElfImage} {W : CliHooks} {i : Inputs} {msg : String}
    (herr : elf.loadState (cliProcessInputs i) = .error msg) :
    cliRunPlacedSig mpl mmpl elf W i = none := by
  unfold cliRunPlacedSig
  split
  · rename_i hex
    rcases hex with ⟨_, s0, hload, _⟩
    rw [herr] at hload
    cases hload
  · rfl

theorem filesExtVisible_cliRunPlacedSig (mpl mmpl : MultiPlacement) (elf : ElfImage)
    (W : CliHooks) : FilesExtVisibleRaw (cliRunPlacedSig mpl mmpl elf W) :=
  fun i i' heq hvis hvis' hload' => by
    by_cases hload : ∀ f ∈ i.files, LoadableFile f
    · right
      have hls := loadState_eq_of_inputsEquiv_of_visible_of_loadable elf heq hvis hvis' hload hload'
      unfold cliRunPlacedSig CliRunsToPlaced
      rw [hls]
    · obtain ⟨_, herr⟩ := loadState_error_of_not_loadable_files (elf := elf) hload
      exact Or.inl (cliRunPlacedSig_eq_none_of_loadState_error herr)

theorem cliRunPlacedSig_some_of_inputsEquiv {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {i i' : Inputs} {o : Outcome}
    (heq : InputsEquivRaw i i') (hvis : FilesVisibleRaw i.files) (hvis' : FilesVisibleRaw i'.files)
    (hload' : ∀ f ∈ i'.files, LoadableFile f)
    (hr : cliRunPlacedSig mpl mmpl elf W i = some o) :
    cliRunPlacedSig mpl mmpl elf W i' = some o := by
  rcases filesExtVisible_cliRunPlacedSig mpl mmpl elf W i i' heq hvis hvis' hload' with hnone | hsame
  · rw [hr] at hnone
    cases hnone
  · exact hsame.symm.trans hr

theorem exited_of_outcomeUpTo_raw_placed {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {i i₀ : Inputs} {Pred : Outcome → Prop}
    {code : Nat} {out : List (BitVec 8)} {files : String → Option (List (BitVec 8))}
    (hr : cliRunPlacedSig mpl mmpl elf W i = some (.exited code out files))
    (hup : OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) i₀ Pred)
    (heq : InputsEquivRaw i i₀) (hvis : FilesVisibleRaw i.files) (hvis₀ : FilesVisibleRaw i₀.files)
    (hload₀ : ∀ f ∈ i₀.files, hasLeadingSlash f.1 = false ∧ hasDotDot f.1 = false) :
    Pred (.exited code out files) := by
  have hnoErr₀ : ∀ msg, elf.loadState (cliProcessInputs i₀) ≠ .error msg := by
    intro msg herr
    rcases hup with ⟨_, ho₀, _⟩ | ⟨_, ⟨s0, _, hok, _⟩⟩
    · have hn := cliRunPlacedSig_eq_none_of_loadState_error (mpl := mpl) (mmpl := mmpl) (W := W) herr
      rw [ho₀] at hn
      cases hn
    · rw [herr] at hok
      cases hok
  have hloadFile₀ : ∀ f ∈ i₀.files, LoadableFile f := fun f hf =>
    ⟨hload₀ f hf, Classical.byContradiction fun hlen => by
      obtain ⟨msg, herr⟩ := loadState_error_of_not_loadable_files (elf := elf) (i := i₀)
        (fun hall => hlen (hall f hf).2)
      exact hnoErr₀ msg herr⟩
  have hr₀ := cliRunPlacedSig_some_of_inputsEquiv heq hvis hvis₀ hloadFile₀ hr
  rcases hup with ⟨o₀, ho₀, hP⟩ | ⟨hab, _⟩
  · rw [hr₀] at ho₀
    injection ho₀ with ho'
    exact ho' ▸ hP
  · rw [hr₀] at hab
    cases hab

theorem exited_of_or_none_outcomeUpTo_eq_raw_placed {mpl mmpl : MultiPlacement}
    {elf : ElfImage} {W : CliHooks}
    {exc : Inputs → Prop} {i : Inputs} {expected : Outcome}
    {code : Nat} {out : List (BitVec 8)} {files : String → Option (List (BitVec 8))}
    (hr : cliRunPlacedSig mpl mmpl elf W i = some (.exited code out files))
    (hor : cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort exc (cliRunPlacedSig mpl mmpl elf W) i (· = expected)) :
    Outcome.exited code out files = expected := by
  rcases hor with hnone | (⟨o₀, ho₀, hP⟩ | ⟨hab, _⟩)
  · rw [hr] at hnone
    cases hnone
  · rw [hr] at ho₀
    injection ho₀ with ho'
    exact ho'.trans hP
  · rw [hr] at hab
    cases hab

end LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3
