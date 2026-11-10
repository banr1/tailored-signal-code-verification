/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Repr
public import Symbolic.Proofs.Refinement.Composed.Cli.Model
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.FilesOfAlg
import Symbolic.Proofs.Refinement.Composed.Cli.ParD7PureGates

/-!
# Flat-Bundle `init` Separation and Extraction

Proves disjointness of flat-bundle `pqInitInputsF` from `send`/`recv` inputs and extracts the
parsed public bundle, coin tape, and `encodeDir` snapshot under `InputsEquiv`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli.SDet

open DY.Libsignal (HwBytes)
open CryptoVerification.E2E (PreKeyBundleFields PEParams initiateTapeLen)
open CryptoVerification.SignalSession

theorem regularFileList_of_bundleFilesFlat {files : List (String × HwBytes)}
    (hflat : BundleFilesFlat files) : RegularFileList files := by
  intro f hf
  obtain ⟨⟨name, hnorm⟩, _⟩ := hflat f hf
  exact regularFile_two hnorm (by decide) f (List.mem_singleton.mpr rfl)

theorem regularFileList_pqInitInputsF (P : PEParams) (st : PqParty)
    {files : List (String × HwBytes)} (hflat : BundleFilesFlat files)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    RegularFileList (pqInitInputsF P st files t).files :=
  ((regularFileList_encodeDir P st).append (regularFileList_of_bundleFilesFlat hflat)).append
    (regularFileList_coins t.toList)

theorem pqSendInputs_pqInitInputsF_false {P : PEParams} {st₀ st₁ : PqParty}
    {m₀ : HwBytes} {r₀ : List.Vector (BitVec 8) 64}
    {files₁ : List (String × HwBytes)} {t₁ : List.Vector (BitVec 8) initiateTapeLen}
    (h : InputsEquiv (pqSendInputs P st₀ m₀ r₀) (pqInitInputsF P st₁ files₁ t₁)) : False := by
  have h0 : (some "send" : Option String) = some "init" := congrArg List.head? h.1
  revert h0; decide

theorem pqRecvInputs_pqInitInputsF_false {P : PEParams} {st₀ st₁ : PqParty}
    {c₀ : HwBytes} {rc₀ : BitVec 256}
    {files₁ : List (String × HwBytes)} {t₁ : List.Vector (BitVec 8) initiateTapeLen}
    (h : InputsEquiv (pqRecvInputs P st₀ c₀ rc₀) (pqInitInputsF P st₁ files₁ t₁)) : False := by
  have h0 : (some "recv" : Option String) = some "init" := congrArg List.head? h.1
  revert h0; decide

private theorem filesOf_eq_none_of_forall_ne' {files : List (String × HwBytes)} {p : String}
    (hreg : RegularFileList files)
    (hne : ∀ f ∈ files, Arm64.normalizePath f.1 ≠ Arm64.normalizePath p) :
    filesOf files p = none := by
  cases hf : filesOf files p with
  | none => rfl
  | some b =>
    obtain ⟨f, hmem, hp, _⟩ := mem_of_filesOf_eq_some hreg hf
    exact False.elim (hne f hmem hp)

private theorem encodeDir_norm_ne_coins_and_bundle' (P : PEParams) (st : PqParty)
    {f : String × HwBytes} (hf : f ∈ encodeDir P st) :
    Arm64.normalizePath f.1 ≠ ["coins"] ∧ (Arm64.normalizePath f.1).head? ≠ some "bundle" := by
  unfold encodeDir at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatten, or_assoc] at hf
  rcases hf with rfl | rfl | rfl | h | h | h | h | h | h
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · cases hp : st.peerId with
    | none => simp [hp] at h
    | some k => simp only [hp, List.mem_singleton] at h; subst h; dsimp only; cases st.party <;> decide
  · cases hs : st.session with
    | none => simp [hs] at h
    | some xg => simp only [hs, List.mem_singleton] at h; subst h; dsimp only; cases st.party <;> decide
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (signedPreKeyFile i) = ["signed-pre-keys", toString i.toNat] := by
      simpa [signedPreKeyFile] using normalizePath_dir_nat_suf (d := "signed-pre-keys") (suf := "") i.toNat
        (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (oneTimePreKeyFile i) = ["one-time-pre-keys", toString i.toNat] := by
      simpa [oneTimePreKeyFile] using normalizePath_dir_nat_suf (d := "one-time-pre-keys") (suf := "") i.toNat
        (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (oneTimeKyberPreKeyFile i) = ["one-time-kyber-pre-keys", toString i.toNat] := by
      simpa [oneTimeKyberPreKeyFile] using normalizePath_dir_nat_suf (d := "one-time-kyber-pre-keys") (suf := "") i.toNat
        (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨l, ⟨⟨i, _, _⟩, _, rfl⟩, hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · have hn : Arm64.normalizePath (lastResortKyberPreKeyFile i) = ["last-resort-kyber-pre-keys", toString i.toNat] := by
        simpa [lastResortKyberPreKeyFile] using normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := "") i.toNat
          (by decide) (by decide) (by decide) (by decide)
      dsimp only; rw [hn]
      exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
        fun he => absurd (Option.some.inj he) (by decide)⟩
    · have hn : Arm64.normalizePath (baseKeysFile i) = ["last-resort-kyber-pre-keys", toString i.toNat ++ ".base-keys"] := by
        simpa [baseKeysFile] using normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := ".base-keys") i.toNat
          (by decide) (by decide) (by decide) (by decide)
      dsimp only; rw [hn]
      exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
        fun he => absurd (Option.some.inj he) (by decide)⟩

private theorem filesOf_encodeDir_eq_none_of_coins' (P : PEParams) (st : PqParty) {p : String}
    (hp : Arm64.normalizePath p = ["coins"]) : filesOf (encodeDir P st) p = none :=
  filesOf_eq_none_of_forall_ne' (regularFileList_encodeDir P st) fun _ hf => by
    rw [hp]; exact (encodeDir_norm_ne_coins_and_bundle' P st hf).1

private theorem filesOf_encodeDir_eq_none_of_bundle' (P : PEParams) (st : PqParty) {p : String}
    (hp : (Arm64.normalizePath p).head? = some "bundle") : filesOf (encodeDir P st) p = none :=
  filesOf_eq_none_of_forall_ne' (regularFileList_encodeDir P st) fun _ hf he =>
    (encodeDir_norm_ne_coins_and_bundle' P st hf).2 (he ▸ hp)

private theorem filesOf_append_coins_self' {l : List (String × HwBytes)} (hl : RegularFileList l)
    (c : HwBytes) : filesOf (l ++ [(coinsFile, c)]) coinsFile = some c := by
  have hs : filesOf [(coinsFile, c)] coinsFile = some c := by
    rw [filesOf_eq_optFold (regularFileList_coins c)]; simp
  rw [filesOf_append_of_regular hl (regularFileList_coins c), hs]; rfl

private theorem filesOf_coins_eq_none' (c : HwBytes) {p : String}
    (hp : Arm64.normalizePath p ≠ ["coins"]) : filesOf [(coinsFile, c)] p = none :=
  filesOf_eq_none_of_forall_ne' (regularFileList_coins c) fun f hf he => by
    rw [List.mem_singleton] at hf; subst hf
    exact hp (he.symm.trans (by decide : Arm64.normalizePath coinsFile = ["coins"]))

private theorem flat_norm_head {files : List (String × HwBytes)} (hflat : BundleFilesFlat files)
    {f : String × HwBytes} (hf : f ∈ files) :
    (Arm64.normalizePath f.1).head? = some "bundle" := by
  obtain ⟨⟨name, hnorm⟩, _⟩ := hflat f hf; rw [hnorm]; rfl

private theorem filesOf_flat_eq_none {files : List (String × HwBytes)}
    (hflat : BundleFilesFlat files) {p : String}
    (hp : (Arm64.normalizePath p).head? ≠ some "bundle") : filesOf files p = none :=
  filesOf_eq_none_of_forall_ne' (regularFileList_of_bundleFilesFlat hflat) fun _ hf he =>
    hp (he ▸ flat_norm_head hflat hf)

private theorem pqInitInputsF_at_bundle (P : PEParams) (st : PqParty)
    {files : List (String × HwBytes)} (hflat : BundleFilesFlat files)
    (t : List.Vector (BitVec 8) initiateTapeLen) {p : String}
    (hpb : (Arm64.normalizePath p).head? = some "bundle")
    (hpc : Arm64.normalizePath p ≠ ["coins"]) :
    filesOf (pqInitInputsF P st files t).files p = filesOf files p := by
  change filesOf (encodeDir P st ++ files ++ [(coinsFile, t.toList)]) p = _
  rw [filesOf_append_of_regular
        ((regularFileList_encodeDir P st).append (regularFileList_of_bundleFilesFlat hflat))
        (regularFileList_coins t.toList),
      filesOf_coins_eq_none' t.toList hpc, Option.none_or,
      filesOf_append_of_regular (regularFileList_encodeDir P st)
        (regularFileList_of_bundleFilesFlat hflat),
      filesOf_encodeDir_eq_none_of_bundle' P st hpb, Option.or_none]

private theorem parseBundleFiles_eq_of_five {d₀ d₁ : DirectorySnapshot}
    (h1 : d₀ (bundleDir ++ "/" ++ "identity-key") = d₁ (bundleDir ++ "/" ++ "identity-key"))
    (h2 : d₀ (bundleDir ++ "/" ++ "registration-id") = d₁ (bundleDir ++ "/" ++ "registration-id"))
    (h3 : d₀ (bundleDir ++ "/" ++ "signed-pre-key") = d₁ (bundleDir ++ "/" ++ "signed-pre-key"))
    (h4 : d₀ (bundleDir ++ "/" ++ "kyber-pre-key") = d₁ (bundleDir ++ "/" ++ "kyber-pre-key"))
    (h5 : d₀ (bundleDir ++ "/" ++ "one-time-pre-key") = d₁ (bundleDir ++ "/" ++ "one-time-pre-key")) :
    parseBundleFiles d₀ = parseBundleFiles d₁ := by
  unfold parseBundleFiles; dsimp only; rw [h1, h2, h3, h4, h5]

theorem pqInitInputs_pqInitInputsF_extract {P : PEParams} {st₀ st₁ : PqParty}
    {b₀ : PreKeyBundleFields} {files₁ : List (String × HwBytes)}
    {t₀ t₁ : List.Vector (BitVec 8) initiateTapeLen}
    (hflat₁ : BundleFilesFlat files₁)
    (h : InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqInitInputsF P st₁ files₁ t₁)) :
    parseBundleFiles (filesOf files₁) = some (publicBundleOf b₀) ∧
      t₀ = t₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p := by
  have hfiles := h.2.2.2
  have hflat₀ := bundleFilesFlat_publicBundleOf b₀
  have hreg₀ := (regularFileList_encodeDir P st₀).append (regularFileList_of_bundleFilesFlat hflat₀)
  have hreg₁ := (regularFileList_encodeDir P st₁).append (regularFileList_of_bundleFilesFlat hflat₁)
  have ht : t₀ = t₁ := by
    have hc := hfiles coinsFile
    change filesOf (encodeDir P st₀ ++ (publicBundleOf b₀).files bundleDir ++ [(coinsFile, t₀.toList)]) coinsFile =
           filesOf (encodeDir P st₁ ++ files₁ ++ [(coinsFile, t₁.toList)]) coinsFile at hc
    rw [filesOf_append_coins_self' hreg₀, filesOf_append_coins_self' hreg₁] at hc
    exact Subtype.ext (Option.some.inj hc)
  have hfive : ∀ {p : String}, (Arm64.normalizePath p).head? = some "bundle" →
      Arm64.normalizePath p ≠ ["coins"] →
      filesOf ((publicBundleOf b₀).files bundleDir) p = filesOf files₁ p := by
    intro p hpb hpc
    rw [← pqInitInputsF_at_bundle P st₀ hflat₀ t₀ hpb hpc,
        ← pqInitInputsF_at_bundle P st₁ hflat₁ t₁ hpb hpc]
    exact hfiles p
  have hpb : parseBundleFiles (filesOf files₁) = some (publicBundleOf b₀) := by
    rw [← parseBundleFiles_eq_of_five
      (hfive (by decide) (by decide)) (hfive (by decide) (by decide))
      (hfive (by decide) (by decide)) (hfive (by decide) (by decide))
      (hfive (by decide) (by decide))]
    exact parseBundleFiles_publicBundleOf b₀
  refine ⟨hpb, ht, fun p => ?_⟩
  by_cases hpc : Arm64.normalizePath p = ["coins"]
  · rw [filesOf_encodeDir_eq_none_of_coins' P st₀ hpc, filesOf_encodeDir_eq_none_of_coins' P st₁ hpc]
  · by_cases hpb' : (Arm64.normalizePath p).head? = some "bundle"
    · rw [filesOf_encodeDir_eq_none_of_bundle' P st₀ hpb', filesOf_encodeDir_eq_none_of_bundle' P st₁ hpb']
    · have hp := hfiles p
      change filesOf (encodeDir P st₀ ++ (publicBundleOf b₀).files bundleDir ++ [(coinsFile, t₀.toList)]) p =
             filesOf (encodeDir P st₁ ++ files₁ ++ [(coinsFile, t₁.toList)]) p at hp
      rw [filesOf_append_of_regular hreg₀ (regularFileList_coins t₀.toList),
          filesOf_append_of_regular hreg₁ (regularFileList_coins t₁.toList),
          filesOf_coins_eq_none' t₀.toList hpc, filesOf_coins_eq_none' t₁.toList hpc,
          Option.none_or, Option.none_or,
          filesOf_append_of_regular (regularFileList_encodeDir P st₀) (regularFileList_of_bundleFilesFlat hflat₀),
          filesOf_append_of_regular (regularFileList_encodeDir P st₁) (regularFileList_of_bundleFilesFlat hflat₁),
          filesOf_flat_eq_none hflat₀ hpb', filesOf_flat_eq_none hflat₁ hpb',
          Option.none_or, Option.none_or] at hp
      exact hp

end DY.Libsignal.Composed.Refinement.Cli.SDet
