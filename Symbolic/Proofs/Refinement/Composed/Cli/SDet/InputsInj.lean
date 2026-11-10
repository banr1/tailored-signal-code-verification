/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Repr
public import Symbolic.Proofs.Refinement.Composed.Cli.Model
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.CodecInj
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.FilesOfAlg

/-!
# CLI Input Separation and Argument Extraction

Proves off-diagonal `InputsEquiv` disjointness between `init`, `send`, and `recv` PQXDH model
inputs and extracts equal call arguments and `encodeDir` snapshots from matching clauses.
-/

@[expose] public section

set_option autoImplicit false

namespace InputsInjAux

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement.Cli (InputsEquiv)
open DY.Libsignal.Composed.Refinement.Cli.SDet
open CryptoVerification.E2E
open CryptoVerification.SignalSession

private theorem filesOf_eq_none_of_forall_ne {files : List (String × HwBytes)} {p : String}
    (hreg : RegularFileList files)
    (hne : ∀ f ∈ files, Arm64.normalizePath f.1 ≠ Arm64.normalizePath p) :
    filesOf files p = none := by
  cases hf : filesOf files p with
  | none => rfl
  | some b =>
    obtain ⟨f, hmem, hp, _⟩ := mem_of_filesOf_eq_some hreg hf
    exact False.elim (hne f hmem hp)

private theorem encodeDir_norm_ne_coins_and_bundle (P : PEParams) (st : PqParty)
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
    | some k =>
      simp only [hp, List.mem_singleton] at h; subst h; dsimp only
      cases st.party <;> decide
  · cases hs : st.session with
    | none => simp [hs] at h
    | some xg =>
      simp only [hs, List.mem_singleton] at h; subst h; dsimp only
      cases st.party <;> decide
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (signedPreKeyFile i) = ["signed-pre-keys", toString i.toNat] := by
      simpa [signedPreKeyFile] using
        normalizePath_dir_nat_suf (d := "signed-pre-keys") (suf := "") i.toNat
          (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (oneTimePreKeyFile i) = ["one-time-pre-keys", toString i.toNat] := by
      simpa [oneTimePreKeyFile] using
        normalizePath_dir_nat_suf (d := "one-time-pre-keys") (suf := "") i.toNat
          (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (oneTimeKyberPreKeyFile i) =
        ["one-time-kyber-pre-keys", toString i.toNat] := by
      simpa [oneTimeKyberPreKeyFile] using
        normalizePath_dir_nat_suf (d := "one-time-kyber-pre-keys") (suf := "") i.toNat
          (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨l, ⟨⟨i, _, _⟩, _, rfl⟩, hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · have hn : Arm64.normalizePath (lastResortKyberPreKeyFile i) =
          ["last-resort-kyber-pre-keys", toString i.toNat] := by
        simpa [lastResortKyberPreKeyFile] using
          normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := "") i.toNat
            (by decide) (by decide) (by decide) (by decide)
      dsimp only; rw [hn]
      exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
        fun he => absurd (Option.some.inj he) (by decide)⟩
    · have hn : Arm64.normalizePath (baseKeysFile i) =
          ["last-resort-kyber-pre-keys", toString i.toNat ++ ".base-keys"] := by
        simpa [baseKeysFile] using
          normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := ".base-keys") i.toNat
            (by decide) (by decide) (by decide) (by decide)
      dsimp only; rw [hn]
      exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
        fun he => absurd (Option.some.inj he) (by decide)⟩

private theorem filesOf_encodeDir_eq_none_of_coins (P : PEParams) (st : PqParty) {p : String}
    (hp : Arm64.normalizePath p = ["coins"]) :
    filesOf (encodeDir P st) p = none :=
  filesOf_eq_none_of_forall_ne (regularFileList_encodeDir P st) fun _ hf => by
    rw [hp]; exact (encodeDir_norm_ne_coins_and_bundle P st hf).1

private theorem filesOf_encodeDir_eq_none_of_bundle (P : PEParams) (st : PqParty) {p : String}
    (hp : (Arm64.normalizePath p).head? = some "bundle") :
    filesOf (encodeDir P st) p = none :=
  filesOf_eq_none_of_forall_ne (regularFileList_encodeDir P st) fun _ hf he =>
    (encodeDir_norm_ne_coins_and_bundle P st hf).2 (he ▸ hp)

private theorem filesOf_coins_self (c : HwBytes) :
    filesOf [(coinsFile, c)] coinsFile = some c := by
  rw [filesOf_eq_optFold (regularFileList_coins c)]
  simp

private theorem filesOf_append_coins_self {l : List (String × HwBytes)} (hl : RegularFileList l)
    (c : HwBytes) :
    filesOf (l ++ [(coinsFile, c)]) coinsFile = some c := by
  rw [filesOf_append_of_regular hl (regularFileList_coins c), filesOf_coins_self]
  rfl

private theorem filesOf_coins_eq_none (c : HwBytes) {p : String}
    (hp : Arm64.normalizePath p ≠ ["coins"]) :
    filesOf [(coinsFile, c)] p = none :=
  filesOf_eq_none_of_forall_ne (regularFileList_coins c) fun f hf he => by
    rw [List.mem_singleton] at hf; subst hf
    have hc : Arm64.normalizePath coinsFile = ["coins"] := by decide
    exact hp (he.symm.trans hc)

private theorem bundle_files_norm_head (b : PublicBundle) {f : String × HwBytes}
    (hf : f ∈ b.files bundleDir) :
    (Arm64.normalizePath f.1).head? = some "bundle" := by
  unfold PublicBundle.files at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl) | ho
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · cases hot : b.oneTime with
    | none => simp [hot] at ho
    | some ik =>
      rcases ik with ⟨_, _⟩
      simp only [hot, List.mem_singleton] at ho; subst ho
      dsimp only; decide

private theorem filesOf_bundle_eq_none (b : PublicBundle) {p : String}
    (hp : (Arm64.normalizePath p).head? ≠ some "bundle") :
    filesOf (b.files bundleDir) p = none :=
  filesOf_eq_none_of_forall_ne (regularFileList_bundle_files b) fun _ hf he =>
    hp (he ▸ bundle_files_norm_head b hf)

theorem strip_coins_filesOf (P : PEParams) (st₀ st₁ : PqParty) (c₀ c₁ : HwBytes)
    (hfiles : ∀ p, filesOf (encodeDir P st₀ ++ [] ++ [(coinsFile, c₀)]) p =
                   filesOf (encodeDir P st₁ ++ [] ++ [(coinsFile, c₁)]) p) :
    c₀ = c₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p := by
  have hr₀ := (regularFileList_encodeDir P st₀).append RegularFileList.nil
  have hr₁ := (regularFileList_encodeDir P st₁).append RegularFileList.nil
  have hc : c₀ = c₁ := by
    have h0 := hfiles coinsFile
    rw [filesOf_append_coins_self hr₀, filesOf_append_coins_self hr₁] at h0
    exact Option.some.inj h0
  refine ⟨hc, fun p => ?_⟩
  by_cases hpc : Arm64.normalizePath p = ["coins"]
  · rw [filesOf_encodeDir_eq_none_of_coins P st₀ hpc, filesOf_encodeDir_eq_none_of_coins P st₁ hpc]
  · have h0 := hfiles p
    rw [filesOf_append_of_regular hr₀ (regularFileList_coins c₀),
        filesOf_append_of_regular hr₁ (regularFileList_coins c₁),
        filesOf_coins_eq_none c₀ hpc, filesOf_coins_eq_none c₁ hpc,
        Option.none_or, Option.none_or] at h0
    simpa [List.append_nil] using h0

private theorem pqInitInputs_at_bundle (P : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) {p : String}
    (hpb : (Arm64.normalizePath p).head? = some "bundle")
    (hpc : Arm64.normalizePath p ≠ ["coins"]) :
    filesOf (pqInitInputs P st b t).files p = filesOf ((publicBundleOf b).files bundleDir) p := by
  change filesOf (encodeDir P st ++ (publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)]) p = _
  rw [filesOf_append_of_regular
        ((regularFileList_encodeDir P st).append (regularFileList_bundle_files (publicBundleOf b)))
        (regularFileList_coins t.toList),
      filesOf_coins_eq_none t.toList hpc, Option.none_or,
      filesOf_append_of_regular (regularFileList_encodeDir P st)
        (regularFileList_bundle_files (publicBundleOf b)),
      filesOf_encodeDir_eq_none_of_bundle P st hpb, Option.or_none]

private theorem eval_bundle_files (b : PublicBundle) :
    filesOf (b.files bundleDir) "bundle/identity-key" = some b.identityKey ∧
    filesOf (b.files bundleDir) "bundle/registration-id" = some (le32 b.registrationId) ∧
    filesOf (b.files bundleDir) "bundle/signed-pre-key" =
      some (le32 b.signedId ++ b.signedKey ++ b.signedSig) ∧
    filesOf (b.files bundleDir) "bundle/kyber-pre-key" =
      some (le32 b.kyberId ++ b.kyberKey ++ b.kyberSig) ∧
    filesOf (b.files bundleDir) "bundle/one-time-pre-key" =
      b.oneTime.map (fun (id, key) => le32 id ++ key) := by
  have hr := regularFileList_bundle_files b
  have h_ik_ik : (Arm64.normalizePath "bundle/identity-key" == Arm64.normalizePath (bundleDir ++ "/identity-key")) = true := by decide
  have h_ik_rg : (Arm64.normalizePath "bundle/identity-key" == Arm64.normalizePath (bundleDir ++ "/registration-id")) = false := by decide
  have h_ik_sp : (Arm64.normalizePath "bundle/identity-key" == Arm64.normalizePath (bundleDir ++ "/signed-pre-key")) = false := by decide
  have h_ik_kp : (Arm64.normalizePath "bundle/identity-key" == Arm64.normalizePath (bundleDir ++ "/kyber-pre-key")) = false := by decide
  have h_ik_ot : (Arm64.normalizePath "bundle/identity-key" == Arm64.normalizePath (bundleDir ++ "/one-time-pre-key")) = false := by decide
  have h_rg_ik : (Arm64.normalizePath "bundle/registration-id" == Arm64.normalizePath (bundleDir ++ "/identity-key")) = false := by decide
  have h_rg_rg : (Arm64.normalizePath "bundle/registration-id" == Arm64.normalizePath (bundleDir ++ "/registration-id")) = true := by decide
  have h_rg_sp : (Arm64.normalizePath "bundle/registration-id" == Arm64.normalizePath (bundleDir ++ "/signed-pre-key")) = false := by decide
  have h_rg_kp : (Arm64.normalizePath "bundle/registration-id" == Arm64.normalizePath (bundleDir ++ "/kyber-pre-key")) = false := by decide
  have h_rg_ot : (Arm64.normalizePath "bundle/registration-id" == Arm64.normalizePath (bundleDir ++ "/one-time-pre-key")) = false := by decide
  have h_sp_ik : (Arm64.normalizePath "bundle/signed-pre-key" == Arm64.normalizePath (bundleDir ++ "/identity-key")) = false := by decide
  have h_sp_rg : (Arm64.normalizePath "bundle/signed-pre-key" == Arm64.normalizePath (bundleDir ++ "/registration-id")) = false := by decide
  have h_sp_sp : (Arm64.normalizePath "bundle/signed-pre-key" == Arm64.normalizePath (bundleDir ++ "/signed-pre-key")) = true := by decide
  have h_sp_kp : (Arm64.normalizePath "bundle/signed-pre-key" == Arm64.normalizePath (bundleDir ++ "/kyber-pre-key")) = false := by decide
  have h_sp_ot : (Arm64.normalizePath "bundle/signed-pre-key" == Arm64.normalizePath (bundleDir ++ "/one-time-pre-key")) = false := by decide
  have h_kp_ik : (Arm64.normalizePath "bundle/kyber-pre-key" == Arm64.normalizePath (bundleDir ++ "/identity-key")) = false := by decide
  have h_kp_rg : (Arm64.normalizePath "bundle/kyber-pre-key" == Arm64.normalizePath (bundleDir ++ "/registration-id")) = false := by decide
  have h_kp_sp : (Arm64.normalizePath "bundle/kyber-pre-key" == Arm64.normalizePath (bundleDir ++ "/signed-pre-key")) = false := by decide
  have h_kp_kp : (Arm64.normalizePath "bundle/kyber-pre-key" == Arm64.normalizePath (bundleDir ++ "/kyber-pre-key")) = true := by decide
  have h_kp_ot : (Arm64.normalizePath "bundle/kyber-pre-key" == Arm64.normalizePath (bundleDir ++ "/one-time-pre-key")) = false := by decide
  have h_ot_ik : (Arm64.normalizePath "bundle/one-time-pre-key" == Arm64.normalizePath (bundleDir ++ "/identity-key")) = false := by decide
  have h_ot_rg : (Arm64.normalizePath "bundle/one-time-pre-key" == Arm64.normalizePath (bundleDir ++ "/registration-id")) = false := by decide
  have h_ot_sp : (Arm64.normalizePath "bundle/one-time-pre-key" == Arm64.normalizePath (bundleDir ++ "/signed-pre-key")) = false := by decide
  have h_ot_kp : (Arm64.normalizePath "bundle/one-time-pre-key" == Arm64.normalizePath (bundleDir ++ "/kyber-pre-key")) = false := by decide
  have h_ot_ot : (Arm64.normalizePath "bundle/one-time-pre-key" == Arm64.normalizePath (bundleDir ++ "/one-time-pre-key")) = true := by decide
  rw [filesOf_eq_optFold hr, filesOf_eq_optFold hr, filesOf_eq_optFold hr,
      filesOf_eq_optFold hr, filesOf_eq_optFold hr]
  unfold PublicBundle.files
  cases hot : b.oneTime with
  | none =>
    simp only [List.append_nil, List.foldl_cons, List.foldl_nil, Option.map_none,
      h_ik_ik, h_ik_rg, h_ik_sp, h_ik_kp,
      h_rg_ik, h_rg_rg, h_rg_sp, h_rg_kp,
      h_sp_ik, h_sp_rg, h_sp_sp, h_sp_kp,
      h_kp_ik, h_kp_rg, h_kp_sp, h_kp_kp,
      h_ot_ik, h_ot_rg, h_ot_sp, h_ot_kp,
      Bool.false_eq_true, ↓reduceIte, and_self]
  | some ik =>
    rcases ik with ⟨id, key⟩
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil, Option.map_some,
      h_ik_ik, h_ik_rg, h_ik_sp, h_ik_kp, h_ik_ot,
      h_rg_ik, h_rg_rg, h_rg_sp, h_rg_kp, h_rg_ot,
      h_sp_ik, h_sp_rg, h_sp_sp, h_sp_kp, h_sp_ot,
      h_kp_ik, h_kp_rg, h_kp_sp, h_kp_kp, h_kp_ot,
      h_ot_ik, h_ot_rg, h_ot_sp, h_ot_kp, h_ot_ot,
      Bool.false_eq_true, ↓reduceIte, and_self]

private theorem bundleE_eq_of_publicBundle_files_eq {b₀ b₁ : PreKeyBundleFields}
    (hik : filesOf ((publicBundleOf b₀).files bundleDir) "bundle/identity-key" =
           filesOf ((publicBundleOf b₁).files bundleDir) "bundle/identity-key")
    (hrg : filesOf ((publicBundleOf b₀).files bundleDir) "bundle/registration-id" =
           filesOf ((publicBundleOf b₁).files bundleDir) "bundle/registration-id")
    (hsp : filesOf ((publicBundleOf b₀).files bundleDir) "bundle/signed-pre-key" =
           filesOf ((publicBundleOf b₁).files bundleDir) "bundle/signed-pre-key")
    (hkp : filesOf ((publicBundleOf b₀).files bundleDir) "bundle/kyber-pre-key" =
           filesOf ((publicBundleOf b₁).files bundleDir) "bundle/kyber-pre-key")
    (hot : filesOf ((publicBundleOf b₀).files bundleDir) "bundle/one-time-pre-key" =
           filesOf ((publicBundleOf b₁).files bundleDir) "bundle/one-time-pre-key") :
    b₀ = b₁ := by
  obtain ⟨e0_ik, e0_rg, e0_sp, e0_kp, e0_ot⟩ := eval_bundle_files (publicBundleOf b₀)
  obtain ⟨e1_ik, e1_rg, e1_sp, e1_kp, e1_ot⟩ := eval_bundle_files (publicBundleOf b₁)
  rw [e0_ik, e1_ik] at hik
  rw [e0_rg, e1_rg] at hrg
  rw [e0_sp, e1_sp] at hsp
  rw [e0_kp, e1_kp] at hkp
  rw [e0_ot, e1_ot] at hot
  unfold publicBundleOf at hik hrg hsp hkp hot
  dsimp only at hik hrg hsp hkp hot
  have hidPub : b₀.idPub = b₁.idPub := djbKey_inj (Option.some.inj hik)
  have hregId : b₀.regId = b₁.regId := le32_inj (Option.some.inj hrg)
  obtain ⟨hsp12, hspSig⟩ := List.append_inj (Option.some.inj hsp)
    (by simp [le32_length, djbKey_length])
  obtain ⟨hspkId_b, hspkPub_b⟩ := List.append_inj hsp12 (by simp [le32_length])
  have hspkId : b₀.spkId = b₁.spkId := le32_inj hspkId_b
  have hspkPub : b₀.spkPub = b₁.spkPub := djbKey_inj hspkPub_b
  have hspkSig_eq : b₀.spkSig = b₁.spkSig := Subtype.ext hspSig
  obtain ⟨hkp12, hkpSig⟩ := List.append_inj (Option.some.inj hkp)
    (by simp [le32_length, kyberKey_length])
  obtain ⟨hkpkId_b, hkpkPub_b⟩ := List.append_inj hkp12 (by simp [le32_length])
  have hkpkId : b₀.kpkId = b₁.kpkId := le32_inj hkpkId_b
  have hkpkPub : b₀.kpkPub = b₁.kpkPub := kyberKey_inj hkpkPub_b
  have hkpkSig_eq : b₀.kpkSig = b₁.kpkSig := Subtype.ext hkpSig
  have hopk : b₀.opk = b₁.opk := by
    cases ho0 : b₀.opk <;> cases ho1 : b₁.opk
    · rfl
    · simp [ho0, ho1] at hot
    · simp [ho0, ho1] at hot
    · rename_i p0 p1
      rcases p0 with ⟨i0, k0⟩; rcases p1 with ⟨i1, k1⟩
      simp only [ho0, ho1, Option.map_some, Option.some.injEq] at hot
      obtain ⟨hi, hk⟩ := List.append_inj hot (by simp [le32_length])
      rw [le32_inj hi, djbKey_inj hk]
  cases b₀; cases b₁
  dsimp only at hregId hopk hspkId hspkPub hspkSig_eq hkpkId hkpkPub hkpkSig_eq hidPub
  rw [hregId, hopk, hspkId, hspkPub, hspkSig_eq, hkpkId, hkpkPub, hkpkSig_eq, hidPub]

theorem pqInitInputs_extract {P : PEParams} {st₀ st₁ : PqParty}
    {b₀ b₁ : PreKeyBundleFields} {t₀ t₁ : List.Vector (BitVec 8) initiateTapeLen}
    (h : InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqInitInputs P st₁ b₁ t₁)) :
    b₀ = b₁ ∧ t₀ = t₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p := by
  have hfiles := h.2.2.2
  have ht : t₀ = t₁ := by
    have hc := hfiles coinsFile
    change filesOf (encodeDir P st₀ ++ (publicBundleOf b₀).files bundleDir ++ [(coinsFile, t₀.toList)]) coinsFile =
           filesOf (encodeDir P st₁ ++ (publicBundleOf b₁).files bundleDir ++ [(coinsFile, t₁.toList)]) coinsFile at hc
    rw [filesOf_append_coins_self
          ((regularFileList_encodeDir P st₀).append (regularFileList_bundle_files (publicBundleOf b₀))),
        filesOf_append_coins_self
          ((regularFileList_encodeDir P st₁).append (regularFileList_bundle_files (publicBundleOf b₁)))] at hc
    exact Subtype.ext (Option.some.inj hc)
  have hb : b₀ = b₁ := by
    refine bundleE_eq_of_publicBundle_files_eq ?_ ?_ ?_ ?_ ?_
    · rw [← pqInitInputs_at_bundle P st₀ b₀ t₀ (by decide) (by decide),
          ← pqInitInputs_at_bundle P st₁ b₁ t₁ (by decide) (by decide)]
      exact hfiles "bundle/identity-key"
    · rw [← pqInitInputs_at_bundle P st₀ b₀ t₀ (by decide) (by decide),
          ← pqInitInputs_at_bundle P st₁ b₁ t₁ (by decide) (by decide)]
      exact hfiles "bundle/registration-id"
    · rw [← pqInitInputs_at_bundle P st₀ b₀ t₀ (by decide) (by decide),
          ← pqInitInputs_at_bundle P st₁ b₁ t₁ (by decide) (by decide)]
      exact hfiles "bundle/signed-pre-key"
    · rw [← pqInitInputs_at_bundle P st₀ b₀ t₀ (by decide) (by decide),
          ← pqInitInputs_at_bundle P st₁ b₁ t₁ (by decide) (by decide)]
      exact hfiles "bundle/kyber-pre-key"
    · rw [← pqInitInputs_at_bundle P st₀ b₀ t₀ (by decide) (by decide),
          ← pqInitInputs_at_bundle P st₁ b₁ t₁ (by decide) (by decide)]
      exact hfiles "bundle/one-time-pre-key"
  refine ⟨hb, ht, fun p => ?_⟩
  by_cases hpc : Arm64.normalizePath p = ["coins"]
  · rw [filesOf_encodeDir_eq_none_of_coins P st₀ hpc, filesOf_encodeDir_eq_none_of_coins P st₁ hpc]
  · by_cases hpb : (Arm64.normalizePath p).head? = some "bundle"
    · rw [filesOf_encodeDir_eq_none_of_bundle P st₀ hpb, filesOf_encodeDir_eq_none_of_bundle P st₁ hpb]
    · have hp := hfiles p
      change filesOf (encodeDir P st₀ ++ (publicBundleOf b₀).files bundleDir ++ [(coinsFile, t₀.toList)]) p =
             filesOf (encodeDir P st₁ ++ (publicBundleOf b₁).files bundleDir ++ [(coinsFile, t₁.toList)]) p at hp
      rw [filesOf_append_of_regular
            ((regularFileList_encodeDir P st₀).append (regularFileList_bundle_files (publicBundleOf b₀)))
            (regularFileList_coins t₀.toList),
          filesOf_append_of_regular
            ((regularFileList_encodeDir P st₁).append (regularFileList_bundle_files (publicBundleOf b₁)))
            (regularFileList_coins t₁.toList),
          filesOf_coins_eq_none t₀.toList hpc, filesOf_coins_eq_none t₁.toList hpc,
          Option.none_or, Option.none_or,
          filesOf_append_of_regular (regularFileList_encodeDir P st₀)
            (regularFileList_bundle_files (publicBundleOf b₀)),
          filesOf_append_of_regular (regularFileList_encodeDir P st₁)
            (regularFileList_bundle_files (publicBundleOf b₁)),
          filesOf_bundle_eq_none (publicBundleOf b₀) hpb,
          filesOf_bundle_eq_none (publicBundleOf b₁) hpb,
          Option.none_or, Option.none_or] at hp
      exact hp

end InputsInjAux

namespace DY.Libsignal.Composed.Refinement.Cli.SDet

open DY.Libsignal (HwBytes)
open CryptoVerification.E2E (PreKeyBundleFields PreKeyMessageFields PEParams initiateTapeLen wireWhisper wirePrekey)
open CryptoVerification.SignalSession

/-! ## Off-diagonal clause separation -/
theorem inputsEquiv_pqInitInputs_pqSendInputs_false {P : PEParams} {st₀ st₁ : PqParty}
    {b₀ : PreKeyBundleFields} {t₀ : List.Vector (BitVec 8) initiateTapeLen}
    {m₁ : HwBytes} {r₁ : List.Vector (BitVec 8) 64}
    (h : InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqSendInputs P st₁ m₁ r₁)) : False := by
  have h0 : (some "init" : Option String) = some "send" := congrArg List.head? h.1
  revert h0; decide

theorem inputsEquiv_pqInitInputs_pqRecvInputs_false {P : PEParams} {st₀ st₁ : PqParty}
    {b₀ : PreKeyBundleFields} {t₀ : List.Vector (BitVec 8) initiateTapeLen}
    {c₁ : HwBytes} {rc₁ : BitVec 256}
    (h : InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqRecvInputs P st₁ c₁ rc₁)) : False := by
  have h0 : (some "init" : Option String) = some "recv" := congrArg List.head? h.1
  revert h0; decide

theorem inputsEquiv_pqSendInputs_pqRecvInputs_false {P : PEParams} {st₀ st₁ : PqParty}
    {m₀ : HwBytes} {r₀ : List.Vector (BitVec 8) 64}
    {c₁ : HwBytes} {rc₁ : BitVec 256}
    (h : InputsEquiv (pqSendInputs P st₀ m₀ r₀) (pqRecvInputs P st₁ c₁ rc₁)) : False := by
  have h0 : (some "send" : Option String) = some "recv" := congrArg List.head? h.1
  revert h0; decide

theorem inputsEquiv_pqRecvWhisper_pqRecvPrekey_false {P : PEParams} {st₀ st₁ : PqParty}
    {body₀ : HwBytes} {rc₀ : BitVec 256} {m₁ : PreKeyMessageFields} {rc₁ : BitVec 256}
    (h : InputsEquiv (pqRecvInputs P st₀ (wireWhisper :: body₀) rc₀)
                     (pqRecvInputs P st₁ (wirePrekey :: m₁.bytes) rc₁)) : False := by
  have h0 : wireWhisper = wirePrekey := (List.cons.inj h.2.2.1).1
  revert h0; decide

theorem inputsEquiv_pqRecvWhisper_other_false {P : PEParams} {st₀ st₁ : PqParty}
    {body₀ : HwBytes} {rc₀ : BitVec 256} {c₁ : HwBytes} {rc₁ : BitVec 256}
    (hc₁ : c₁.head? ≠ some wireWhisper)
    (h : InputsEquiv (pqRecvInputs P st₀ (wireWhisper :: body₀) rc₀)
                     (pqRecvInputs P st₁ c₁ rc₁)) : False := by
  have hs : wireWhisper :: body₀ = c₁ := h.2.2.1
  exact hc₁ (by rw [← hs]; rfl)

theorem inputsEquiv_pqRecvPrekey_other_false {P : PEParams} {st₀ st₁ : PqParty}
    {m₀ : PreKeyMessageFields} {rc₀ : BitVec 256} {c₁ : HwBytes} {rc₁ : BitVec 256}
    (hc₁ : c₁.head? ≠ some wirePrekey)
    (h : InputsEquiv (pqRecvInputs P st₀ (wirePrekey :: m₀.bytes) rc₀)
                     (pqRecvInputs P st₁ c₁ rc₁)) : False := by
  have hs : wirePrekey :: m₀.bytes = c₁ := h.2.2.1
  exact hc₁ (by rw [← hs]; rfl)

/-! ## Same-clause argument extraction -/
theorem inputsEquiv_pqInitInputs_extract {P : PEParams} {st₀ st₁ : PqParty}
    {b₀ b₁ : PreKeyBundleFields} {t₀ t₁ : List.Vector (BitVec 8) initiateTapeLen}
    (h : InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqInitInputs P st₁ b₁ t₁)) :
    b₀ = b₁ ∧ t₀ = t₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p :=
  InputsInjAux.pqInitInputs_extract h

theorem inputsEquiv_pqSendInputs_extract {P : PEParams} {st₀ st₁ : PqParty}
    {m₀ m₁ : HwBytes} {r₀ r₁ : List.Vector (BitVec 8) 64}
    (h : InputsEquiv (pqSendInputs P st₀ m₀ r₀) (pqSendInputs P st₁ m₁ r₁)) :
    m₀ = m₁ ∧ r₀ = r₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p := by
  obtain ⟨hr, hdir⟩ := InputsInjAux.strip_coins_filesOf P st₀ st₁ r₀.toList r₁.toList h.2.2.2
  exact ⟨h.2.2.1, Subtype.ext hr, hdir⟩

theorem inputsEquiv_pqRecvWhisper_extract {P : PEParams} {st₀ st₁ : PqParty}
    {body₀ body₁ : HwBytes} {rc₀ rc₁ : BitVec 256}
    (h : InputsEquiv (pqRecvInputs P st₀ (wireWhisper :: body₀) rc₀)
                     (pqRecvInputs P st₁ (wireWhisper :: body₁) rc₁)) :
    body₀ = body₁ ∧ rc₀ = rc₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p := by
  obtain ⟨hrc, hdir⟩ := InputsInjAux.strip_coins_filesOf P st₀ st₁
    (CryptoGames.HMAC.keyToBytes32 rc₀) (CryptoGames.HMAC.keyToBytes32 rc₁) h.2.2.2
  exact ⟨(List.cons.inj h.2.2.1).2, keyToBytes32_inj hrc, hdir⟩

theorem inputsEquiv_pqRecvPrekey_extract {P : PEParams} {st₀ st₁ : PqParty}
    {m₀ m₁ : PreKeyMessageFields} {rc₀ rc₁ : BitVec 256}
    (hlen₀ : m₀.inner.length + 2048 < 2 ^ 32)
    (hlen₁ : m₁.inner.length + 2048 < 2 ^ 32)
    (h : InputsEquiv (pqRecvInputs P st₀ (wirePrekey :: m₀.bytes) rc₀)
                     (pqRecvInputs P st₁ (wirePrekey :: m₁.bytes) rc₁)) :
    m₀ = m₁ ∧ rc₀ = rc₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p := by
  have _ := hlen₀; have _ := hlen₁
  obtain ⟨hrc, hdir⟩ := InputsInjAux.strip_coins_filesOf P st₀ st₁
    (CryptoGames.HMAC.keyToBytes32 rc₀) (CryptoGames.HMAC.keyToBytes32 rc₁) h.2.2.2
  exact ⟨preKeyMsgE_bytes_inj (List.cons.inj h.2.2.1).2, keyToBytes32_inj hrc, hdir⟩

end DY.Libsignal.Composed.Refinement.Cli.SDet
