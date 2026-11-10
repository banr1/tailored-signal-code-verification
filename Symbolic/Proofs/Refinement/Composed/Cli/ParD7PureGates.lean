/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model

/-!
# Flat-Bundle Directory Round-Trip and Injectivity Lemmas

Proves field-parser round-trip lemmas, flatness and `parseBundleFiles` round-trip for canonical
`publicBundleOf` directories, injectivity of `publicBundleOf`, and reflexivity of `ScrubAgree`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY.Libsignal (HwBytes)
open CryptoVerification.E2E (PreKeyBundleFields djbKey)
open CryptoVerification.SignalSession
  (Inputs Outcome PublicBundle PqParty filesOf bundleDir pqInitInputs pqxdhExpectedOutcome pqInitModel PqxdhPartyInSpecDomain
   publicBundleOf)

private theorem extractLsb'_append_eq {W : Nat} (b : BitVec W) (s₂ s₁ n₂ n₁ : Nat)
    (h : s₂ = s₁ + n₁) : b.extractLsb' s₂ n₂ ++ b.extractLsb' s₁ n₁ = b.extractLsb' s₁ (n₂ + n₁) := by
  subst h; ext i hi; simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split <;> [rfl; (congr 1; omega)]

private theorem extractLsb_concat_32 (x : BitVec 32) :
    x.extractLsb' 24 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 0 8 = x := by
  rw [extractLsb'_append_eq x 24 16 8 8 rfl, extractLsb'_append_eq x 16 8 16 8 rfl,
    extractLsb'_append_eq x 8 0 24 8 rfl]; ext i hi; simp

theorem bundleU32_le32 (x : BitVec 32) :
    bundleU32 (CryptoVerification.SignalSession.le32 x) = some x := by
  simp only [CryptoVerification.SignalSession.le32, bundleU32, Option.some.injEq]
  exact extractLsb_concat_32 x

theorem bundleSplitId_le32 (x : BitVec 32) (rest : HwBytes) :
    bundleSplitId (CryptoVerification.SignalSession.le32 x ++ rest) = some (x, rest) := by
  simp only [CryptoVerification.SignalSession.le32, List.cons_append, List.nil_append,
    bundleSplitId, bundleU32, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  exact extractLsb_concat_32 x

theorem bundleSplitSigned_le32 (id : BitVec 32) (key sig : HwBytes) (hsig : sig.length = 64) :
    bundleSplitSigned (CryptoVerification.SignalSession.le32 id ++ key ++ sig) =
      some (id, key, sig) := by
  rw [List.append_assoc]; unfold bundleSplitSigned; rw [bundleSplitId_le32]
  have hge : 64 ≤ (key ++ sig).length := by rw [List.length_append, hsig]; omega
  have hsub : (key ++ sig).length - 64 = key.length := by rw [List.length_append, hsig]; omega
  simp only [hge, ↓reduceIte, hsub, List.take_left, List.drop_left]

theorem parseEcKey_djbKey (v : List.Vector (BitVec 8) 32) :
    parseEcKey (djbKey v) = some (djbKey v) := by
  have hlen : v.toList.length = 32 := v.2
  have htake : v.toList.take 32 = v.toList := List.take_of_length_le (by omega)
  simp [djbKey, parseEcKey, ecKeyParses, hlen, htake]

theorem parseKyberKey_kyberKey (v : List.Vector (BitVec 8) 1568) :
    parseKyberKey (CryptoVerification.E2E.kyberKey v) = some (CryptoVerification.E2E.kyberKey v) := by
  have hlen : v.toList.length = 1568 := v.2
  simp only [CryptoVerification.E2E.kyberKey, parseKyberKey, hlen, and_self, ↓reduceIte]

theorem filesOf_publicBundleOf (b : PreKeyBundleFields) :
    filesOf ((publicBundleOf b).files bundleDir) (bundleDir ++ "/" ++ "identity-key") =
      some (djbKey b.idPub) ∧
    filesOf ((publicBundleOf b).files bundleDir) (bundleDir ++ "/" ++ "registration-id") =
      some (CryptoVerification.SignalSession.le32 b.regId) ∧
    filesOf ((publicBundleOf b).files bundleDir) (bundleDir ++ "/" ++ "signed-pre-key") =
      some (CryptoVerification.SignalSession.le32 b.spkId ++ djbKey b.spkPub ++ b.spkSig.toList) ∧
    filesOf ((publicBundleOf b).files bundleDir) (bundleDir ++ "/" ++ "kyber-pre-key") =
      some (CryptoVerification.SignalSession.le32 b.kpkId ++
        CryptoVerification.E2E.kyberKey b.kpkPub ++ b.kpkSig.toList) ∧
    filesOf ((publicBundleOf b).files bundleDir) (bundleDir ++ "/" ++ "one-time-pre-key") =
      (b.opk.map fun (id, k) => CryptoVerification.SignalSession.le32 id ++ djbKey k) := by
  rcases b with ⟨_, _ | ⟨_, _⟩, _, _, _, _, _, _, _⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bundleFilesFlat_publicBundleOf (b : PreKeyBundleFields) :
    BundleFilesFlat ((publicBundleOf b).files bundleDir) := by
  intro f hf
  simp only [publicBundleOf, PublicBundle.files, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl) | hot_mem
  · refine ⟨⟨"identity-key", by dsimp only; decide⟩, ?_⟩
    have h1 : b.idPub.toList.length = 32 := b.idPub.2
    simp only [djbKey, List.length_cons, h1]; omega
  · refine ⟨⟨"registration-id", by dsimp only; decide⟩, ?_⟩
    simp only [CryptoVerification.SignalSession.le32, List.length_cons, List.length_nil]; omega
  · refine ⟨⟨"signed-pre-key", by dsimp only; decide⟩, ?_⟩
    have h1 : b.spkPub.toList.length = 32 := b.spkPub.2
    have h2 : b.spkSig.toList.length = 64 := b.spkSig.2
    simp only [CryptoVerification.SignalSession.le32, djbKey, List.length_append,
      List.length_cons, List.length_nil, h1, h2]; omega
  · refine ⟨⟨"kyber-pre-key", by dsimp only; decide⟩, ?_⟩
    have h1 : b.kpkPub.toList.length = 1568 := b.kpkPub.2
    have h2 : b.kpkSig.toList.length = 64 := b.kpkSig.2
    simp only [CryptoVerification.SignalSession.le32, CryptoVerification.E2E.kyberKey,
      List.length_append, List.length_cons, List.length_nil, h1, h2]; omega
  · cases ho : b.opk with
    | none => simp [ho] at hot_mem
    | some p =>
      rcases p with ⟨oid, okey⟩
      simp only [ho, Option.map_some, List.mem_singleton] at hot_mem; subst hot_mem
      refine ⟨⟨"one-time-pre-key", by dsimp only; decide⟩, ?_⟩
      have h1 : okey.toList.length = 32 := okey.2
      simp only [CryptoVerification.SignalSession.le32, djbKey, List.length_append,
        List.length_cons, List.length_nil, h1]; omega

theorem parseBundleFiles_publicBundleOf (b : PreKeyBundleFields) :
    parseBundleFiles (filesOf ((publicBundleOf b).files bundleDir)) = some (publicBundleOf b) := by
  obtain ⟨f_ik, f_reg, f_spk, f_kpk, f_opk⟩ := filesOf_publicBundleOf b
  unfold parseBundleFiles; dsimp only [bind, Option.bind]
  rw [f_ik, Option.getD_some, parseEcKey_djbKey b.idPub,
    f_reg, Option.getD_some, bundleU32_le32 b.regId,
    f_spk, Option.getD_some, bundleSplitSigned_le32 b.spkId (djbKey b.spkPub) b.spkSig.toList b.spkSig.2,
    f_kpk, Option.getD_some,
    bundleSplitSigned_le32 b.kpkId (CryptoVerification.E2E.kyberKey b.kpkPub) b.kpkSig.toList b.kpkSig.2,
    f_opk]
  cases ho : b.opk with
  | none =>
    dsimp only [Option.map, Option.getD]
    rw [parseEcKey_djbKey b.spkPub, parseKyberKey_kyberKey b.kpkPub]
    simp [publicBundleOf, ho]
  | some p =>
    rcases p with ⟨oid, okey⟩
    have hsplit := bundleSplitId_le32 oid (djbKey okey)
    dsimp only [Option.map, Option.getD, CryptoVerification.SignalSession.le32,
      List.cons_append, List.nil_append] at hsplit ⊢
    rw [hsplit]; dsimp only
    rw [parseEcKey_djbKey okey]; dsimp only
    rw [parseEcKey_djbKey b.spkPub, parseKyberKey_kyberKey b.kpkPub]
    simp [publicBundleOf, ho]

theorem publicBundleOf_injective {b₁ b₂ : PreKeyBundleFields}
    (h : publicBundleOf b₁ = publicBundleOf b₂) : b₁ = b₂ := by
  cases b₁ with | mk reg₁ opk₁ spkId₁ spkPub₁ spkSig₁ kpkId₁ kpkPub₁ kpkSig₁ idPub₁ =>
  cases b₂ with | mk reg₂ opk₂ spkId₂ spkPub₂ spkSig₂ kpkId₂ kpkPub₂ kpkSig₂ idPub₂ =>
  simp only [publicBundleOf, PublicBundle.mk.injEq, djbKey, CryptoVerification.E2E.kyberKey,
    List.cons.injEq, true_and] at h
  rcases h with ⟨hid, rfl, rfl, hspk, hssig, rfl, hkpk, hksig, hopk⟩
  cases Subtype.ext hid; cases Subtype.ext hspk; cases Subtype.ext hssig
  cases Subtype.ext hkpk; cases Subtype.ext hksig; congr 1
  cases opk₁ with
  | none => cases opk₂ <;> simp at hopk; rfl
  | some p₁ =>
    cases opk₂ with
    | none => simp at hopk
    | some p₂ =>
      rcases p₁ with ⟨i₁, k₁⟩; rcases p₂ with ⟨i₂, k₂⟩
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and]
        at hopk
      exact congrArg some (Prod.ext hopk.1 (Subtype.ext hopk.2))

theorem ScrubAgree.refl (o : Outcome) : ScrubAgree o o := by cases o <;> simp [ScrubAgree]

end DY.Libsignal.Composed.Refinement.Cli
