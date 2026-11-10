/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Repr
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.CommitEval

@[expose] public section

set_option autoImplicit false

/-!
# PQXDH Directory Commit Equivalence

Proves `filesOf_pqCommit`, showing that appending `[identityFile, sessionFile]` to an encoded
PQXDH store directory induces the same `filesOf` view as re-encoding the updated `PqParty` state.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Agree

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunRefine

/-! ## Path classification for `encodeDir` -/

private theorem gameFilePath_of_twoSeg {p d suf : String}
    (hn : normalizePath p = [d, suf]) (hd : d ∈ storeParentDirs) :
    GameFilePath p := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hn]; rfl
  · intro d' _; rw [hn]; simp
  · intro pref hpref
    have hdrop : (FsPath.nonEmptyPrefixes [d, suf]).dropLast = [[d]] := rfl
    rw [hn, hdrop, List.mem_singleton] at hpref
    exact ⟨d, hd, hpref⟩

private theorem norm_identityFile (P : Party) :
    normalizePath (identityFile (partyAddressName P)) = ["identities", partyAddressName P] := by
  cases P <;> decide

private theorem norm_sessionFile (P : Party) :
    normalizePath (sessionFile (partyAddress P)) = ["sessions", (partyAddress P).text] := by
  cases P <;> decide

private theorem norm_signedPreKeyFile (i : BitVec 32) :
    normalizePath (signedPreKeyFile i) = ["signed-pre-keys", toString i.toNat] :=
  norm_prekey_nat "signed-pre-keys" i.toNat (by decide) (by decide)

private theorem norm_oneTimePreKeyFile (i : BitVec 32) :
    normalizePath (oneTimePreKeyFile i) = ["one-time-pre-keys", toString i.toNat] :=
  norm_prekey_nat "one-time-pre-keys" i.toNat (by decide) (by decide)

private theorem norm_oneTimeKyberPreKeyFile (i : BitVec 32) :
    normalizePath (oneTimeKyberPreKeyFile i) = ["one-time-kyber-pre-keys", toString i.toNat] :=
  norm_prekey_nat "one-time-kyber-pre-keys" i.toNat (by decide) (by decide)

private theorem norm_lastResortKyberPreKeyFile (i : BitVec 32) :
    normalizePath (lastResortKyberPreKeyFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat] :=
  norm_prekey_nat "last-resort-kyber-pre-keys" i.toNat (by decide) (by decide)

private theorem norm_baseKeysFile (i : BitVec 32) :
    normalizePath (baseKeysFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat ++ ".base-keys"] :=
  norm_basekeys_nat "last-resort-kyber-pre-keys" i.toNat (by decide) (by decide)

private def pqRoot3 (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  [(addressFile, textBytes (partyAddress st.party).text),
   (identityKeyPairFile, RecordCodecs.IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩),
   (registrationIdFile, SignalSession.le32 st.me.regId)]

private def pqMid (st : PqParty) : List (String × List (BitVec 8)) :=
  (match st.peerId with
   | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
   | none => []) ++
  (match st.session with
   | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
   | none => [])

private def pqPost (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)) ++
  st.oneTime.map (fun (i, k) =>
    (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) =>
    (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten

private theorem encodeDir_split (W : PEParams) (st : PqParty) :
    encodeDir W st = pqRoot3 W st ++ pqMid st ++ pqPost W st := by
  unfold encodeDir pqRoot3 pqMid pqPost
  simp only [List.append_assoc]
  rfl

private def prekeyDirs : List String :=
  ["signed-pre-keys", "one-time-pre-keys", "one-time-kyber-pre-keys", "last-resort-kyber-pre-keys"]

private theorem pqRoot3_props (W : PEParams) (st : PqParty) :
    ∀ x ∈ pqRoot3 W st, GameFilePath x.1 ∧
      normalizePath x.1 ∈ [["address"], ["identity-key-pair"], ["registration-id"]] := by
  intro x hx
  simp only [pqRoot3, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    (dsimp only; exact ⟨⟨by decide, by decide, by decide⟩, by decide⟩)

private theorem pqMid_props (st : PqParty) :
    ∀ x ∈ pqMid st, GameFilePath x.1 ∧
      ∃ d ∈ ["identities", "sessions"], ∃ s, normalizePath x.1 = [d, s] := by
  intro x hx
  simp only [pqMid, List.mem_append] at hx
  rcases hx with h | h
  · cases hp : st.peerId with
    | none => simp [hp] at h
    | some k =>
      simp only [hp, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact ⟨gameFilePath_of_twoSeg (norm_identityFile _) (by decide),
        "identities", by decide, _, norm_identityFile _⟩
  · cases hs : st.session with
    | none => simp [hs] at h
    | some xg =>
      obtain ⟨xv, gv⟩ := xg
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact ⟨gameFilePath_of_twoSeg (norm_sessionFile _) (by decide),
        "sessions", by decide, _, norm_sessionFile _⟩

private theorem pqPost_props (W : PEParams) (st : PqParty) :
    ∀ x ∈ pqPost W st, GameFilePath x.1 ∧
      ∃ d ∈ prekeyDirs, ∃ s, normalizePath x.1 = [d, s] := by
  intro x hx
  simp only [pqPost, List.mem_append, List.mem_map, List.mem_flatten, or_assoc] at hx
  rcases hx with h | h | h | h
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := h
    exact ⟨gameFilePath_of_twoSeg (norm_signedPreKeyFile i) (by decide),
      "signed-pre-keys", by decide, _, norm_signedPreKeyFile i⟩
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := h
    exact ⟨gameFilePath_of_twoSeg (norm_oneTimePreKeyFile i) (by decide),
      "one-time-pre-keys", by decide, _, norm_oneTimePreKeyFile i⟩
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := h
    exact ⟨gameFilePath_of_twoSeg (norm_oneTimeKyberPreKeyFile i) (by decide),
      "one-time-kyber-pre-keys", by decide, _, norm_oneTimeKyberPreKeyFile i⟩
  · obtain ⟨l, ⟨⟨i, _, _⟩, _, rfl⟩, hl⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨gameFilePath_of_twoSeg (norm_lastResortKyberPreKeyFile i) (by decide),
        "last-resort-kyber-pre-keys", by decide, _, norm_lastResortKyberPreKeyFile i⟩
    · exact ⟨gameFilePath_of_twoSeg (norm_baseKeysFile i) (by decide),
        "last-resort-kyber-pre-keys", by decide, _, norm_baseKeysFile i⟩

private theorem coins_gameFilePath : GameFilePath coinsFile :=
  ⟨by decide, by decide, by decide⟩

private theorem norm_coinsFile : normalizePath coinsFile = ["coins"] := by decide

/-- Appending `[identityFile, sessionFile]` to `encodeDir W st ++ [(coinsFile, coins)]` yields the
same `filesOf` view as `encodeDir W` on the updated `PqParty` state. -/
theorem filesOf_pqCommit (W : PEParams) (st : PqParty) (coins : List (BitVec 8))
    (k : IdentityKey) (x : RecordExtras) (g' : GhostState (List (BitVec 8))) :
    let files := encodeDir W st ++ [(coinsFile, coins)]
    let ws := [(identityFile (partyAddressName st.party.other), k.serialize),
               (sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g')]
    let st' : PqParty := { st with peerId := some k, session := some (x, g') }
    filesOf (files ++ ws) = filesOf (files ++ encodeDir W st') := by
  intro files ws st'
  have hst'_mid : pqMid st' = ws := rfl
  have hst'_root : pqRoot3 W st' = pqRoot3 W st := rfl
  have hst'_post : pqPost W st' = pqPost W st := rfl
  have hws_props : ∀ y ∈ ws, GameFilePath y.1 ∧
      ∃ d ∈ ["identities", "sessions"], ∃ s, normalizePath y.1 = [d, s] :=
    hst'_mid ▸ pqMid_props st'
  have henc_gp : ∀ st0 : PqParty, ∀ y ∈ encodeDir W st0, GameFilePath y.1 := by
    intro st0 y hy
    rw [encodeDir_split] at hy
    simp only [List.mem_append, or_assoc] at hy
    rcases hy with h | h | h
    · exact (pqRoot3_props W st0 y h).1
    · exact (pqMid_props st0 y h).1
    · exact (pqPost_props W st0 y h).1
  have hfiles_gp : ∀ y ∈ files, GameFilePath y.1 := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact henc_gp st y h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; exact coins_gameFilePath
  have hlhs_gp : ∀ y ∈ files ++ ws, GameFilePath y.1 := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact hfiles_gp y h
    · exact (hws_props y h).1
  have hrhs_gp : ∀ y ∈ files ++ encodeDir W st', GameFilePath y.1 := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact hfiles_gp y h
    · exact henc_gp st' y h
  funext p
  rw [filesOf_eq_evalAt hlhs_gp p, filesOf_eq_evalAt hrhs_gp p]
  split
  · rfl
  · split
    · rfl
    · generalize normalizePath p = q
      have hsplit_st : files = pqRoot3 W st ++ pqMid st ++ pqPost W st ++ [(coinsFile, coins)] := by
        simp [files, encodeDir_split, List.append_assoc]
      have hsplit_st' : encodeDir W st' = pqRoot3 W st ++ ws ++ pqPost W st := by
        rw [encodeDir_split, hst'_root, hst'_mid, hst'_post]
      rw [hsplit_st']
      by_cases hpost : ∃ y ∈ pqPost W st, normalizePath y.1 = q
      · obtain ⟨y, hy, rfl⟩ := hpost
        obtain ⟨_, d, hd, s, hyn⟩ := pqPost_props W st y hy
        have h_not_coins : ∀ z ∈ [(coinsFile, coins)], normalizePath z.1 ≠ normalizePath y.1 := by
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          subst hz; rw [norm_coinsFile, hyn]; simp
        have h_not_ws : ∀ z ∈ ws, normalizePath z.1 ≠ normalizePath y.1 := by
          intro z hz heq
          obtain ⟨_, dz, hdz, sz, hzn⟩ := hws_props z hz
          rw [hzn, hyn] at heq
          injection heq with hdeq _
          subst hdeq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hdz
          rcases hdz with rfl | rfl <;> revert hd <;> decide
        rw [hsplit_st]
        simp only [evalAt_append]
        rw [evalAt_idle h_not_ws, evalAt_idle h_not_coins]
        exact evalAt_const_of_exists ⟨y, hy, rfl⟩ _ _
      · have hpost_idle : ∀ z ∈ pqPost W st, normalizePath z.1 ≠ q :=
          fun z hz hzq => hpost ⟨z, hz, hzq⟩
        simp only [evalAt_append]
        rw [evalAt_idle hpost_idle]
        by_cases hws : ∃ y ∈ ws, normalizePath y.1 = q
        · exact evalAt_const_of_exists hws _ _
        · have hws_idle : ∀ z ∈ ws, normalizePath z.1 ≠ q :=
            fun z hz hzq => hws ⟨z, hz, hzq⟩
          rw [evalAt_idle hws_idle, evalAt_idle hws_idle]
          by_cases hroot : ∃ y ∈ pqRoot3 W st, normalizePath y.1 = q
          · obtain ⟨y, hy, rfl⟩ := hroot
            have hyn := (pqRoot3_props W st y hy).2
            have h_not_mid : ∀ z ∈ pqMid st, normalizePath z.1 ≠ normalizePath y.1 := by
              intro z hz heq
              obtain ⟨_, dz, _, sz, hzn⟩ := pqMid_props st z hz
              rw [hzn] at heq
              rw [← heq] at hyn
              simp at hyn
            have h_not_coins :
                ∀ z ∈ [(coinsFile, coins)], normalizePath z.1 ≠ normalizePath y.1 := by
              intro z hz heq
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              subst hz
              rw [norm_coinsFile] at heq
              rw [← heq] at hyn
              revert hyn; decide
            rw [hsplit_st]
            simp only [evalAt_append]
            rw [evalAt_idle h_not_coins, evalAt_idle hpost_idle, evalAt_idle h_not_mid]
            exact evalAt_const_of_exists ⟨y, hy, rfl⟩ _ _
          · have hroot_idle : ∀ z ∈ pqRoot3 W st, normalizePath z.1 ≠ q :=
              fun z hz hzq => hroot ⟨z, hz, hzq⟩
            rw [evalAt_idle hroot_idle]

end CryptoVerification.SignalSession.Cli.RunProofs.Agree
