/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge

/-!
# PQXDH Directory Provisioning and Clear-Session Bridges

Establishes `PqDirInv` for provisioned directories (`initPqParty`, `pqDirInv_init`) and proves its
preservation under session clearing (`pqPartyInv_clear_same`, `pqDirInv_clear`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli

open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

/-! ## Initial directory provisioning -/

/-- Initial `PqParty` state provisioned by `initDirs interp r p`. -/
def initPqParty (interp : ExternInterpretation) (r : ProtocolSetup) (p : Participant) : PqParty :=
  { party := partyOf r p
    me := ⟨bytesToVec 32 (idSecret r p), regIdOf r p⟩
    peerId := some ⟨⟨bytesToVec 32 (pubBytes interp (peerIdSecret r p))⟩⟩
    session := none
    signed := if p = r.alice then [] else
      [(r.spkId, ⟨bytesToVec 32 (secretBytes r 2), bytesToVec 64 (r.opaqueBytes (setupPublic r 5)), 0⟩)]
    oneTime := if p = r.alice then [] else
      if r.withOpk then [(r.opkId, some (bytesToVec 32 (secretBytes r 6)))] else []
    kyberOneTime := []
    kyberLastResort := if p = r.alice then [] else
      [(r.kpkId, ⟨bytesToVec 1568 (r.opaqueBytes (setupPublic r 6)),
        bytesToVec 3168 (r.kyberSecB.drop 1),
        bytesToVec 64 (r.opaqueBytes (setupPublic r 7)), 0⟩, [])] }

theorem pqDirInv_init {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hr : ProtocolSetupWF r) (hagree : ModelAgree interp P) :
    PqDirInv interp P r (CliTurn.init (initDirs interp r)) [] := by
  have hidA := bytesToVec_toList_of_len (idSecret_length hr r.alice)
  have hidB := bytesToVec_toList_of_len (idSecret_length hr r.bob)
  have hpidA := bytesToVec_toList_of_len (pubBytes_length_of_modelAgree hagree (peerIdSecret_length hr r.alice))
  have hpidB := bytesToVec_toList_of_len (pubBytes_length_of_modelAgree hagree (peerIdSecret_length hr r.bob))
  have hsec2 := bytesToVec_toList_of_len (secretBytes_2_length hr)
  have hop5 : (bytesToVec 64 (r.opaqueBytes (setupPublic r 5))).toList =
      r.opaqueBytes (setupPublic r 5) := bytesToVec_toList_of_len hr.2.2.2.1
  have hop6 : (bytesToVec 1568 (r.opaqueBytes (setupPublic r 6))).toList =
      r.opaqueBytes (setupPublic r 6) := bytesToVec_toList_of_len hr.2.2.2.2.1
  have hop7 : (bytesToVec 64 (r.opaqueBytes (setupPublic r 7))).toList =
      r.opaqueBytes (setupPublic r 7) := bytesToVec_toList_of_len hr.2.2.2.2.2.1
  have hksec_drop : (r.kyberSecB.drop 1).length = 3168 := by simp [hr.2.2.2.2.2.2.1]
  have hksec : 0x08#8 :: (bytesToVec 3168 (r.kyberSecB.drop 1)).toList =
      DY.Libsignal.Composed.Refinement.kyberKey (r.kyberSecB.drop 1) := by
    rw [bytesToVec_toList_of_len hksec_drop]; rfl
  refine ⟨⟨initPqParty interp r r.alice, ?_⟩, ⟨initPqParty interp r r.bob, ?_⟩,
    fun p ha hb => by simp [CliTurn.init, initDirs, ha, hb]⟩
  · refine ⟨rfl, rfl, rfl, fun _ => by simp [initPqParty], fun h => absurd rfl h,
      (fun _ _ hs => by cases hs), ?_⟩
    simp only [CliTurn.init, initDirs, ↓reduceIte]
    congr 1
    unfold commonFiles encodeDir initPqParty
    rw [ecKey_pubBytes_eq_djbKey_keyPairOf hagree (idSecret_length hr r.alice)]
    simp only [↓reduceIte, cliTextBytes_eq_signalTextBytes, addrOf_eq_addrE, peerNameOf_eq_nameE_other,
      hidA, IdentityKey.serialize, PublicKey.serialize, djbKey, ecKey, hpidA,
      List.map_nil, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append]; rfl
  · refine ⟨rfl, rfl, rfl, fun h => absurd h.symm hr.1, fun _ => ?_,
      (fun _ _ hs => by cases hs), ?_⟩
    · refine ⟨by simp [initPqParty, hr.1.symm], rfl, ?_, ⟨[], by simp [initPqParty, hr.1.symm],
        by simp, by simp⟩⟩
      cases hop : r.withOpk
      · exact Or.inl ⟨rfl, by simp [initPqParty, hr.1.symm, hop]⟩
      · exact Or.inr ⟨rfl, Or.inl (by simp [initPqParty, hr.1.symm, hop])⟩
    · simp only [CliTurn.init, initDirs, hr.1.symm, ↓reduceIte]
      have hc : commonFiles interp r r.bob =
          [(addressFile, CryptoVerification.SignalSession.textBytes (partyAddress (partyOf r r.bob)).text),
           (identityKeyPairFile, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
             ⟨djbKey (keyPairOf P.C (bytesToVec 32 (idSecret r r.bob))).publicKey.bytes,
              (bytesToVec 32 (idSecret r r.bob)).toList⟩),
           (registrationIdFile, CryptoVerification.SignalSession.le32 (regIdOf r r.bob)),
           (identityFile (partyAddressName (partyOf r r.bob).other),
            (IdentityKey.mk ⟨bytesToVec 32 (pubBytes interp (peerIdSecret r r.bob))⟩).serialize)] := by
        unfold commonFiles
        rw [ecKey_pubBytes_eq_djbKey_keyPairOf hagree (idSecret_length hr r.bob)]
        simp only [cliTextBytes_eq_signalTextBytes, addrOf_eq_addrE, peerNameOf_eq_nameE_other,
          hidB, IdentityKey.serialize, PublicKey.serialize, djbKey, ecKey, hpidB]; rfl
      have hspk_eq : CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
          ⟨r.spkId, ecKey (pubBytes interp (secretBytes r 2)), secretBytes r 2,
            r.opaqueBytes (setupPublic r 5), 0⟩ =
          signedRecordBytes P.C r.spkId
            ⟨bytesToVec 32 (secretBytes r 2), bytesToVec 64 (r.opaqueBytes (setupPublic r 5)), 0⟩ := by
        unfold signedRecordBytes
        rw [ecKey_pubBytes_eq_djbKey_keyPairOf hagree (secretBytes_2_length hr), hsec2, hop5]
      have hkyb_eq : CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
          ⟨r.kpkId, DY.Libsignal.Composed.Refinement.kyberKey (r.opaqueBytes (setupPublic r 6)),
            DY.Libsignal.Composed.Refinement.kyberKey (r.kyberSecB.drop 1),
            r.opaqueBytes (setupPublic r 7), 0⟩ =
          kyberRecordBytes r.kpkId
            ⟨bytesToVec 1568 (r.opaqueBytes (setupPublic r 6)),
             bytesToVec 3168 (r.kyberSecB.drop 1),
             bytesToVec 64 (r.opaqueBytes (setupPublic r 7)), 0⟩ := by
        unfold kyberRecordBytes CryptoVerification.E2E.kyberKey
        rw [hop6, hksec, hop7]; rfl
      cases hop : r.withOpk
      · congr 1
        unfold bobPreKeyFiles ProtocolSetup.spkSecBytes ProtocolSetup.spkSigTerm
          ProtocolSetup.pqpkPubTerm ProtocolSetup.pqpkSigTerm ProtocolSetup.opkSecBytes
          encodeDir initPqParty
        rw [hc]
        simp only [hr.1.symm, hop, Bool.false_eq_true, ↓reduceIte, hspk_eq, hkyb_eq, baseKeysBytes,
          List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.cons_append, List.nil_append]
      · have hopk_eq : CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode
            ⟨r.opkId, ecKey (pubBytes interp (secretBytes r 6)), secretBytes r 6⟩ =
            oneTimeRecordBytes P.C r.opkId (bytesToVec 32 (secretBytes r 6)) := by
          unfold oneTimeRecordBytes
          rw [ecKey_pubBytes_eq_djbKey_keyPairOf hagree (secretBytes_6_length hr hop),
              bytesToVec_toList_of_len (secretBytes_6_length hr hop)]
        funext path
        have hreg1 := regularFileList_encodeDir P (initPqParty interp r r.bob)
        have hreg2 : RegularFileList (commonFiles interp r r.bob ++ bobPreKeyFiles interp r) := by
          intro f hf
          have hmem : f ∈ encodeDir P (initPqParty interp r r.bob) := by
            unfold bobPreKeyFiles ProtocolSetup.spkSecBytes ProtocolSetup.spkSigTerm
              ProtocolSetup.pqpkPubTerm ProtocolSetup.pqpkSigTerm ProtocolSetup.opkSecBytes at hf
            rw [hc] at hf
            unfold encodeDir initPqParty
            simp only [hr.1.symm, hop, ↓reduceIte, hspk_eq, hkyb_eq, hopk_eq, baseKeysBytes,
              List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
              List.cons_append, List.nil_append, List.mem_cons,
              List.not_mem_nil, or_false] at hf ⊢
            tauto
          exact hreg1 f hmem
        rw [filesOf_eq_optFold hreg2, filesOf_eq_optFold hreg1, hc]
        unfold bobPreKeyFiles ProtocolSetup.spkSecBytes ProtocolSetup.spkSigTerm
          ProtocolSetup.pqpkPubTerm ProtocolSetup.pqpkSigTerm ProtocolSetup.opkSecBytes
          encodeDir initPqParty
        simp only [hr.1.symm, hop, ↓reduceIte, hspk_eq, hkyb_eq, hopk_eq, baseKeysBytes,
          List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
        by_cases hop_p : (Arm64.normalizePath path == Arm64.normalizePath (oneTimePreKeyFile r.opkId)) = true
        · have hp_eq := eq_of_beq hop_p
          have ha : Arm64.normalizePath (oneTimePreKeyFile r.opkId) =
              ["one-time-pre-keys", toString r.opkId.toNat ++ ""] := by
            simpa [oneTimePreKeyFile] using normalizePath_dir_nat_suf
              (d := "one-time-pre-keys") (suf := "") r.opkId.toNat
              (by decide) (by decide) (by decide) (by decide)
          have h1 : (Arm64.normalizePath path == Arm64.normalizePath (lastResortKyberPreKeyFile r.kpkId)) = false := by
            apply beq_false_of_ne; rw [hp_eq]; intro heq
            have hb : Arm64.normalizePath (lastResortKyberPreKeyFile r.kpkId) =
                ["last-resort-kyber-pre-keys", toString r.kpkId.toNat ++ ""] := by
              simpa [lastResortKyberPreKeyFile] using normalizePath_dir_nat_suf
                (d := "last-resort-kyber-pre-keys") (suf := "") r.kpkId.toNat
                (by decide) (by decide) (by decide) (by decide)
            rw [ha, hb] at heq
            exact absurd (List.cons.inj heq).1 (by decide)
          have h2 : (Arm64.normalizePath path == Arm64.normalizePath (baseKeysFile r.kpkId)) = false := by
            apply beq_false_of_ne; rw [hp_eq]; intro heq
            have hb : Arm64.normalizePath (baseKeysFile r.kpkId) =
                ["last-resort-kyber-pre-keys", toString r.kpkId.toNat ++ ".base-keys"] := by
              simpa [baseKeysFile] using normalizePath_dir_nat_suf
                (d := "last-resort-kyber-pre-keys") (suf := ".base-keys") r.kpkId.toNat
                (by decide) (by decide) (by decide) (by decide)
            rw [ha, hb] at heq
            exact absurd (List.cons.inj heq).1 (by decide)
          simp [hop_p, h1, h2]
        · simp [hop_p]

/-! ## Clear-session preservation -/

theorem filesOf_congr_samePath_of_regular {files : List (String × HwBytes)}
    (hreg : RegularFileList files) {p q : String} (hsp : SamePath p q = true) :
    filesOf files p = filesOf files q := by
  have hnorm : Arm64.normalizePath p = Arm64.normalizePath q := beq_iff_eq.mp hsp
  rw [filesOf_eq_optFold hreg, filesOf_eq_optFold hreg, hnorm]

private theorem encodeDir_clear_session_foldl (P : PEParams) (st : PqParty) (x : RecordExtras)
    (g : GhostState HwBytes) (hsess : st.session = some (x, g)) (path : String)
    (hne : (Arm64.normalizePath path ==
      Arm64.normalizePath (sessionFile (partyAddress st.party.other))) = false) :
    (encodeDir P st).foldl
      (fun acc f => if Arm64.normalizePath path == Arm64.normalizePath f.1 then some f.2 else acc)
      none =
    (encodeDir P { st with session := none }).foldl
      (fun acc f => if Arm64.normalizePath path == Arm64.normalizePath f.1 then some f.2 else acc)
      none := by
  unfold encodeDir
  simp only [hsess, List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil,
    hne, Bool.false_eq_true, ↓reduceIte]

theorem pqPartyInv_clear_same {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {p : Participant} {st : PqParty} {d : DirectorySnapshot}
    (h : PqPartyInv interp P r accepted p st d) :
    PqPartyInv interp P r accepted p { st with session := none }
      (fun path => if SamePath path (sessionPathOf r p) then none else d path) := by
  let st₀ : PqParty := { st with session := none }
  have hst₀ : PqPartyInv interp P r accepted p st₀ (filesOf (encodeDir P st₀)) :=
    ⟨h.party_eq, h.me_eq, h.peerId_eq, h.alice_stores, h.bob_stores,
      (fun _ _ hs => by cases hs), rfl⟩
  refine ⟨h.party_eq, h.me_eq, h.peerId_eq, h.alice_stores, h.bob_stores,
    (fun _ _ hs => by cases hs), ?_⟩
  funext path
  cases hsp : SamePath path (sessionPathOf r p) with
  | true =>
    simp only [↓reduceIte]
    change none = filesOf (encodeDir P st₀) path
    rw [filesOf_congr_samePath_of_regular (regularFileList_encodeDir P st₀) hsp,
        dir_sessionPathOf_of_pqPartyInv hst₀]
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, h.dir_eq]
    cases hsess : st.session with
    | none =>
      have heq : ({ st with session := none } : PqParty) = st := by cases st; cases hsess; rfl
      rw [heq]
    | some xg =>
      rcases xg with ⟨x, g⟩
      rw [filesOf_eq_optFold (regularFileList_encodeDir P st),
          filesOf_eq_optFold (regularFileList_encodeDir P { st with session := none })]
      have hne : (Arm64.normalizePath path ==
          Arm64.normalizePath (sessionFile (partyAddress st.party.other))) = false := by
        simpa [SamePath, sessionPathOf_eq_sessionFile, h.party_eq] using hsp
      exact encodeDir_clear_session_foldl P st x g hsess path hne

theorem pqDirInv_clear {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {t : CliTurn} (p : Participant)
    (hr : ProtocolSetupWF r) (hinv : PqDirInv interp P r t accepted) :
    PqDirInv interp P r (t.clearSession r p) accepted := by
  obtain ⟨⟨stA, hA⟩, ⟨stB, hB⟩, hother⟩ := hinv
  by_cases hpA : p = r.alice
  · subst hpA
    refine ⟨⟨{ stA with session := none }, ?_⟩, ⟨stB, ?_⟩, fun q hqa hqb => ?_⟩
    · simpa [CliTurn.clearSession] using pqPartyInv_clear_same hA
    · simpa [CliTurn.clearSession, hr.1, hr.1.symm] using hB
    · simp [CliTurn.clearSession, hqa, hother q hqa hqb]
  · by_cases hpB : p = r.bob
    · subst hpB
      refine ⟨⟨stA, ?_⟩, ⟨{ stB with session := none }, ?_⟩, fun q hqa hqb => ?_⟩
      · simpa [CliTurn.clearSession, hr.1] using hA
      · have hbo' : (t.clearSession r r.bob).bobOff = false := by simp [CliTurn.clearSession]
        rw [hbo']; unfold PqBobInv
        simp only [Bool.false_eq_true, ↓reduceIte, CliTurn.clearSession]
        unfold PqBobInv at hB
        cases hbo : t.bobOff
        · rw [hbo] at hB
          exact pqPartyInv_clear_same hB
        · rw [hbo] at hB
          rcases hB with ⟨d₀, hB₀, hag⟩
          have hd_eq :
              (fun path => if SamePath path (sessionPathOf r r.bob) then none else t.dirs r.bob path) =
              (fun path => if SamePath path (sessionPathOf r r.bob) then none else d₀ path) := by
            funext path
            cases hsp : SamePath path (sessionPathOf r r.bob)
            · simp [hag path hsp]
            · simp
          rw [hd_eq]
          exact pqPartyInv_clear_same hB₀
      · simp [CliTurn.clearSession, hqb, hother q hqa hqb]
    · refine ⟨⟨stA, ?_⟩, ⟨stB, ?_⟩, fun q hqa hqb => ?_⟩
      · simpa [CliTurn.clearSession, Ne.symm hpA] using hA
      · simpa [CliTurn.clearSession, hpB, Ne.symm hpB] using hB
      · by_cases hqp : q = p
        · subst hqp; funext path; simp [CliTurn.clearSession, hother q hqa hqb]
        · simp [CliTurn.clearSession, hqp, hother q hqa hqb]

end Symbolic.Swarm.CREF.Cli
