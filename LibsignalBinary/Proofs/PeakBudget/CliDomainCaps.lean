/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Semantics
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageLengthBound
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridge
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen

@[expose] public section

set_option autoImplicit false

/-!
# `AllocCostModel`-free CLI, store, and wire domain caps (`CliDomainCaps`)

Pure domain predicates and byte-length bounds derived from `CliPqxdhInputs`, `PqDir`,
`sessionCapBytes` (`2 MiB`), `StoresGhost.opened`, and the protobuf wire parsers:
- Query, session-record, `.base-keys`, and `FsState` regular-file caps (`R3QueryCap`,
  `SessionRecordCapInDomain`, `PqPartyBaseKeysCap`, `FilesBounded`);
- Process input bounds (`stdin ≤ 2 ^ 32`, `argv ≤ 3`, `coinsOf < 2 ^ 31`, bundle files `≤ 1637`);
- `DirDomainCaps`, store path and parsed address bounds (`≤ 40` bytes), `PeerSpqrValid`, and the
  bundled invocation cap `CliPqDomainCaps`.
-/

namespace LibsignalBinary.Proofs.PeakBudget.CliDomainCaps

open Arm64 (FsPath FsState normalizePath)
open Arm64.Process (ProcessInputs bytesOfString initFsState)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (GhostState IdentityKey PublicKey)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage Session SessionRecord)
open CryptoVerification.E2E
  (LocalIdentity PEParams PreKeyBundleFields PreKeyMessageFields ReachablePqxdhSession
   RecordExtras djbKey encodeRecordUnderExtras initiateTapeLen keyPairOf kyberKey partyAddressName
   wirePrekey wireWhisper)
open CryptoVerification.E2E.Record (encodeRecord toRecord)
open CryptoVerification.E2E.RecordX
  (DeserializeScopeBounded extrasOf sessionOfX sessionScopeBounded_of_sessionScopeP
   toRecord_extrasOf_eq)
open CryptoVerification.LibsignalProtoCodec
  (WireType encodeBytesField encodeKey encodeUint32Field protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet.Prost (encodeVarint_length_bounds)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost hyphenatedLength pniPrefix pniPrefix_word serviceIdParse tryParseHyphenated
   uuidTryParse)
open CryptoVerification.RecordCodecs
  (IdentityKeyPairStructure PreKeyRecordStructure SignedPreKeyRecordStructure
   encodeProto3BytesField encodeProto3Fixed64Field encodeProto3Uint32Field le64Bytes)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs PqKyberKey PqParty PqSignedKey PqxdhPartyInSpecDomain PublicBundle
   addressFile baseKeysBytes baseKeysFile bundleDir coinsFile encodeDir filesOf fsView identityFile
   identityKeyPairFile kyberRecordBytes lastResortKyberPreKeyFile le32 oneTimeKyberPreKeyFile
   oneTimePreKeyFile oneTimeRecordBytes partyAddress pqInitInputs pqInputs
   pqRecvInputs pqSendInputs publicBundleOf registrationIdFile
   sessionFile signedPreKeyFile signedRecordBytes textBytes)
open CryptoVerification.SignalSession.Cli
  (DirGhost SessFileWf StoresGhost addressText baseKeysName cliInputs decimalText keyName utf8)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV addrParse coinsOf encodeInjOn_scopeIn parseArgs parseUnsigned
   ratchetScopeCoversPq_scopeIn rsplitDot)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (loadRec_scopeKit_eq w1SessKit)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_init parseArgs_recv parseArgs_send)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (callPeer_of_cmd encodeInjOn_deserializeScopeP_Q filesOkPeer_pqSend loadRec loadRec_pqSend
   loadRec_unique partyAddr pqSessBytes_le_fileCapBytes scopeIn scopeKit)
open CryptoVerification.SignalSession.Cli.Slots.PqValid
  (PqOutV1 encodeRecord_length_lt_32_of_stripPq_bounded pqRatchetState_length_le_encodeRecordX
   stripPq)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
  (ValidEncoderPts sessionCapBytes validEncoderPts_of_reachPq)
export LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps
  (pksmParse_lengths_le signalMessage_tryFrom_lengths_le)

/-! ## Domain cap predicates -/

/-- Query-count cap `∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32`. -/
def R3QueryCap (qStart : Nat) (qs : Nat → Nat) : Prop :=
  ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32

/-- Session-record byte-length cap on `ReachablePqxdhSession W me x g`. -/
def SessionRecordCapInDomain (W : PEParams) (cap : Nat) : Prop :=
  ∀ (me : LocalIdentity) (x : RecordExtras) (g : GhostState (List (BitVec 8))),
    ReachablePqxdhSession W me x g →
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ cap

/-- Byte-length cap on every last-resort Kyber pre-key `.base-keys` file in `st`. -/
def PqPartyBaseKeysCap (bkCap : Nat) (st : PqParty) : Prop :=
  ∀ i k seen, (i, k, seen) ∈ st.kyberLastResort → (baseKeysBytes seen).length ≤ bkCap

/-- Every regular file in `fs` has byte length `≤ cap`. -/
def FilesBounded (cap : Nat) (fs : FsState) : Prop :=
  ∀ p bs, fs.files p = some (.file bs) → bs.length ≤ cap

theorem FilesBounded.mono {c₁ c₂ : Nat} {fs : FsState}
    (h : FilesBounded c₁ fs) (hle : c₁ ≤ c₂) : FilesBounded c₂ fs :=
  fun p bs hp => Nat.le_trans (h p bs hp) hle

/-! ## Provenance of regular files in `initFsState` and `filesOf` -/

private def EntriesFrom (files : List (String × List (BitVec 8))) (fs : FsState) : Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, (p, bs) ∈ files

private theorem entriesFrom_empty (files : List (String × List (BitVec 8))) :
    EntriesFrom files ({} : FsState) := by
  intro k bs hk
  dsimp only at hk
  split at hk <;> cases hk

private theorem entriesFrom_setEntry_dir {files : List (String × List (BitVec 8))} {fs : FsState}
    (h : EntriesFrom files fs) (pref : FsPath) :
    EntriesFrom files (fs.setEntry pref (some .dir)) := by
  intro k bs hk
  unfold FsState.setEntry at hk
  dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem entriesFrom_foldl_dirs {files : List (String × List (BitVec 8))}
    (prefs : List FsPath) {fs : FsState} (h : EntriesFrom files fs) :
    EntriesFrom files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFrom_setEntry_dir h hd)

private theorem entriesFrom_foldl_outer_dirs {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : FsState} (h : EntriesFrom files fs) :
    EntriesFrom files
      (dirs.foldl
        (fun acc d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFrom_foldl_dirs _ h)

private theorem entriesFrom_setFile {files : List (String × List (BitVec 8))} {fs : FsState}
    (h : EntriesFrom files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    EntriesFrom files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk
  unfold FsState.setFile FsState.setEntry at hk
  dsimp only at hk
  split at hk
  · injection hk with hfile
    injection hfile with hbs
    subst hbs
    exact ⟨p, hmem⟩
  · exact h k bs' hk

private theorem entriesFrom_foldl_files {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : FsState} (h : EntriesFrom allFiles fs) :
    EntriesFrom allFiles
      (rem.foldl
        (fun acc (p, bs) =>
          let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
            (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    have hanc := entriesFrom_foldl_dirs ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast) h
    have hset := entriesFrom_setFile hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem entriesFrom_initFsState (inputs : ProcessInputs) :
    EntriesFrom inputs.files (initFsState inputs) := by
  have hd := entriesFrom_foldl_outer_dirs inputs.dirs (entriesFrom_empty inputs.files)
  have hf := entriesFrom_foldl_files inputs.files (fun _ hx => hx) hd
  intro k bs hk
  exact hf k bs hk

/-- Every regular file in `(initFsState inputs).files` comes from an entry in `inputs.files`. -/
theorem initFsState_files_mem {inputs : ProcessInputs} {q : String} {bs : List (BitVec 8)}
    (h : (initFsState inputs).files q = some (.file bs)) :
    ∃ p, (p, bs) ∈ inputs.files := by
  unfold FsState.files FsState.getEntry at h
  split at h
  · cases h
  · exact entriesFrom_initFsState inputs (normalizePath q) bs h

/-- Every lookup hit in `filesOf files` comes from an entry in `files`. -/
theorem filesOf_mem {files : List (String × List (BitVec 8))} {q : String} {bs : List (BitVec 8)}
    (h : filesOf files q = some bs) :
    ∃ p, (p, bs) ∈ files := by
  unfold filesOf fsView at h
  split at h
  · cases h
  · split at h
    · rename_i bs' hfile
      injection h with hbs
      subst hbs
      exact initFsState_files_mem hfile
    · cases h

/-! ## Bundle, `encodeDir`, and `CliPqxdhInputs` bounds -/

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem repr_utf8_eq_kutf8 (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, kutf8, List.utf8Encode,
    byteArray_toList_eq_data]

/-- Every file in `(publicBundleOf b).files dir` is at most `1637` bytes (`kyber-pre-key`). -/
theorem publicBundleOf_files_le_1637 (b : PreKeyBundleFields) (dir : String) :
    ∀ f ∈ (publicBundleOf b).files dir, f.2.length ≤ 1637 := by
  intro f hf
  unfold PublicBundle.files publicBundleOf at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl) | hopk
  · simp [djbKey]
  · simp [le32]
  · simp [le32, djbKey]
  · simp [le32, kyberKey]
  · cases hb : b.opk with
    | none => simp [hb] at hopk
    | some p =>
      rcases p with ⟨id, k⟩
      simp only [hb, Option.map_some, List.mem_singleton] at hopk
      subst hopk
      simp [le32, djbKey]

/-- Every file in `(publicBundleOf b).files dir` is strictly under `2 ^ 31` bytes. -/
theorem publicBundleOf_files_lt (b : PreKeyBundleFields) (dir : String) :
    ∀ f ∈ (publicBundleOf b).files dir, f.2.length < 2 ^ 31 :=
  fun f hf => Nat.lt_of_le_of_lt (publicBundleOf_files_le_1637 b dir f hf) (by omega)

/-- Exact byte length of `.base-keys` (`37` bytes per `(signedPreKeyId, baseKey)` entry). -/
theorem baseKeysBytes_length (seen : List (BitVec 32 × List.Vector (BitVec 8) 32)) :
    (baseKeysBytes seen).length = 37 * seen.length := by
  unfold baseKeysBytes
  induction seen with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨s, b⟩
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons]
    have h1 : (le32 s).length = 4 := rfl
    have h2 : (djbKey b).length = 33 := by simp [djbKey]
    omega

private theorem encodeKey_length_le_10 (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 := by
  unfold encodeKey
  exact (encodeVarint_length_bounds _).2

private theorem encodeProto3Uint32Field_length_le_20 (tag : Nat) (v : BitVec 32) :
    (encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold encodeProto3Uint32Field encodeUint32Field
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := encodeKey_length_le_10 tag .varint
    have hv := (encodeVarint_length_bounds (BitVec.zeroExtend 64 v)).2
    omega

private theorem encodeProto3Fixed64Field_length_le_18 (tag : Nat) (v : BitVec 64) :
    (encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold encodeProto3Fixed64Field le64Bytes
  split_ifs
  · simp
  · simp only [List.length_append, List.length_cons, List.length_nil]
    have hk := encodeKey_length_le_10 tag .sixtyFourBit
    omega

private theorem encodeProto3BytesField_length_le (tag : Nat) (v : List (BitVec 8)) :
    (encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold encodeProto3BytesField encodeBytesField
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := encodeKey_length_le_10 tag .lengthDelimited
    have hv := (encodeVarint_length_bounds (BitVec.ofNat 64 v.length)).2
    omega

private theorem partyAddress_textBytes_length_le_40 (p : Party) :
    (textBytes (partyAddress p).text).length ≤ 40 := by
  unfold textBytes partyAddress CryptoVerification.SignalSession.Address.text
  dsimp only
  rw [repr_utf8_eq_kutf8]
  have hk_app (a b : String) : kutf8 (a ++ b) = kutf8 a ++ kutf8 b := by
    simp [kutf8, String.toList_append, List.flatMap_append]
  rw [hk_app, hk_app, List.length_append, List.length_append]
  have hd : (kutf8 (toString (1 : Nat))).length ≤ 1 := by
    rw [← utf8_eq_kutf8]
    exact decimalText_length_le 1 1 (by omega) (by omega)
  have hdot : (kutf8 ".").length = 1 := rfl
  have hp : (kutf8 (partyAddressName p)).length = 36 := by cases p <;> rfl
  omega

private theorem identityKeyPair_encode_length_le_105 (W : PEParams) (me : LocalIdentity) :
    (IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C me.idPriv).publicKey.bytes, me.idPriv.toList⟩).length ≤ 105 := by
  unfold IdentityKeyPairStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3BytesField_length_le 1 (djbKey (keyPairOf W.C me.idPriv).publicKey.bytes)
  have h2 := encodeProto3BytesField_length_le 2 me.idPriv.toList
  have hdjb : (djbKey (keyPairOf W.C me.idPriv).publicKey.bytes).length = 33 := by simp [djbKey]
  have hpriv : me.idPriv.toList.length = 32 := me.idPriv.toList_length
  omega

private theorem signedRecordBytes_length_le_230 (W : PEParams) (id : BitVec 32) (k : PqSignedKey) :
    (signedRecordBytes W.C id k).length ≤ 230 := by
  unfold signedRecordBytes SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3Uint32Field_length_le_20 1 id
  have h2 := encodeProto3BytesField_length_le 2 (djbKey (keyPairOf W.C k.priv).publicKey.bytes)
  have h3 := encodeProto3BytesField_length_le 3 k.priv.toList
  have h4 := encodeProto3BytesField_length_le 4 k.sig.toList
  have h5 := encodeProto3Fixed64Field_length_le_18 5 k.timestamp
  have hdjb : (djbKey (keyPairOf W.C k.priv).publicKey.bytes).length = 33 := by simp [djbKey]
  have hpriv : k.priv.toList.length = 32 := k.priv.toList_length
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

private theorem oneTimeRecordBytes_length_le_125 (W : PEParams) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    (oneTimeRecordBytes W.C id sk).length ≤ 125 := by
  unfold oneTimeRecordBytes PreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3Uint32Field_length_le_20 1 id
  have h2 := encodeProto3BytesField_length_le 2 (djbKey (keyPairOf W.C sk).publicKey.bytes)
  have h3 := encodeProto3BytesField_length_le 3 sk.toList
  have hdjb : (djbKey (keyPairOf W.C sk).publicKey.bytes).length = 33 := by simp [djbKey]
  have hpriv : sk.toList.length = 32 := sk.toList_length
  omega

private theorem kyberRecordBytes_length_le_4900 (id : BitVec 32) (k : PqKyberKey) :
    (kyberRecordBytes id k).length ≤ 4900 := by
  unfold kyberRecordBytes SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3Uint32Field_length_le_20 1 id
  have h2 := encodeProto3BytesField_length_le 2 (kyberKey k.pub)
  have h3 := encodeProto3BytesField_length_le 3 (0x08#8 :: k.sec.toList)
  have h4 := encodeProto3BytesField_length_le 4 k.sig.toList
  have h5 := encodeProto3Fixed64Field_length_le_18 5 k.timestamp
  have hpub : (kyberKey k.pub).length = 1569 := by simp [kyberKey]
  have hsec : (0x08#8 :: k.sec.toList).length = 3169 := by simp [k.sec.toList_length]
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

theorem encodeRecordUnderExtras_congr {E : Party → RecordExtras}
    {g₁ g₂ : GhostState (List (BitVec 8))}
    (hp : g₁.party = g₂.party) (hs : g₁.session = g₂.session) :
    encodeRecordUnderExtras E g₁ = encodeRecordUnderExtras E g₂ := by
  unfold encodeRecordUnderExtras
  rw [hp, hs]

/-- Tight file-size bound on `encodeDir W st` from `SessionRecordCapInDomain W sessCap` and
`PqPartyBaseKeysCap bkCap st`: every file in `encodeDir W st` is at most
`max (max sessCap bkCap) 4900` bytes (so `≤ sessionCapBytes` (`2 MiB`) whenever
`sessCap ≤ sessionCapBytes` and `bkCap ≤ sessionCapBytes`). -/
theorem encodeDir_files_le_of_caps {W : PEParams} {st : PqParty} {sessCap bkCap : Nat}
    (hwf : PqxdhPartyInSpecDomain W st)
    (hSess : SessionRecordCapInDomain W sessCap)
    (hBk : PqPartyBaseKeysCap bkCap st) :
    ∀ f ∈ encodeDir W st, f.2.length ≤ max (max sessCap bkCap) 4900 := by
  intro f hf
  unfold encodeDir at hf
  simp only [List.mem_append] at hf
  rcases hf with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with rfl | rfl | rfl
    · dsimp only; have h := partyAddress_textBytes_length_le_40 st.party; omega
    · dsimp only; have h := identityKeyPair_encode_length_le_105 W st.me; omega
    · dsimp only; have h : (le32 st.me.regId).length = 4 := rfl; omega
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      subst hf_peer
      dsimp only
      have hk : k.serialize.length = 33 := by simp [IdentityKey.serialize, PublicKey.serialize]
      omega
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨x, g⟩
      simp only [hs, List.mem_singleton] at hf_sess
      subst hf_sess
      dsimp only
      obtain ⟨⟨g₀, hr₀, hp₀, hs₀⟩, -⟩ := hwf.1 x g hs
      have heq := encodeRecordUnderExtras_congr (E := fun _ => x) hp₀ hs₀
      have hcap := hSess st.me x g₀ hr₀
      rw [← heq]
      omega
  · rw [List.mem_map] at hf_sig
    rcases hf_sig with ⟨⟨id, k⟩, _, rfl⟩
    dsimp only; have h := signedRecordBytes_length_le_230 W id k; omega
  · rw [List.mem_map] at hf_ot
    rcases hf_ot with ⟨⟨id, opt⟩, _, rfl⟩
    cases opt with
    | none => simp
    | some sk => dsimp only; have h := oneTimeRecordBytes_length_le_125 W id sk; omega
  · rw [List.mem_map] at hf_kot
    rcases hf_kot with ⟨⟨id, opt⟩, _, rfl⟩
    cases opt with
    | none => simp
    | some k => dsimp only; have h := kyberRecordBytes_length_le_4900 id k; omega
  · rw [List.mem_flatten] at hf_klr
    rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub
    rcases hsub with ⟨⟨id, k, seen⟩, hm, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with rfl | rfl
    · dsimp only; have h := kyberRecordBytes_length_le_4900 id k; omega
    · dsimp only; have h := hBk id k seen hm; omega

private theorem hmac_keyToBytes32_length_eq (rc : BitVec 256) :
    (keyToBytes32 rc).length = 32 := by
  simp [keyToBytes32]

private theorem pqParty_files_mem_le {W : PEParams} {st : PqParty} {bkCap : Nat} {i : Inputs}
    (hwf : PqxdhPartyInSpecDomain W st)
    (hSess : SessionRecordCapInDomain W sessionCapBytes)
    (hBk : PqPartyBaseKeysCap bkCap st)
    (hcase :
      (st.session = none ∧ ∃ b t, i = pqInitInputs W st b t) ∨
      (∃ m r, m.length < 2 ^ 32 ∧ i = pqSendInputs W st m r) ∨
      (∃ c rc, c.length < 2 ^ 32 ∧ i = pqRecvInputs W st (wireWhisper :: c) rc) ∨
      (∃ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 ∧ i = pqRecvInputs W st (wirePrekey :: m.bytes) rc) ∨
      (∃ c rc, c.length < 2 ^ 32 ∧ c.head? ≠ some wireWhisper ∧ c.head? ≠ some wirePrekey ∧
        i = pqRecvInputs W st c rc)) :
    ∀ p bs, (p, bs) ∈ i.files → bs.length ≤ max sessionCapBytes bkCap := by
  have h4900 : max (max sessionCapBytes bkCap) 4900 = max sessionCapBytes bkCap := by
    unfold sessionCapBytes; omega
  have hdir : ∀ f ∈ encodeDir W st, f.2.length ≤ max sessionCapBytes bkCap := by
    intro f hf
    rw [← h4900]
    exact encodeDir_files_le_of_caps hwf hSess hBk f hf
  intro p bs hp'
  have hsc : 2097152 ≤ max sessionCapBytes bkCap := by unfold sessionCapBytes; omega
  rcases hcase with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ |
      ⟨m, rc, _, rfl⟩ | ⟨c, rc, _, _, _, rfl⟩
  · simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_singleton] at hp'
    rcases hp' with (hed | hbun) | hcoins
    · exact hdir (p, bs) hed
    · have hb := publicBundleOf_files_le_1637 b bundleDir (p, bs) hbun; dsimp only at hb; omega
    · injection hcoins with _ hbs; subst hbs
      have ht : t.toList.length = initiateTapeLen := t.toList_length
      unfold initiateTapeLen at ht; omega
  · simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hp'
    rcases hp' with hed | hcoins
    · exact hdir (p, bs) hed
    · injection hcoins with _ hbs; subst hbs
      have hr : r.toList.length = 64 := r.toList_length; omega
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hp'
    rcases hp' with hed | hcoins
    · exact hdir (p, bs) hed
    · injection hcoins with _ hbs; subst hbs
      have hrc := hmac_keyToBytes32_length_eq rc; omega
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hp'
    rcases hp' with hed | hcoins
    · exact hdir (p, bs) hed
    · injection hcoins with _ hbs; subst hbs
      have hrc := hmac_keyToBytes32_length_eq rc; omega
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hp'
    rcases hp' with hed | hcoins
    · exact hdir (p, bs) hed
    · injection hcoins with _ hbs; subst hbs
      have hrc := hmac_keyToBytes32_length_eq rc; omega

/-- Tight regular-file bound (`≤ max sessionCapBytes bkCap`) on `initFsState (cliInputs i)` for any
call `i` of a `PqParty` `st` in `PqxdhPartyInSpecDomain W st` under `SessionRecordCapInDomain W sessionCapBytes`
and `PqPartyBaseKeysCap bkCap st`. -/
theorem filesBounded_of_pqParty_caps {W : PEParams} {st : PqParty} {bkCap : Nat} {i : Inputs}
    (hwf : PqxdhPartyInSpecDomain W st)
    (hSess : SessionRecordCapInDomain W sessionCapBytes)
    (hBk : PqPartyBaseKeysCap bkCap st)
    (hcase :
      (st.session = none ∧ ∃ b t, i = pqInitInputs W st b t) ∨
      (∃ m r, m.length < 2 ^ 32 ∧ i = pqSendInputs W st m r) ∨
      (∃ c rc, c.length < 2 ^ 32 ∧ i = pqRecvInputs W st (wireWhisper :: c) rc) ∨
      (∃ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 ∧ i = pqRecvInputs W st (wirePrekey :: m.bytes) rc) ∨
      (∃ c rc, c.length < 2 ^ 32 ∧ c.head? ≠ some wireWhisper ∧ c.head? ≠ some wirePrekey ∧
        i = pqRecvInputs W st c rc)) :
    FilesBounded (max sessionCapBytes bkCap) (initFsState (cliInputs i)) := by
  intro q bs hfile
  obtain ⟨p, hp⟩ := initFsState_files_mem hfile
  exact pqParty_files_mem_le hwf hSess hBk hcase p bs hp

/-- Every file in `i.files` for `CliPqxdhInputs P i` has byte length `< 2 ^ 31`. -/
theorem files_length_lt_of_cliPqInputs {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ f ∈ i.files, f.2.length < 2 ^ 31 := by
  obtain ⟨st, hwf, hcase⟩ := hi
  have hdir : ∀ f ∈ encodeDir P st, f.2.length < 2 ^ 31 := fun f hf => (hwf.2.1 f hf).1
  intro f hf
  rcases hcase with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ |
      ⟨m, rc, _, rfl⟩ | ⟨c, rc, _, _, _, rfl⟩
  · simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_singleton] at hf
    rcases hf with (hed | hbun) | rfl
    · exact hdir f hed
    · exact publicBundleOf_files_lt b bundleDir f hbun
    · simp [initiateTapeLen]
  · simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hf
    rcases hf with hed | rfl
    · exact hdir f hed
    · simp
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hf
    rcases hf with hed | rfl
    · exact hdir f hed
    · have hrc := hmac_keyToBytes32_length_eq rc; dsimp only; omega
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hf
    rcases hf with hed | rfl
    · exact hdir f hed
    · have hrc := hmac_keyToBytes32_length_eq rc; dsimp only; omega
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hf
    rcases hf with hed | rfl
    · exact hdir f hed
    · have hrc := hmac_keyToBytes32_length_eq rc; dsimp only; omega

/-- On any `CliPqxdhInputs P i`, every regular file in `initFsState (cliInputs i)` has byte length
`≤ 2 ^ 31` (in fact `< 2 ^ 31`). -/
theorem filesBounded_initFsState_of_cliPqInputs {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    FilesBounded (2 ^ 31) (initFsState (cliInputs i)) := by
  intro q bs hfile
  obtain ⟨p, hp⟩ := initFsState_files_mem hfile
  have hp' : (p, bs) ∈ i.files := hp
  exact Nat.le_of_lt (files_length_lt_of_cliPqInputs hi (p, bs) hp')

private theorem varint_length_le_5 {n : Nat} (hn : n < 2 ^ 32) :
    (CryptoGames.LibsignalSessionApi.Prost.varint n).length ≤ 5 := by
  unfold CryptoGames.LibsignalSessionApi.Prost.varint; split
  · simp
  · dsimp only [List.length_cons]; unfold CryptoGames.LibsignalSessionApi.Prost.varint; split
    · simp
    · dsimp only [List.length_cons]; unfold CryptoGames.LibsignalSessionApi.Prost.varint; split
      · simp
      · dsimp only [List.length_cons]; unfold CryptoGames.LibsignalSessionApi.Prost.varint; split
        · simp
        · dsimp only [List.length_cons]; unfold CryptoGames.LibsignalSessionApi.Prost.varint
          have h5 : n / 128 / 128 / 128 / 128 < 128 := by omega
          simp [h5]

private theorem uint32Field_length_le_10 {tag : Nat} (ht : 8 * tag < 2 ^ 32)
    (ov : Option (BitVec 32)) :
    (CryptoGames.LibsignalSessionApi.Prost.uint32Field tag ov).length ≤ 10 := by
  cases ov with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.uint32Field]
  | some v =>
    simp only [CryptoGames.LibsignalSessionApi.Prost.uint32Field, List.length_append]
    have h1 : (CryptoGames.LibsignalSessionApi.Prost.key tag 0).length ≤ 5 :=
      varint_length_le_5 (by omega)
    have h2 := varint_length_le_5 v.isLt
    omega

private theorem bytesField_some_length_le {tag : Nat} {bs : List (BitVec 8)}
    (ht : 8 * tag + 2 < 2 ^ 32) (hbs : bs.length < 2 ^ 32) :
    (CryptoGames.LibsignalSessionApi.Prost.bytesField tag (some bs)).length ≤ bs.length + 10 := by
  simp only [CryptoGames.LibsignalSessionApi.Prost.bytesField, List.length_append]
  have h1 : (CryptoGames.LibsignalSessionApi.Prost.key tag 2).length ≤ 5 := varint_length_le_5 ht
  have h2 := varint_length_le_5 hbs
  omega

private theorem preKeyMsgE_bytes_lt_2_32 {m : PreKeyMessageFields}
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    m.bytes.length < 2 ^ 32 := by
  simp only [PreKeyMessageFields.bytes, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  have h1 := uint32Field_length_le_10 (tag := 1) (by decide) m.opkId
  have h2 := bytesField_some_length_le (tag := 2) (bs := djbKey m.baseKey) (by decide)
    (by simp [djbKey])
  have h3 := bytesField_some_length_le (tag := 3) (bs := djbKey m.idPub) (by decide)
    (by simp [djbKey])
  have h4 := bytesField_some_length_le (tag := 4) (bs := m.inner) (by decide) (by omega)
  have h5 := uint32Field_length_le_10 (tag := 5) (by decide) (some m.regId)
  have h6 := uint32Field_length_le_10 (tag := 6) (by decide) (some m.spkId)
  have h7 := uint32Field_length_le_10 (tag := 7) (by decide) (some m.kpkId)
  have h8 := bytesField_some_length_le (tag := 8) (bs := kyberKey m.kyberCt) (by decide)
    (by simp [kyberKey])
  have hdjb1 : (djbKey m.baseKey).length = 33 := by simp [djbKey]
  have hdjb2 : (djbKey m.idPub).length = 33 := by simp [djbKey]
  have hkyb : (kyberKey m.kyberCt).length = 1569 := by simp [kyberKey]
  omega

/-- On any `CliPqxdhInputs P i`, `i.stdin.length ≤ 2 ^ 32`. -/
theorem stdin_length_le_of_cliPqInputs {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    i.stdin.length ≤ 2 ^ 32 := by
  obtain ⟨_, _, hcase⟩ := hi
  rcases hcase with ⟨_, b, t, rfl⟩ | ⟨m, r, hm, rfl⟩ | ⟨c, rc, hc, rfl⟩ |
      ⟨m, rc, hm, rfl⟩ | ⟨c, rc, hc, _, _, rfl⟩
  · simp [pqInitInputs, pqInputs]
  · simp only [pqSendInputs, pqInputs]; omega
  · simp only [pqRecvInputs, pqInputs, List.length_cons]; omega
  · simp only [pqRecvInputs, pqInputs, List.length_cons]
    have hmb := preKeyMsgE_bytes_lt_2_32 hm
    omega
  · simp only [pqRecvInputs, pqInputs]; omega

/-- On any `CliPqxdhInputs P i`, `i.argv.length ≤ 3`. -/
theorem argv_length_le_of_cliPqInputs {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    i.argv.length ≤ 3 := by
  obtain ⟨_, _, hcase⟩ := hi
  rcases hcase with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ |
      ⟨m, rc, _, rfl⟩ | ⟨c, rc, _, _, _, rfl⟩
  · simp [pqInitInputs, pqInputs, Cmd.argv]
  · simp [pqSendInputs, pqInputs, Cmd.argv]
  · simp [pqRecvInputs, pqInputs, Cmd.argv]
  · simp [pqRecvInputs, pqInputs, Cmd.argv]
  · simp [pqRecvInputs, pqInputs, Cmd.argv]

/-- On any `CliPqxdhInputs P i`, `(coinsOf i).length < 2 ^ 31`. -/
theorem coinsOf_length_lt_of_cliPqInputs {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    (coinsOf i).length < 2 ^ 31 := by
  unfold coinsOf
  cases hc : filesOf i.files "coins" with
  | none => simp
  | some bs =>
    obtain ⟨p, hp⟩ := filesOf_mem hc
    simpa using files_length_lt_of_cliPqInputs hi (p, bs) hp

/-- Any per-entry file cap `∀ p bs, (p, bs) ∈ i.files → bs.length ≤ cap` bounds `(coinsOf i).length ≤ cap`. -/
theorem coinsOf_length_le_of_files_le {cap : Nat} {i : Inputs}
    (hf : ∀ p bs, (p, bs) ∈ i.files → bs.length ≤ cap) :
    (coinsOf i).length ≤ cap := by
  unfold coinsOf
  cases hc : filesOf i.files "coins" with
  | none => simp
  | some bs =>
    obtain ⟨p, hp⟩ := filesOf_mem hc
    exact hf p bs hp

/-! ## `Dir`, store path, and record length bounds -/

theorem keyName_length_le (id : BitVec 32) : (keyName id).length ≤ 10 :=
  decimalText_length_le 10 id.toNat (by omega) (Nat.lt_trans id.isLt (by omega))

theorem baseKeysName_length_le (id : BitVec 32) : (baseKeysName id).length ≤ 20 := by
  have hk := keyName_length_le id
  have h10 : (utf8 ".base-keys").length = 10 := by rw [utf8_eq_kutf8]; rfl
  rw [baseKeysName, List.length_append, h10]
  omega

theorem addressText_length_le (a : AddrVal) : (addressText a).length ≤ a.name.length + 4 := by
  have hd : (decimalText a.device.toNat).length ≤ 3 :=
    decimalText_length_le 3 a.device.toNat (by omega) (Nat.lt_trans a.device.isLt (by omega))
  have h1 : (utf8 ".").length = 1 := by rw [utf8_eq_kutf8]; rfl
  rw [addressText, List.length_append, List.length_append, h1]
  omega

theorem encodeRecord_length_lt_32_of_scopeIn {r : SessionRecord (List (BitVec 8))}
    (h : scopeIn r) : (encodeRecord r).length < 2 ^ 32 := by
  obtain ⟨⟨hIn, hPq, hRepr⟩, s, hs, hSessP⟩ := h
  cases r with
  | mk cur =>
    dsimp only at hs
    subst hs
    have hInS := hIn s rfl
    have hPqS := hPq s rfl
    have hReprS := hRepr s rfl
    have hSessB := sessionScopeBounded_of_sessionScopeP hSessP
    have hBdd : DeserializeScopeBounded ⟨some (stripPq s)⟩ := by
      refine ⟨⟨?_, ?_, ?_⟩, _, rfl, ⟨hSessB.1, hSessB.2.1, hSessB.2.2.1, hSessB.2.2.2⟩⟩
      · intro s' hs'; cases hs'; exact ⟨hInS.1, hInS.2.1, hInS.2.2⟩
      · intro s' hs'; cases hs'; rfl
      · intro s' hs'; cases hs'
        exact ⟨hReprS.1, hReprS.2.1, hReprS.2.2.1, hReprS.2.2.2⟩
    have hOut : PqOutV1 s.state.pqRatchetState := by
      have h31 := hPqS.2
      unfold PqOutV1
      omega
    exact encodeRecord_length_lt_32_of_stripPq_bounded hBdd hOut

theorem sessFileWf_scopeIn_length_lt_32 {bs : List (BitVec 8)}
    (h : SessFileWf scopeIn bs) : bs.length < 2 ^ 32 := by
  rcases h with rfl | ⟨r, rfl, hr⟩
  · decide
  · exact encodeRecord_length_lt_32_of_scopeIn hr

/-- `AllocCostModel`-free domain invariant on a `DirGhost` directory handle:
`path` byte length `≤ maxPath`, `changed` entry count `≤ maxChanged` (bounding the `Vec<24>` buffer
to `≤ 64` entries throughout CLI execution), and every buffered value byte slice `≤ maxVal`. -/
structure DirDomainCaps (maxPath maxChanged maxVal : Nat) (d : DirGhost) : Prop where
  path_len_le : d.path.length ≤ maxPath
  changed_len_le : d.changed.length ≤ maxChanged
  changed_val_le : ∀ k v, (k, v) ∈ d.changed → v.length ≤ maxVal

theorem DirDomainCaps.mono {p₁ p₂ c₁ c₂ v₁ v₂ : Nat} {d : DirGhost}
    (h : DirDomainCaps p₁ c₁ v₁ d) (hp : p₁ ≤ p₂) (hc : c₁ ≤ c₂) (hv : v₁ ≤ v₂) :
    DirDomainCaps p₂ c₂ v₂ d :=
  ⟨Nat.le_trans h.path_len_le hp,
   Nat.le_trans h.changed_len_le hc,
   fun k v hm => Nat.le_trans (h.changed_val_le k v hm) hv⟩

theorem opened_own_path_len : StoresGhost.opened.identity.own.path.length = 0 := rfl

theorem opened_peers_path_len : StoresGhost.opened.identity.peers.path.length = 10 := by
  show (utf8 "identities").length = 10
  rw [utf8_eq_kutf8]; rfl

theorem opened_signed_path_len : StoresGhost.opened.signed.path.length = 15 := by
  show (utf8 "signed-pre-keys").length = 15
  rw [utf8_eq_kutf8]; rfl

theorem opened_kpkOt_path_len : StoresGhost.opened.kyber.oneTime.path.length = 23 := by
  show (utf8 "one-time-kyber-pre-keys").length = 23
  rw [utf8_eq_kutf8]; rfl

theorem opened_kpkLr_path_len : StoresGhost.opened.kyber.lastResort.path.length = 26 := by
  show (utf8 "last-resort-kyber-pre-keys").length = 26
  rw [utf8_eq_kutf8]; rfl

theorem opened_opk_path_len : StoresGhost.opened.oneTime.path.length = 17 := by
  show (utf8 "one-time-pre-keys").length = 17
  rw [utf8_eq_kutf8]; rfl

theorem opened_sess_path_len : StoresGhost.opened.sessions.path.length = 8 := by
  show (utf8 "sessions").length = 8
  rw [utf8_eq_kutf8]; rfl

theorem dirDomainCaps_opened_own : DirDomainCaps 26 0 0 StoresGhost.opened.identity.own :=
  ⟨by rw [opened_own_path_len]; omega, Nat.le_refl 0, fun _ _ h => nomatch h⟩

theorem dirDomainCaps_opened_peers : DirDomainCaps 26 0 0 StoresGhost.opened.identity.peers :=
  ⟨by rw [opened_peers_path_len]; omega, Nat.le_refl 0, fun _ _ h => nomatch h⟩

theorem dirDomainCaps_opened_signed : DirDomainCaps 26 0 0 StoresGhost.opened.signed :=
  ⟨by rw [opened_signed_path_len]; omega, Nat.le_refl 0, fun _ _ h => nomatch h⟩

theorem dirDomainCaps_opened_kpkOt : DirDomainCaps 26 0 0 StoresGhost.opened.kyber.oneTime :=
  ⟨by rw [opened_kpkOt_path_len]; omega, Nat.le_refl 0, fun _ _ h => nomatch h⟩

theorem dirDomainCaps_opened_kpkLr : DirDomainCaps 26 0 0 StoresGhost.opened.kyber.lastResort :=
  ⟨by rw [opened_kpkLr_path_len], Nat.le_refl 0, fun _ _ h => nomatch h⟩

theorem dirDomainCaps_opened_opk : DirDomainCaps 26 0 0 StoresGhost.opened.oneTime :=
  ⟨by rw [opened_opk_path_len]; omega, Nat.le_refl 0, fun _ _ h => nomatch h⟩

theorem dirDomainCaps_opened_sess : DirDomainCaps 26 0 0 StoresGhost.opened.sessions :=
  ⟨by rw [opened_sess_path_len]; omega, Nat.le_refl 0, fun _ _ h => nomatch h⟩

/-! ## Parsed address name length bound (`≤ 40`) -/

theorem tryParseHyphenated_length_eq {u} {bs : List (BitVec 8)}
    (h : tryParseHyphenated uuidTryParse bs = some u) :
    bs.length = 36 := by
  unfold tryParseHyphenated hyphenatedLength at h
  split_ifs at h with hlen
  exact hlen

theorem serviceIdParse_length_le {sid} {bs : List (BitVec 8)}
    (h : serviceIdParse uuidTryParse bs = some sid) :
    bs.length ≤ 40 := by
  unfold serviceIdParse at h
  have hpni : pniPrefix.length = 4 := by
    rw [pniPrefix_word]
    rfl
  split_ifs at h with hp
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨u, hu, _⟩ := h
    have hdrop := tryParseHyphenated_length_eq hu
    have hpre := (List.isPrefixOf_iff_prefix.mp hp).length_le
    rw [List.length_drop, hpni] at hdrop
    rw [hpni] at hpre
    omega
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨u, hu, _⟩ := h
    have h36 := tryParseHyphenated_length_eq hu
    omega

theorem addrParse_name_length_le {bs : List (BitVec 8)} {v : AddrV}
    (h : addrParse uuidTryParse bs = some v) :
    v.name.length ≤ 40 := by
  unfold addrParse at h
  rcases hr : rsplitDot bs with _ | ⟨nm, dev⟩ <;> rw [hr] at h
  · cases h
  · dsimp only at h
    rcases hs : serviceIdParse uuidTryParse nm with _ | sid <;> rw [hs] at h
    · cases h
    · rcases hp : parseUnsigned 255 dev with _ | d <;> rw [hp] at h
      · cases h
      · dsimp only at h
        split_ifs at h
        injection h with hv
        rw [← hv]
        exact serviceIdParse_length_le hs

def callAddrNameLen : CallV → Nat
  | .keygen me _ => me.name.length
  | .init peer _ => peer.name.length
  | .send peer => peer.name.length
  | .recv peer => peer.name.length

theorem parseArgs_peer_name_length_le {args : List (List (BitVec 8))} {c : CallV}
    (h : parseArgs uuidTryParse args = some c) :
    callAddrNameLen c ≤ 40 := by
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩⟩
  · cases h
  · cases h
  · unfold parseArgs at h
    dsimp only at h
    split_ifs at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      exact addrParse_name_length_le hp
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      exact addrParse_name_length_le hp
  · unfold parseArgs at h
    dsimp only at h
    by_cases hkg : a0 = utf8 "keygen"
    · simp only [hkg, ↓reduceIte] at h
      rcases ha : addrParse uuidTryParse a1 with _ | me <;> rw [ha] at h
      · cases h
      · rcases hn : parseUnsigned (2 ^ 32 - 1) a2 with _ | n <;> rw [hn] at h
        · cases h
        · dsimp only at h
          split_ifs at h
          injection h with hc
          rw [← hc]
          exact addrParse_name_length_le ha
    · simp only [hkg, ↓reduceIte] at h
      split_ifs at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      exact addrParse_name_length_le hp
  · cases h

/-! ## Send-slot SPQR `ValidEncoderPts` bridge and `CliPqDomainCaps` -/

/-- `AllocCostModel`-free SPQR encoder-point validity of the current session stored for `rem` on
`F` under `scopeKit` (`True` when no session is present). -/
def PeerSpqrValid (F : FsFiles) (rem : AddrVal) : Prop :=
  match loadRec scopeKit F rem with
  | .ok (some r) =>
    match r.currentSession with
    | some sess => ValidEncoderPts sess.state.pqRatchetState ∧
        sess.state.pqRatchetState.length < 2 ^ 31
    | none => True
  | _ => True

/-- At any `ScopeAt` record loaded from `StoresGhost.opened.sessions` by `w1SessKit`, `PeerSpqrValid`
delivers `ValidEncoderPts otrPqr ∧ otrPqr.length < 2 ^ 31` on the session's `pqRatchetState`. -/
theorem peerSpqrValid_of_scopeAt {B : RunBudgets} {img : Arm64.Obj.Image}
    {F : FsFiles} {peer : AddrGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otrPqr : List (BitVec 8)}
    (hScAt : (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hpqr : otrPqr = sess.state.pqRatchetState)
    (hValid : PeerSpqrValid F rem) :
    ValidEncoderPts otrPqr ∧ otrPqr.length < 2 ^ 31 := by
  obtain ⟨bs, hbs, hla⟩ := hScAt.2
  have hlr : loadRec scopeKit F rem = .ok (some r) := by
    symm
    exact loadRec_unique encodeInjOn_deserializeScopeP_Q (hbs ▸ hla)
  unfold PeerSpqrValid at hValid
  rw [hlr] at hValid
  dsimp only at hValid
  rw [hcur] at hValid
  simpa [hpqr] using hValid

/-- On every `CliPqxdhInputs W i` whose `argv` parses to `.send peer`, `PeerSpqrValid` holds on
`runFiles i` and `addrValOf peer`. -/
theorem peerSpqrValid_of_cliPqInputs_send {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) :
    PeerSpqrValid (runFiles i) (addrValOf peer) := by
  obtain ⟨st, hwf, hcases⟩ := hi
  rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ | ⟨m, rc, _, rfl⟩ |
    ⟨c, rc, _, _, _, rfl⟩
  · have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
    rw [ha, parseArgs_init] at hparse
    cases hparse
  · have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
    have hpeer : addrValOf peer = partyAddr st.party.other :=
      callPeer_of_cmd (.send (partyAddress st.party.other)) rfl (ha ▸ hparse) rfl
    have hcov := fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs
    have hok := filesOkPeer_pqSend W st m r hcov (pqSessBytes_le_fileCapBytes hwf)
    have hlrK := loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hok
    have hlrIn := loadRec_pqSend encodeInjOn_scopeIn W st m r hcov (pqSessBytes_le_fileCapBytes hwf)
    rw [hpeer]
    unfold PeerSpqrValid
    rw [hlrK, hlrIn]
    rcases hs : st.session with _ | ⟨x, g⟩
    · trivial
    · simp only [Option.map_some, toRecord_extrasOf_eq, sessionOfX]
      have hwf_sess := hwf.1 x g hs
      rcases hwf_sess.1 with ⟨g₀, hr, _, hsess₀⟩
      have hpq31 : g.session.pqRatchetState.length < 2 ^ 31 :=
        Nat.lt_of_le_of_lt (pqRatchetState_length_le_encodeRecordX (fun _ => x) g) hwf_sess.2.2
      have hve := validEncoderPts_of_reachPq hr
      rw [hsess₀] at hve
      exact ⟨hve, hpq31⟩
  · have ha : (pqRecvInputs W st (wireWhisper :: c) rc).argv =
        (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_recv] at hparse
    cases hparse
  · have ha : (pqRecvInputs W st (wirePrekey :: m.bytes) rc).argv =
        (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_recv] at hparse
    cases hparse
  · have ha : (pqRecvInputs W st c rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_recv] at hparse
    cases hparse

/-- Bundled `AllocCostModel`-free domain caps (`stdinCap`, `fileCap`) on a CLI invocation `i`. -/
structure CliPqDomainCaps (stdinCap fileCap : Nat) (i : Inputs) : Prop where
  stdin_le : i.stdin.length ≤ stdinCap
  argv_le : i.argv.length ≤ 3
  files_bounded : FilesBounded fileCap (initFsState (cliInputs i))
  coins_le : (coinsOf i).length ≤ fileCap
  send_spqr_valid : ∀ peer,
    parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
    PeerSpqrValid (runFiles i) (addrValOf peer)

/-- Unconditional `CliPqDomainCaps (2 ^ 32) (2 ^ 31) i` derived solely from `CliPqxdhInputs W i`. -/
theorem cliPqDomainCaps_2_32_of_cliPqInputs {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) :
    CliPqDomainCaps (2 ^ 32) (2 ^ 31) i :=
  ⟨stdin_length_le_of_cliPqInputs hi,
   argv_length_le_of_cliPqInputs hi,
   filesBounded_initFsState_of_cliPqInputs hi,
   Nat.le_of_lt (coinsOf_length_lt_of_cliPqInputs hi),
   fun _ hp => peerSpqrValid_of_cliPqInputs_send hi hp⟩

/-- Tight `CliPqDomainCaps stdinCap (max sessionCapBytes bkCap) i` under `SessionRecordCapInDomain W sessionCapBytes` and `PqPartyBaseKeysCap bkCap st`. -/
theorem cliPqDomainCaps_of_pqParty_caps {W : PEParams} {st : PqParty} {stdinCap bkCap : Nat}
    {i : Inputs}
    (hwf : PqxdhPartyInSpecDomain W st)
    (hSess : SessionRecordCapInDomain W sessionCapBytes)
    (hBk : PqPartyBaseKeysCap bkCap st)
    (hstdin : i.stdin.length ≤ stdinCap)
    (hcase :
      (st.session = none ∧ ∃ b t, i = pqInitInputs W st b t) ∨
      (∃ m r, m.length < 2 ^ 32 ∧ i = pqSendInputs W st m r) ∨
      (∃ c rc, c.length < 2 ^ 32 ∧ i = pqRecvInputs W st (wireWhisper :: c) rc) ∨
      (∃ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 ∧ i = pqRecvInputs W st (wirePrekey :: m.bytes) rc) ∨
      (∃ c rc, c.length < 2 ^ 32 ∧ c.head? ≠ some wireWhisper ∧ c.head? ≠ some wirePrekey ∧
        i = pqRecvInputs W st c rc)) :
    CliPqDomainCaps stdinCap (max sessionCapBytes bkCap) i := by
  have hi : CliPqxdhInputs W i := ⟨st, hwf, hcase⟩
  exact ⟨hstdin,
    argv_length_le_of_cliPqInputs hi,
    filesBounded_of_pqParty_caps hwf hSess hBk hcase,
    coinsOf_length_le_of_files_le (pqParty_files_mem_le hwf hSess hBk hcase),
    fun _ hp => peerSpqrValid_of_cliPqInputs_send hi hp⟩

end LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
