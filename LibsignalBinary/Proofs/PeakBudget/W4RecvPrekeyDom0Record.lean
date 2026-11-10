/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.RecordX.BridgeCommon
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf
public import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-!
# Prost `RecordStructure` Wire Round-Trip & Session-File Tie

Prost `RecordStructure` wire decoding and session-file identity on `CliPqOrD3RecvDom`:
1. Defines the prost protobuf wire decoder `RecordStructure.decode` / `RecordStructure.deserialize`
   for `storage.proto`'s `RecordStructure` (`optional SessionStructure current_session = 1;
   repeated SessionStructure previous_sessions = 2;`) over `RecordCodecs.decodeFieldsLoop`, and
   proves that decoding `encodeRecordUnderExtras E g` or `Record.encodeRecord (toRecord (extrasOf E) g)`
   (for payloads `< 2 ^ 64` bytes) yields `previousSessions = []`.
2. Proves that on `pqRecvInputs W st ct rc` (under `PqxdhPartyInSpecDomain W st`) and across
   `CliPqOrD3RecvDom W i`, the peer session file in `StoresGhost.opened.sessions` holds
   `encodeRecordUnderExtras (fun _ => x) g` (or `[]` when `st.session = none`), so
   `RecordStructure.decode` / `RecordStructure.deserialize` yields `previousSessions = []`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record

open Arm64.Process (bytesOfString)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification.E2E
  (PEParams RecordExtras encStateUnderExtras encodeRecordUnderExtras lenField msgField
   wirePrekey wireWhisper)
open CryptoVerification.E2E.Record (encSession encodeRecord toRecord)
open CryptoVerification.E2E.RecordX (encodeRecordX_eq_toRecord extrasOf)
open CryptoVerification.LibsignalProtoCodec
  (WireType encodeKey encodeVarint encodeVarint_ne_nil mergeBytes mergeBytes_encode)
open CryptoVerification.LibsignalSpqrV1 (Bytes)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RecordCodecs
  (LoopsTo decodeFieldsLoop loopsTo_field loopsTo_nil skipUnknown)
open CryptoVerification.SignalSession
  (Address CliPqxdhInputs Cmd Inputs PqParty PqxdhPartyInSpecDomain bundleDir encodeDir fileCapBytes
   partyAddress pqInitInputs pqRecvInputs pqSendInputs sessionFile)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText decimalText pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV cliIo encodeInjOn_scopeIn parseArgs ratchetScopeCoversPq_scopeIn)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
  (blockDir5 encodeDir_find_at recvBucket_sessionFile)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (loadRec_scopeKit_eq)
open CryptoVerification.SignalSession.Cli.RunRefine
  (addrValE parseArgs_init parseArgs_send)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn callPeer_of_cmd encodeInjOn_deserializeScopeP_Q filesOkPeer_pqRecv loadRec
   loadRec_pqRecv partyAddr pqSessBytes_le_fileCapBytes scopeIn scopeKit)
open LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap
  (reachPq_encodeRecordX_length_le_fileCapBytes)

/-! ## Prost `RecordStructure` Wire Codec & `previousSessions = []` -/

/-- Prost wire-format representation of `storage.proto`'s `RecordStructure`:
`optional SessionStructure current_session = 1; repeated SessionStructure previous_sessions = 2;`
with submessage bodies retained as raw length-delimited byte slices. -/
structure RecordStructure where
  currentSession : Option (List (BitVec 8))
  previousSessions : List (List (BitVec 8))
  deriving DecidableEq

/-- Default (all-empty) `RecordStructure` prior to prost `Message::merge`. -/
def RecordStructure.empty : RecordStructure :=
  { currentSession := none, previousSessions := [] }

/-- Prost `RecordStructure::merge_field`:
- tag `1` (`optional SessionStructure current_session = 1`): merges length-delimited submessage
  bytes (`getD [] ++ v` matches prost repeated-tag submessage merge and gives `some v` from `empty`);
- tag `2` (`repeated SessionStructure previous_sessions = 2`): appends one length-delimited entry;
- any other tag: skips unknown fields via `RecordCodecs.skipUnknown`. -/
def RecordStructure.mergeField (m : RecordStructure) (tag : Nat) (wt : WireType)
    (bs : List (BitVec 8)) : Option (RecordStructure × List (BitVec 8)) :=
  match tag with
  | 1 =>
    (mergeBytes wt bs).map fun (v, r) =>
      ({ m with currentSession := some (m.currentSession.getD [] ++ v) }, r)
  | 2 =>
    (mergeBytes wt bs).map fun (v, r) =>
      ({ m with previousSessions := m.previousSessions ++ [v] }, r)
  | _ => skipUnknown m tag wt bs

/-- Prost `RecordStructure::decode` (`decodeFieldsLoop` with fuel `bs.length` from `empty`). -/
def RecordStructure.decode (bs : List (BitVec 8)) : Option RecordStructure :=
  decodeFieldsLoop RecordStructure.mergeField bs.length RecordStructure.empty bs

/-- Session-store slice deserializer matching CLI `load_session`: empty slice returns `.ok none`,
non-empty slice runs prost `RecordStructure.decode`. -/
def RecordStructure.deserialize (bs : List (BitVec 8)) : Except Unit (Option RecordStructure) :=
  match bs with
  | [] => .ok none
  | _ :: _ =>
    match RecordStructure.decode bs with
    | some r => .ok (some r)
    | none => .error ()

@[simp]
theorem RecordStructure.decode_nil : RecordStructure.decode [] = some RecordStructure.empty :=
  rfl

@[simp]
theorem RecordStructure.deserialize_nil : RecordStructure.deserialize [] = .ok none :=
  rfl

theorem lenField_ne_nil (tag : Nat) (payload : List (BitVec 8)) :
    lenField tag payload ≠ [] := by
  unfold lenField
  intro h
  have hpos : 0 < (encodeKey tag .lengthDelimited).length :=
    List.length_pos_iff.mpr (encodeVarint_ne_nil _)
  have hlen :
      (encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 payload.length) ++
          payload).length = 0 :=
    congrArg List.length h
  simp only [List.length_append] at hlen
  omega

theorem payload_length_lt_lenField (tag : Nat) (payload : List (BitVec 8)) :
    payload.length < (lenField tag payload).length := by
  unfold lenField
  have hpos : 0 < (encodeKey tag .lengthDelimited).length :=
    List.length_pos_iff.mpr (encodeVarint_ne_nil _)
  simp only [List.length_append]
  omega

theorem loopsTo_lenField1 (payload : List (BitVec 8)) (hlen : payload.length < 2 ^ 64) :
    LoopsTo RecordStructure.mergeField RecordStructure.empty (lenField 1 payload)
      ⟨some payload, []⟩ := by
  have hmerge :
      RecordStructure.mergeField RecordStructure.empty 1 .lengthDelimited
        ((encodeVarint (BitVec.ofNat 64 payload.length) ++ payload) ++ []) =
        some (⟨some payload, []⟩, []) := by
    have hb := mergeBytes_encode payload [] hlen
    simp only [List.append_nil] at hb ⊢
    simp [RecordStructure.mergeField, RecordStructure.empty, hb]
  have hloop :=
    loopsTo_field RecordStructure.mergeField 1 .lengthDelimited (by decide) (by decide)
      RecordStructure.empty ⟨some payload, []⟩ ⟨some payload, []⟩
      (encodeVarint (BitVec.ofNat 64 payload.length) ++ payload) []
      hmerge (loopsTo_nil RecordStructure.mergeField ⟨some payload, []⟩)
  simpa only [lenField, List.append_assoc, List.append_nil] using hloop

theorem decode_lenField1 {payload : List (BitVec 8)} (hlen : payload.length < 2 ^ 64) :
    RecordStructure.decode (lenField 1 payload) = some ⟨some payload, []⟩ :=
  loopsTo_lenField1 payload hlen (lenField 1 payload).length (Nat.le_refl _)

theorem deserialize_lenField1 {payload : List (BitVec 8)} (hlen : payload.length < 2 ^ 64) :
    RecordStructure.deserialize (lenField 1 payload) = .ok (some ⟨some payload, []⟩) := by
  obtain ⟨b, bs, hcons⟩ := List.exists_cons_of_ne_nil (lenField_ne_nil 1 payload)
  unfold RecordStructure.deserialize
  rw [hcons]
  dsimp only
  rw [← hcons, decode_lenField1 hlen]

theorem decode_msgField1_some {payload : List (BitVec 8)} (hlen : payload.length < 2 ^ 64) :
    RecordStructure.decode (msgField 1 (some payload)) = some ⟨some payload, []⟩ :=
  decode_lenField1 hlen

theorem encodeRecordUnderExtras_eq_lenField (E : Party → RecordExtras) (g : GhostState Bytes) :
    encodeRecordUnderExtras E g = lenField 1 (encStateUnderExtras (E g.party) g.session) :=
  rfl

theorem encodeRecordUnderExtras_ne_nil (E : Party → RecordExtras) (g : GhostState Bytes) :
    encodeRecordUnderExtras E g ≠ [] :=
  lenField_ne_nil 1 (encStateUnderExtras (E g.party) g.session)

theorem encStateUnderExtras_length_lt_encodeRecordUnderExtras
    (E : Party → RecordExtras) (g : GhostState Bytes) :
    (encStateUnderExtras (E g.party) g.session).length < (encodeRecordUnderExtras E g).length :=
  payload_length_lt_lenField 1 (encStateUnderExtras (E g.party) g.session)

/-- Prost `RecordStructure.decode` on `encodeRecordUnderExtras E g` yields
`currentSession = some (encStateUnderExtras …)` and `previousSessions = []`. -/
theorem decode_encodeRecordUnderExtras {E : Party → RecordExtras} {g : GhostState Bytes}
    (hlen : (encStateUnderExtras (E g.party) g.session).length < 2 ^ 64) :
    RecordStructure.decode (encodeRecordUnderExtras E g) =
      some ⟨some (encStateUnderExtras (E g.party) g.session), []⟩ :=
  decode_lenField1 hlen

/-- Variant of `decode_encodeRecordUnderExtras` taking a bound on the outer record length. -/
theorem decode_encodeRecordUnderExtras_of_record_le {E : Party → RecordExtras}
    {g : GhostState Bytes} (hlen : (encodeRecordUnderExtras E g).length ≤ 2 ^ 64) :
    RecordStructure.decode (encodeRecordUnderExtras E g) =
      some ⟨some (encStateUnderExtras (E g.party) g.session), []⟩ :=
  decode_encodeRecordUnderExtras
    (Nat.lt_of_lt_of_le (encStateUnderExtras_length_lt_encodeRecordUnderExtras E g) hlen)

/-- `RecordStructure.deserialize` round-trip on `encodeRecordUnderExtras E g`. -/
theorem deserialize_encodeRecordUnderExtras {E : Party → RecordExtras} {g : GhostState Bytes}
    (hlen : (encStateUnderExtras (E g.party) g.session).length < 2 ^ 64) :
    RecordStructure.deserialize (encodeRecordUnderExtras E g) =
      .ok (some ⟨some (encStateUnderExtras (E g.party) g.session), []⟩) :=
  deserialize_lenField1 hlen

theorem deserialize_encodeRecordUnderExtras_of_record_le {E : Party → RecordExtras}
    {g : GhostState Bytes} (hlen : (encodeRecordUnderExtras E g).length ≤ 2 ^ 64) :
    RecordStructure.deserialize (encodeRecordUnderExtras E g) =
      .ok (some ⟨some (encStateUnderExtras (E g.party) g.session), []⟩) :=
  deserialize_encodeRecordUnderExtras
    (Nat.lt_of_lt_of_le (encStateUnderExtras_length_lt_encodeRecordUnderExtras E g) hlen)

/-- `previousSessions = []` projection from `RecordStructure.decode` on `encodeRecordUnderExtras E g`. -/
theorem previousSessions_eq_nil_of_decode_encodeRecordUnderExtras
    {E : Party → RecordExtras} {g : GhostState Bytes} {rec : RecordStructure}
    (hlen : (encodeRecordUnderExtras E g).length ≤ 2 ^ 64)
    (hdec : RecordStructure.decode (encodeRecordUnderExtras E g) = some rec) :
    rec.previousSessions = [] := by
  rw [decode_encodeRecordUnderExtras_of_record_le hlen] at hdec
  injection hdec with hrec
  rw [← hrec]

/-- `previousSessions = []` projection from `RecordStructure.deserialize` on `encodeRecordUnderExtras E g`. -/
theorem previousSessions_eq_nil_of_deserialize_encodeRecordUnderExtras
    {E : Party → RecordExtras} {g : GhostState Bytes} {rec : RecordStructure}
    (hlen : (encodeRecordUnderExtras E g).length ≤ 2 ^ 64)
    (hdes : RecordStructure.deserialize (encodeRecordUnderExtras E g) = .ok (some rec)) :
    rec.previousSessions = [] := by
  rw [deserialize_encodeRecordUnderExtras_of_record_le hlen] at hdes
  injection hdes with hsome
  injection hsome with hrec
  rw [← hrec]

/-- Proof-side `E2E.Record.encodeRecord (toRecord (extrasOf E) g)` round-trip via
`encodeRecordX_eq_toRecord`. -/
theorem decode_encodeRecord_toRecord {E : Party → RecordExtras} {g : GhostState Bytes}
    (hlen : (encodeRecordUnderExtras E g).length ≤ 2 ^ 64) :
    RecordStructure.decode (encodeRecord (toRecord (extrasOf E) g)) =
      some ⟨some (encStateUnderExtras (E g.party) g.session), []⟩ := by
  rw [← encodeRecordX_eq_toRecord E g]
  exact decode_encodeRecordUnderExtras_of_record_le hlen

theorem deserialize_encodeRecord_toRecord {E : Party → RecordExtras} {g : GhostState Bytes}
    (hlen : (encodeRecordUnderExtras E g).length ≤ 2 ^ 64) :
    RecordStructure.deserialize (encodeRecord (toRecord (extrasOf E) g)) =
      .ok (some ⟨some (encStateUnderExtras (E g.party) g.session), []⟩) := by
  rw [← encodeRecordX_eq_toRecord E g]
  exact deserialize_encodeRecordUnderExtras_of_record_le hlen

/-! ## Session-File Identity (`sessionFile` / `encodeDir`) & `loadRec` Tie -/

/-- Combined honest PQXDH + D3 arbitrary-wire `recv` domain (`CliPqxdhInputs ∨ D3 pqRecvInputs`). -/
abbrev CliPqOrD3RecvDom (W : PEParams) (i : Inputs) : Prop :=
  CliPqxdhInputs W i ∨
    ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
      PqxdhPartyInSpecDomain W st ∧ i = pqRecvInputs W st ct rc

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

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem utf8_append_eq (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  rw [utf8_eq_kutf8, utf8_eq_kutf8, utf8_eq_kutf8]
  simp [kutf8, String.toList_append, List.flatMap_append]

/-- Parsed `.recv peer` address on `pqRecvInputs W st ct rc` equals `partyAddr st.party.other`. -/
theorem pqRecv_peer_eq {W : PEParams} {st : PqParty} {ct : List (BitVec 8)} {rc : BitVec 256}
    {peer : AddrV}
    (hparse : parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
      some (.recv peer)) :
    addrValOf peer = partyAddr st.party.other := by
  have ha : (pqRecvInputs W st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  exact callPeer_of_cmd (.recv (partyAddress st.party.other)) rfl (ha ▸ hparse) rfl

/-- Store path identity: `StoresGhost.opened.sessions` for `partyAddr P` resolves to
`utf8 (sessionFile (partyAddress P))`. -/
theorem sessions_path_partyAddr_eq_sessionFile (P : Party) :
    pathOf StoresGhost.opened.sessions.path (addressText (partyAddr P)) =
      utf8 (sessionFile (partyAddress P)) := by
  have hroot : StoresGhost.opened.sessions.path = utf8 "sessions" := rfl
  have hne : utf8 "sessions" ≠ [] := by rw [utf8_eq_kutf8]; decide
  have had : addressText (partyAddr P) = utf8 (partyAddress P).text := by
    have hp : partyAddr P = addrValE P := rfl
    have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
    rw [hp]
    simp only [addressText, addrValE, decimalText, h1, Address.text, partyAddress]
    rw [← utf8_append_eq, ← utf8_append_eq]
  rw [hroot, had]
  simp only [pathOf, hne, ↓reduceIte, sessionFile]
  rw [← utf8_append_eq, ← utf8_append_eq]
  rfl

/-- On `pqRecvInputs`, the CLI session store path for the parsed `peer` is
`utf8 (sessionFile (partyAddress st.party.other))`. -/
theorem pqRecv_sessions_path_eq_sessionFile {W : PEParams} {st : PqParty}
    {ct : List (BitVec 8)} {rc : BitVec 256} {peer : AddrV}
    (hparse : parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
      some (.recv peer)) :
    pathOf StoresGhost.opened.sessions.path (addressText (addrValOf peer)) =
      utf8 (sessionFile (partyAddress st.party.other)) := by
  rw [pqRecv_peer_eq hparse]
  exact sessions_path_partyAddr_eq_sessionFile st.party.other

/-- `encodeDir W st` at `sessionFile (partyAddress st.party.other)` holds
`encodeRecordUnderExtras (fun _ => x) g` when `st.session = some (x, g)`, and `[]` when
`st.session = none`. -/
theorem encodeDir_find_sessionFile_eq (W : PEParams) (st : PqParty) :
    (((encodeDir W st).reverse.find?
        (fun x => x.1 == sessionFile (partyAddress st.party.other))).map Prod.snd).getD [] =
      match st.session with
      | some (x, g) => encodeRecordUnderExtras (fun _ => x) g
      | none => [] := by
  rw [encodeDir_find_at, recvBucket_sessionFile]
  cases h : st.session with
  | none => simp [blockDir5, h]
  | some xg =>
    rcases xg with ⟨x, g⟩
    simp [blockDir5, h]

/-- Byte-length cap `≤ fileCapBytes` (`= 1 MiB < 2 ^ 64`) on the encoded record of any session in a
`PqxdhPartyInSpecDomain W st` party. -/
theorem encodeRecordUnderExtras_length_le_fileCapBytes_of_wf {W : PEParams} {st : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) {x : RecordExtras} {g : GhostState Bytes}
    (hs : st.session = some (x, g)) :
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes := by
  obtain ⟨⟨g₀, hR₀, _, hs₀⟩, _⟩ := hwf.1 x g hs
  unfold encodeRecordUnderExtras
  rw [← hs₀]
  exact reachPq_encodeRecordX_length_le_fileCapBytes hR₀

theorem encodeRecordUnderExtras_length_le_2pow64_of_wf {W : PEParams} {st : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) {x : RecordExtras} {g : GhostState Bytes}
    (hs : st.session = some (x, g)) :
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ 2 ^ 64 := by
  have hcap := encodeRecordUnderExtras_length_le_fileCapBytes_of_wf hwf hs
  have hfc : fileCapBytes ≤ 2 ^ 64 := by decide
  exact Nat.le_trans hcap hfc

/-- Raw store-get identity on `pqRecvInputs`:
`StoresGhost.opened.sessions.get cliIo.rd (runFiles (pqRecvInputs W st ct rc)) (addressText (addrValOf peer))`
returns `encodeRecordUnderExtras (fun _ => x) g` (when `st.session = some (x, g)`) or `[]`
(when `st.session = none`). -/
theorem sessions_get_pqRecv_eq {W : PEParams} {st : PqParty} {ct : List (BitVec 8)}
    {rc : BitVec 256} {peer : AddrV} (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
      some (.recv peer)) :
    StoresGhost.opened.sessions.get cliIo.rd (runFiles (pqRecvInputs W st ct rc))
        (addressText (addrValOf peer)) =
      .ok (match st.session with
           | some (x, g) => encodeRecordUnderExtras (fun _ => x) g
           | none => []) := by
  rw [pqRecv_peer_eq hparse]
  have hcov := fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs
  have hcap := pqSessBytes_le_fileCapBytes hwf
  have hok := filesOkPeer_pqRecv W st ct rc hcov hcap
  have hlrIn := loadRec_pqRecv encodeInjOn_scopeIn W st ct rc hcov hcap
  obtain ⟨bs, hget, hwfBs⟩ := hok.sessGet
  unfold loadRec at hlrIn
  rw [hget] at hlrIn ⊢
  rcases bs with _ | ⟨b, bs'⟩
  · cases hs : st.session with
    | none => rfl
    | some xg =>
      rw [hs] at hlrIn
      cases hlrIn
  · rcases hwfBs with hnil | hex
    · cases hnil
    · simp only [hex, ↓reduceDIte] at hlrIn
      cases hs : st.session with
      | none =>
        rw [hs] at hlrIn
        cases hlrIn
      | some xg =>
        rcases xg with ⟨x, g⟩
        rw [hs] at hlrIn
        dsimp only [Option.map_some] at hlrIn
        injection hlrIn with hsome
        injection hsome with hchoose
        have henc : encodeRecord (Classical.choose hex) = b :: bs' := (Classical.choose_spec hex).1
        rw [hchoose, ← encodeRecordX_eq_toRecord (fun _ => x) g] at henc
        rw [← henc]

/-- Generic `Slots.loadRec` identity on `pqRecvInputs` for any `Scope` extending `scopeIn` with
`EncodeInjOn Scope`. -/
theorem loadRec_pqRecv_of_scope {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) (hsub : ∀ r, scopeIn r → Scope r)
    {st : PqParty} {ct : List (BitVec 8)} {rc : BitVec 256} {peer : AddrV}
    (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
      some (.recv peer)) :
    loadRec Scope (runFiles (pqRecvInputs W st ct rc)) (addrValOf peer) =
      .ok (st.session.map fun (x, g) => toRecord (extrasOf fun _ => x) g) := by
  rw [pqRecv_peer_eq hparse]
  have hcov := fun x g hs => hsub _ (ratchetScopeCoversPq_scopeIn W st x g hwf hs)
  exact loadRec_pqRecv hinj W st ct rc hcov (pqSessBytes_le_fileCapBytes hwf)

/-- `loadRec scopeIn` specialization on `pqRecvInputs`. -/
theorem loadRec_pqRecv_scopeIn_eq {W : PEParams} {st : PqParty} {ct : List (BitVec 8)}
    {rc : BitVec 256} {peer : AddrV} (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
      some (.recv peer)) :
    loadRec scopeIn (runFiles (pqRecvInputs W st ct rc)) (addrValOf peer) =
      .ok (st.session.map fun (x, g) => toRecord (extrasOf fun _ => x) g) :=
  loadRec_pqRecv_of_scope encodeInjOn_scopeIn (fun _ h => h) hwf hparse

/-- `loadRec scopeKit` specialization on `pqRecvInputs`. -/
theorem loadRec_pqRecv_scopeKit_eq {W : PEParams} {st : PqParty} {ct : List (BitVec 8)}
    {rc : BitVec 256} {peer : AddrV} (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
      some (.recv peer)) :
    loadRec scopeKit (runFiles (pqRecvInputs W st ct rc)) (addrValOf peer) =
      .ok (st.session.map fun (x, g) => toRecord (extrasOf fun _ => x) g) := by
  rw [pqRecv_peer_eq hparse]
  have hcov := fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs
  have hcap := pqSessBytes_le_fileCapBytes hwf
  have hok := filesOkPeer_pqRecv W st ct rc hcov hcap
  rw [loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hok]
  exact loadRec_pqRecv encodeInjOn_scopeIn W st ct rc hcov hcap

/-- Reduction of `CliPqOrD3RecvDom W i` under `.recv peer`: `.init` and `.send` arms are refuted by
`parseArgs_init` / `parseArgs_send`, leaving `i = pqRecvInputs W st ct rc` with
`PqxdhPartyInSpecDomain W st`. -/
theorem cliPqOrD3RecvDom_eq_pqRecvInputs {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
      PqxdhPartyInSpecDomain W st ∧ i = pqRecvInputs W st ct rc := by
  rcases hi with ⟨st, hwf, hcases⟩ | hex
  · rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ | ⟨m, rc, _, rfl⟩ |
      ⟨c, rc, _, _, _, rfl⟩
    · have ha : (pqInitInputs W st b t).argv =
          (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
      rw [ha, parseArgs_init] at hparse
      cases hparse
    · have ha : (pqSendInputs W st m r).argv =
          (Cmd.send (partyAddress st.party.other)).argv := rfl
      rw [ha, parseArgs_send] at hparse
      cases hparse
    · exact ⟨st, wireWhisper :: c, rc, hwf, rfl⟩
    · exact ⟨st, wirePrekey :: m.bytes, rc, hwf, rfl⟩
    · exact ⟨st, c, rc, hwf, rfl⟩
  · exact hex

/-! ## Combined Session-File & `loadRec` Decode Ties on `CliPqOrD3RecvDom` -/

/-- On any `CliPqOrD3RecvDom W i` `.recv peer` input, if the peer session file is non-empty
(`b :: bs`), it equals `encodeRecordUnderExtras (fun _ => x) g` for the stored session `(x, g)`,
decodes under prost `RecordStructure.decode` to `⟨some (encStateUnderExtras x g.session), []⟩`, and
has `previousSessions = []`. -/
theorem sessions_get_cliPqOrD3RecvDom_nonempty_decode {W : PEParams} {i : Inputs} {peer : AddrV}
    {b : BitVec 8} {bs : List (BitVec 8)}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hget : StoresGhost.opened.sessions.get cliIo.rd (runFiles i) (addressText (addrValOf peer)) =
      .ok (b :: bs)) :
    ∃ (st : PqParty) (x : RecordExtras) (g : GhostState Bytes),
      PqxdhPartyInSpecDomain W st ∧
      st.session = some (x, g) ∧
      addrValOf peer = partyAddr st.party.other ∧
      pathOf StoresGhost.opened.sessions.path (addressText (addrValOf peer)) =
        utf8 (sessionFile (partyAddress st.party.other)) ∧
      b :: bs = encodeRecordUnderExtras (fun _ => x) g ∧
      RecordStructure.decode (b :: bs) =
        some ⟨some (encStateUnderExtras x g.session), []⟩ ∧
      RecordStructure.deserialize (b :: bs) =
        .ok (some ⟨some (encStateUnderExtras x g.session), []⟩) := by
  obtain ⟨st, ct, rc, hwf, rfl⟩ := cliPqOrD3RecvDom_eq_pqRecvInputs hi hparse
  rw [sessions_get_pqRecv_eq hwf hparse] at hget
  cases hs : st.session with
  | none =>
    rw [hs] at hget
    cases hget
  | some xg =>
    rcases xg with ⟨x, g⟩
    rw [hs] at hget
    injection hget with hbs
    have hlen := encodeRecordUnderExtras_length_le_2pow64_of_wf hwf hs
    refine ⟨st, x, g, hwf, hs, pqRecv_peer_eq hparse, pqRecv_sessions_path_eq_sessionFile hparse,
      hbs.symm, ?_, ?_⟩
    · rw [← hbs]
      exact decode_encodeRecordUnderExtras_of_record_le hlen
    · rw [← hbs]
      exact deserialize_encodeRecordUnderExtras_of_record_le hlen

/-- For any `Scope` extending `scopeIn` with `EncodeInjOn Scope` on `CliPqOrD3RecvDom W i`, if
`loadRec Scope (runFiles i) (addrValOf peer) = .ok (some r)`, then `r = toRecord (extrasOf fun _ => x) g`,
`encodeRecord r = encodeRecordUnderExtras (fun _ => x) g`, and `RecordStructure.decode (encodeRecord r)`
has `previousSessions = []`. -/
theorem loadRec_cliPqOrD3RecvDom_some_decode {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) (hsub : ∀ r, scopeIn r → Scope r)
    {i : Inputs} {peer : AddrV} {r : SessionRecord (List (BitVec 8))}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hlr : loadRec Scope (runFiles i) (addrValOf peer) = .ok (some r)) :
    ∃ (st : PqParty) (x : RecordExtras) (g : GhostState Bytes),
      PqxdhPartyInSpecDomain W st ∧
      st.session = some (x, g) ∧
      addrValOf peer = partyAddr st.party.other ∧
      r = toRecord (extrasOf fun _ => x) g ∧
      encodeRecord r = encodeRecordUnderExtras (fun _ => x) g ∧
      RecordStructure.decode (encodeRecord r) =
        some ⟨some (encStateUnderExtras x g.session), []⟩ ∧
      RecordStructure.deserialize (encodeRecord r) =
        .ok (some ⟨some (encStateUnderExtras x g.session), []⟩) := by
  obtain ⟨st, ct, rc, hwf, rfl⟩ := cliPqOrD3RecvDom_eq_pqRecvInputs hi hparse
  rw [loadRec_pqRecv_of_scope hinj hsub hwf hparse] at hlr
  cases hs : st.session with
  | none =>
    rw [hs] at hlr
    cases hlr
  | some xg =>
    rcases xg with ⟨x, g⟩
    rw [hs] at hlr
    dsimp only [Option.map_some] at hlr
    injection hlr with hsome
    injection hsome with hr
    have hlen := encodeRecordUnderExtras_length_le_2pow64_of_wf hwf hs
    have henc : encodeRecord r = encodeRecordUnderExtras (fun _ => x) g := by
      rw [← hr, ← encodeRecordX_eq_toRecord (fun _ => x) g]
    refine ⟨st, x, g, hwf, hs, pqRecv_peer_eq hparse, hr.symm, henc, ?_, ?_⟩
    · rw [henc]
      exact decode_encodeRecordUnderExtras_of_record_le hlen
    · rw [henc]
      exact deserialize_encodeRecordUnderExtras_of_record_le hlen

/-- `loadRec scopeKit` specialization of `loadRec_cliPqOrD3RecvDom_some_decode`. -/
theorem loadRec_cliPqOrD3RecvDom_scopeKit_some_decode {W : PEParams}
    {i : Inputs} {peer : AddrV} {r : SessionRecord (List (BitVec 8))}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hlr : loadRec scopeKit (runFiles i) (addrValOf peer) = .ok (some r)) :
    ∃ (st : PqParty) (x : RecordExtras) (g : GhostState Bytes),
      PqxdhPartyInSpecDomain W st ∧
      st.session = some (x, g) ∧
      addrValOf peer = partyAddr st.party.other ∧
      r = toRecord (extrasOf fun _ => x) g ∧
      encodeRecord r = encodeRecordUnderExtras (fun _ => x) g ∧
      RecordStructure.decode (encodeRecord r) =
        some ⟨some (encStateUnderExtras x g.session), []⟩ ∧
      RecordStructure.deserialize (encodeRecord r) =
        .ok (some ⟨some (encStateUnderExtras x g.session), []⟩) := by
  obtain ⟨st, ct, rc, hwf, rfl⟩ := cliPqOrD3RecvDom_eq_pqRecvInputs hi hparse
  have hlrIn : loadRec scopeIn (runFiles (pqRecvInputs W st ct rc)) (addrValOf peer) = .ok (some r) := by
    rw [loadRec_pqRecv_scopeIn_eq hwf hparse, ← loadRec_pqRecv_scopeKit_eq hwf hparse, hlr]
  exact loadRec_cliPqOrD3RecvDom_some_decode encodeInjOn_scopeIn (fun _ h => h)
    (Or.inr ⟨st, ct, rc, hwf, rfl⟩) hparse hlrIn

/-- Direct `previousSessions = []` corollary for any `rec : RecordStructure` decoded from the
loaded `scopeKit` session record on `CliPqOrD3RecvDom W i`. -/
theorem previousSessions_eq_nil_of_loadRec_scopeKit {W : PEParams}
    {i : Inputs} {peer : AddrV} {r : SessionRecord (List (BitVec 8))} {rec : RecordStructure}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hlr : loadRec scopeKit (runFiles i) (addrValOf peer) = .ok (some r))
    (hdec : RecordStructure.decode (encodeRecord r) = some rec) :
    rec.previousSessions = [] := by
  obtain ⟨_, _, _, _, _, _, _, _, hdec₀, _⟩ :=
    loadRec_cliPqOrD3RecvDom_scopeKit_some_decode hi hparse hlr
  rw [hdec₀] at hdec
  injection hdec with hrec
  rw [← hrec]

/-- Direct `previousSessions = []` corollary for any `r : SessionRecord (List (BitVec 8))` whose
serialized bytes fit in `≤ 2 ^ 64` bytes: `RecordStructure.decode (encodeRecord r)` yields
`previousSessions = []`. -/
theorem previousSessions_eq_nil_of_encodeRecord {r : SessionRecord (List (BitVec 8))}
    {rec : RecordStructure} (hlen : (encodeRecord r).length ≤ 2 ^ 64)
    (hdec : RecordStructure.decode (encodeRecord r) = some rec) :
    rec.previousSessions = [] := by
  cases r with
  | mk cur =>
    cases cur with
    | none =>
      have hempty : encodeRecord ⟨none⟩ = [] := rfl
      rw [hempty, RecordStructure.decode_nil] at hdec
      injection hdec with hrec
      rw [← hrec]
      rfl
    | some s =>
      have henc : encodeRecord ⟨some s⟩ = lenField 1 (encSession s) := rfl
      have hs_lt : (encSession s).length < 2 ^ 64 := by
        rw [henc] at hlen
        exact Nat.lt_of_lt_of_le (payload_length_lt_lenField 1 (encSession s)) hlen
      rw [henc, decode_lenField1 hs_lt] at hdec
      injection hdec with hrec
      rw [← hrec]

/-- If `xs.length` is bounded by `rec.previousSessions.length` for the prost `RecordStructure`
decoded from the loaded `scopeKit` record on `CliPqOrD3RecvDom W i`, then `xs = []`. -/
theorem list_eq_nil_of_loadRec_scopeKit_recordTie {α : Type} {W : PEParams}
    {i : Inputs} {peer : AddrV} {r : SessionRecord (List (BitVec 8))} {xs : List α}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hlr : loadRec scopeKit (runFiles i) (addrValOf peer) = .ok (some r))
    (hTie : ∀ rec, RecordStructure.decode (encodeRecord r) = some rec →
      xs.length ≤ rec.previousSessions.length) :
    xs = [] := by
  obtain ⟨_, _, _, _, _, _, _, _, hdec₀, _⟩ :=
    loadRec_cliPqOrD3RecvDom_scopeKit_some_decode hi hparse hlr
  have hle := hTie _ hdec₀
  simp only [List.length_nil, Nat.le_zero] at hle
  exact List.eq_nil_of_length_eq_zero hle

/-- Raw `sessions.get` variant of `list_eq_nil_of_loadRec_scopeKit_recordTie`. -/
theorem list_eq_nil_of_sessions_get_recordTie {α : Type} {W : PEParams}
    {i : Inputs} {peer : AddrV} {b : BitVec 8} {bs : List (BitVec 8)} {xs : List α}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hget : StoresGhost.opened.sessions.get cliIo.rd (runFiles i) (addressText (addrValOf peer)) =
      .ok (b :: bs))
    (hTie : ∀ rec, RecordStructure.decode (b :: bs) = some rec →
      xs.length ≤ rec.previousSessions.length) :
    xs = [] := by
  obtain ⟨_, _, _, _, _, _, _, _, hdec₀, _⟩ :=
    sessions_get_cliPqOrD3RecvDom_nonempty_decode hi hparse hget
  have hle := hTie _ hdec₀
  simp only [List.length_nil, Nat.le_zero] at hle
  exact List.eq_nil_of_length_eq_zero hle

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record
