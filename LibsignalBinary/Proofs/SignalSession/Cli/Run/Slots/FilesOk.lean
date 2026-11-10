/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import all Init.Data.String.Defs
import all Init.Data.String.Bootstrap
import all Init.Data.Repr
import all Init.Data.List.SplitOn.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
import LibsignalBinary.Proofs.E2E.Reach.SmSessionCap
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run

/-!
# Store-File Well-Formedness for Wrapper Slots (`filesOk₀` and `RunFilesOk`)

Defines `FilesOkPeer` and `filesOk₀` for `S.filesOk` (`RunFilesOk`), capturing the peer `u32`
bounds, path guards, well-formed session/identity files (`SessFileWf`, `IdFileWf`) needed by
`CliSessInv` and `CliIdInv` at `StoresGhost.opened`, and account distinctness (`DistinctSid`)
between `me` and `peer`, and discharges them on Signal-Message and PQXDH domain inputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## Peer store-file well-formedness (`FilesOkPeer` and `filesOk₀`) -/

/-- Peer bounds, path guards, and loadable well-formed `sessions/<address_text peer>` and
`identities/<peer.name>` files required by `CliSessInv` and `CliIdInv` at `StoresGhost.opened`. -/
structure FilesOkPeer (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) : Prop where
  nameLt : peer.name.length < 2 ^ 32
  textLt : (Cli.addressText peer).length < 2 ^ 32
  sessPathOk : cliIo.pathOk (pathOf (utf8 "sessions") (Cli.addressText peer))
  idPathOk : cliIo.pathOk (pathOf (utf8 "identities") peer.name)
  /-- Path-length bound for `sessions/<address_text peer>` (`< 2^32`). -/
  sessPathLt : (pathOf (utf8 "sessions") (Cli.addressText peer)).length < 2 ^ 32
  /-- Path-length bound for `identities/<peer.name>` (`< 2^32`). -/
  idPathLt : (pathOf (utf8 "identities") peer.name).length < 2 ^ 32
  sessGet : ∃ bs, StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) = .ok bs ∧
    SessFileWf Scope bs
  idGet : ∃ bs, StoresGhost.opened.identity.peers.get cliIo.rd F peer.name = .ok bs ∧ IdFileWf bs

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : Cli.utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [Cli.utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem trUtf8_eq_kutf8 (s : String) :
    LibsignalTripleRatchetRepr.utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [LibsignalTripleRatchetRepr.utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem pathOf_eq (d n : List (BitVec 8)) :
    pathOf d n = if d = [] then n else d ++ kutf8 "/" ++ n := by
  unfold pathOf
  rw [utf8_eq_kutf8]

private theorem addressText_eq (a : AddrVal) :
    Cli.addressText a = a.name ++ kutf8 "." ++ kutf8 (toString a.device.toNat) := by
  unfold Cli.addressText decimalText
  rw [utf8_eq_kutf8, utf8_eq_kutf8]

/-- Derives `CliSessInv` at `StoresGhost.opened.sessions` from `FilesOkPeer`. -/
theorem cliSessInv_opened {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrGhost} (h : FilesOkPeer Scope F peer.val) :
    CliSessInv cliIo.rd F cliIo.pathOk Scope peer StoresGhost.opened.sessions := by
  have hp : StoresGhost.opened.sessions.path.length < 2 ^ 32 := by
    show (Cli.utf8 "sessions").length < 2 ^ 32
    rw [utf8_eq_kutf8]
    exact of_decide_eq_true rfl
  exact ⟨h.nameLt, h.textLt, hp, h.sessPathOk, h.sessGet,
    ⟨of_decide_eq_true rfl, .inl (of_decide_eq_true rfl)⟩⟩

/-- Derives `CliIdInv` at `StoresGhost.opened.identity` from `FilesOkPeer`. -/
theorem cliIdInv_opened {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrGhost} (h : FilesOkPeer Scope F peer.val) :
    CliIdInv cliIo.rd F cliIo.pathOk peer StoresGhost.opened.identity := by
  have hp : StoresGhost.opened.identity.peers.path.length < 2 ^ 32 := by
    show (Cli.utf8 "identities").length < 2 ^ 32
    rw [utf8_eq_kutf8]
    exact of_decide_eq_true rfl
  exact ⟨h.nameLt, hp, h.idPathOk, h.idGet,
    ⟨of_decide_eq_true rfl, .inl (of_decide_eq_true rfl)⟩⟩

/-- Account distinctness: `bs1` and `bs2` do not parse to the same `ServiceId` under `parse`. -/
abbrev DistinctSid (parse : UuidParser) (bs1 bs2 : List (BitVec 8)) : Prop :=
  ∀ v, serviceIdParse parse bs1 = some v → serviceIdParse parse bs2 ≠ some v

/-- Two addresses parse to the same `ServiceId` under `uuidTryParse`. -/
abbrev SameServiceId : AddrVal → AddrVal → Prop :=
  RunProofs.SameServiceId

theorem distinctSid_iff_not_sameServiceId (peer me : AddrVal) :
    DistinctSid uuidTryParse me.name peer.name ↔ ¬ SameServiceId peer me := by
  constructor
  · rintro hd ⟨sid, hp, hm⟩; exact hd sid hm hp
  · intro hns v hm hp; exact hns ⟨v, hp, hm⟩

/-- Store-file well-formedness predicate combining `FilesOkPeer`, `DistinctSid` between `me` and
`peer`, and an auxiliary file invariant `extra`. -/
def filesOk₀ (Scope : SessionRecord (List (BitVec 8)) → Prop) (extra : FsFiles → Prop)
    (F : FsFiles) (peer me : AddrVal) : Prop :=
  FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name ∧ extra F

/-! ## Domain party addresses and `ServiceId` distinctness -/

/-- Session-API `AddrVal` of domain party `P` (`utf8 (partyAddressName P)`, device ID `1`). -/
def partyAddr (P : Party) : AddrVal := ⟨utf8 (partyAddressName P), 1#8⟩

private theorem partyAddr_eq (P : Party) : partyAddr P = ⟨kutf8 (partyAddressName P), 1#8⟩ := by
  unfold partyAddr
  simp only [utf8_eq_kutf8]

theorem partyAddr_peerOk (P : Party) :
    (partyAddr P).name.length < 2 ^ 32 ∧ (Cli.addressText (partyAddr P)).length < 2 ^ 32 ∧
      cliIo.pathOk (pathOf (utf8 "sessions") (Cli.addressText (partyAddr P))) ∧
      cliIo.pathOk (pathOf (utf8 "identities") (partyAddr P).name) ∧
      (pathOf (utf8 "sessions") (Cli.addressText (partyAddr P))).length < 2 ^ 32 ∧
      (pathOf (utf8 "identities") (partyAddr P).name).length < 2 ^ 32 := by
  unfold cliIo
  simp only [partyAddr_eq, addressText_eq, pathOf_eq, utf8_eq_kutf8]
  cases P <;> exact ⟨of_decide_eq_true rfl, of_decide_eq_true rfl,
    ⟨rfl, of_decide_eq_true rfl⟩,
    ⟨rfl, of_decide_eq_true rfl⟩,
    of_decide_eq_true rfl, of_decide_eq_true rfl⟩

private theorem addrParse_party_shape (P : Party) :
    (addrParse uuidTryParse (bytesOfString (partyAddress P).text)).map (fun v => (v.name, v.device)) =
      some (utf8 (partyAddressName P), 1#8) := by
  unfold addrParse serviceIdParse uuidTryParse pniPrefix urnPrefix
  simp only [utf8_eq_kutf8, trUtf8_eq_kutf8]
  cases P <;> exact of_decide_eq_true rfl

private theorem addrParse_party (P : Party) :
    addrParse uuidTryParse (bytesOfString (partyAddress P).text) = some ⟨utf8 (partyAddressName P), 1#8⟩ := by
  have h := addrParse_party_shape P
  cases hv : addrParse uuidTryParse (bytesOfString (partyAddress P).text) with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    injection h with h
    injection h with hn hd
    cases v
    subst hn hd
    rfl

private theorem addrParse_party_textBytes_shape (P : Party) :
    (addrParse uuidTryParse (textBytes (partyAddress P).text)).map (fun v => (v.name, v.device)) =
      some (utf8 (partyAddressName P), 1#8) := by
  unfold addrParse serviceIdParse uuidTryParse pniPrefix urnPrefix textBytes
  simp only [utf8_eq_kutf8, trUtf8_eq_kutf8]
  cases P <;> exact of_decide_eq_true rfl

theorem addrParse_party_textBytes (P : Party) :
    addrParse uuidTryParse (textBytes (partyAddress P).text) = some ⟨utf8 (partyAddressName P), 1#8⟩ := by
  have h := addrParse_party_textBytes_shape P
  cases hv : addrParse uuidTryParse (textBytes (partyAddress P).text) with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    injection h with h
    injection h with hn hd
    cases v
    subst hn hd
    rfl

/-- Distinct domain parties `P` and `P.other` have distinct `ServiceId`s under `uuidTryParse`. -/
theorem distinctSid_party (P : Party) :
    DistinctSid uuidTryParse (partyAddr P).name (partyAddr P.other).name := by
  intro v h1 h2
  have hm1 := congrArg (Option.map fun (b, u) => (b, u.toList)) h1
  have hm2 := congrArg (Option.map fun (b, u) => (b, u.toList)) h2
  rw [← hm1] at hm2
  revert hm2
  unfold serviceIdParse uuidTryParse pniPrefix urnPrefix
  simp only [partyAddr_eq, trUtf8_eq_kutf8]
  cases P <;> exact of_decide_eq_true rfl

theorem not_sameServiceId_party (P : Party) :
    ¬ SameServiceId (partyAddr P.other) (partyAddr P) :=
  (distinctSid_iff_not_sameServiceId (partyAddr P.other) (partyAddr P)).mp (distinctSid_party P)

theorem callPeer_of_cmd (cmd : Cmd) {P : Party} (hP : cmdPeer cmd = partyAddress P) {c : CallV}
    {peer : AddrV} (hc : parseArgs uuidTryParse (cmd.argv.map bytesOfString) = some c)
    (hpeer : callPeer c = some peer) : addrValOf peer = partyAddr P := by
  have hi : bytesOfString "init" = utf8 "init" := by
    simp only [utf8_eq_kutf8]; exact of_decide_eq_true rfl
  have hs : bytesOfString "send" = utf8 "send" := by
    simp only [utf8_eq_kutf8]; exact of_decide_eq_true rfl
  have hr : bytesOfString "recv" = utf8 "recv" := by
    simp only [utf8_eq_kutf8]; exact of_decide_eq_true rfl
  have hk : utf8 "init" ≠ utf8 "keygen" := by
    simp only [utf8_eq_kutf8]; exact of_decide_eq_true rfl
  have hrs : utf8 "recv" ≠ utf8 "send" := by
    simp only [utf8_eq_kutf8]; exact of_decide_eq_true rfl
  have ha := addrParse_party P
  cases cmd with
  | init p b =>
    change p = partyAddress P at hP
    subst hP
    simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hi, hk, ha, Option.map_some,
      ↓reduceIte] at hc
    injection hc with hc
    subst hc
    injection hpeer with hpeer
    subst hpeer
    rfl
  | send p =>
    change p = partyAddress P at hP
    subst hP
    simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hs, ha, Option.map_some,
      ↓reduceIte] at hc
    injection hc with hc
    subst hc
    injection hpeer with hpeer
    subst hpeer
    rfl
  | recv p =>
    change p = partyAddress P at hP
    subst hP
    simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hr, hrs, ha, Option.map_some,
      ↓reduceIte] at hc
    injection hc with hc
    subst hc
    injection hpeer with hpeer
    subst hpeer
    rfl

/-! ## Session and identity file contents on domain inputs -/

/-- Serialized session file bytes of a `PqParty` (`encodeRecordUnderExtras`, or `[]` when absent). -/
def pqSessBytes (st : PqParty) : List (BitVec 8) :=
  match st.session with
  | some (x, g) => encodeRecordUnderExtras (fun _ => x) g
  | none => []

/-- Serialized peer identity-key bytes of a `PqParty` (`k.serialize`, or `[]` when absent). -/
def pqIdBytes (st : PqParty) : List (BitVec 8) :=
  match st.peerId with
  | some k => k.serialize
  | none => []

theorem smSessBytes_le_fileCapBytes (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (E2E.encodeRecord g).length ≤ fileCapBytes :=
  LibsignalBinary.Proofs.E2E.Reach.SmSessionCap.reach_encodeRecord_length_le_fileCapBytes C hg

theorem pqSessBytes_le_fileCapBytes {W : PEParams} {st : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) :
    (pqSessBytes st).length ≤ fileCapBytes := by
  unfold pqSessBytes
  cases hs : st.session with
  | none => simp [fileCapBytes]
  | some xg =>
    rcases xg with ⟨x, g⟩
    obtain ⟨⟨g₀, hR₀, _, hs₀⟩, _⟩ := hwf.1 x g hs
    have heq : encodeRecordUnderExtras (fun _ => x) g₀ = encodeRecordUnderExtras (fun _ => x) g := by
      unfold encodeRecordUnderExtras; rw [hs₀]
    dsimp only
    rw [← heq]
    exact LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.reachPq_encodeRecordX_length_le_fileCapBytes hR₀

private theorem pqIdBytes_le_fileCapBytes (st : PqParty) :
    (pqIdBytes st).length ≤ fileCapBytes := by
  unfold pqIdBytes
  cases st.peerId with
  | none => simp [fileCapBytes]
  | some k => simp [IdentityKey.serialize, PublicKey.serialize, fileCapBytes]

private def lookupLast (l : List (String × List (BitVec 8))) (q : String) :
    Option (List (BitVec 8)) :=
  (l.reverse.find? (fun x => x.1 == q)).map Prod.snd

private theorem lookupLast_append_none {l1 l2 : List (String × List (BitVec 8))} {q : String}
    (h2 : ∀ f ∈ l2, f.1 ≠ q) : lookupLast (l1 ++ l2) q = lookupLast l1 q := by
  unfold lookupLast
  rw [List.reverse_append, List.find?_append]
  have hf : l2.reverse.find? (fun x => x.1 == q) = none := by
    rw [List.find?_eq_none]
    intro x hx hxq
    exact h2 x (List.mem_reverse.mp hx) (beq_iff_eq.mp hxq)
  rw [hf]
  rfl

private theorem lookupLast_append_hit (l : List (String × List (BitVec 8))) (q : String)
    (bs : List (BitVec 8)) : lookupLast (l ++ [(q, bs)]) q = some bs := by
  have hqq : (q == q) = true := beq_iff_eq.mpr rfl
  unfold lookupLast
  rw [List.reverse_append]
  show (((q, bs) :: l.reverse).find? (fun x => x.1 == q)).map Prod.snd = some bs
  rw [List.find?_cons, hqq]
  rfl

private theorem lookupLast_eq_none {l : List (String × List (BitVec 8))} {q : String}
    (h : ∀ f ∈ l, f.1 ≠ q) : lookupLast l q = none := by
  unfold lookupLast
  have hf : l.reverse.find? (fun x => x.1 == q) = none := by
    rw [List.find?_eq_none]
    intro x hx hxq
    exact h x (List.mem_reverse.mp hx) (beq_iff_eq.mp hxq)
  rw [hf]
  rfl

private theorem pathStr_session (P : Party) :
    pathStr (pathOf (utf8 "sessions") (Cli.addressText (partyAddr P))) = sessionFile (partyAddress P) := by
  simp only [partyAddr_eq, addressText_eq, pathOf_eq, utf8_eq_kutf8]
  cases P <;> exact of_decide_eq_true rfl

private theorem pathStr_identity (P : Party) :
    pathStr (pathOf (utf8 "identities") (partyAddr P).name) = identityFile (partyAddressName P) := by
  simp only [partyAddr_eq, pathOf_eq, utf8_eq_kutf8]
  cases P <;> exact of_decide_eq_true rfl

private theorem ancestors_session (P : Party) :
    ancestors (sessionFile (partyAddress P)) = ["sessions"] := by
  cases P <;> exact of_decide_eq_true rfl

private theorem ancestors_identity (P : Party) :
    ancestors (identityFile (partyAddressName P)) = ["identities"] := by
  cases P <;> exact of_decide_eq_true rfl

private def SafeFile (s : String) : Prop :=
  normalizePath s ≠ ["sessions"] ∧ normalizePath s ≠ ["identities"] ∧
  (∀ P : Party,
    (normalizePath s = normalizePath (sessionFile (partyAddress P)) → s = sessionFile (partyAddress P)) ∧
    (normalizePath s = normalizePath (identityFile (partyAddressName P)) → s = identityFile (partyAddressName P)) ∧
    (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath s)).dropLast,
      pref ≠ normalizePath (sessionFile (partyAddress P)) ∧
      pref ≠ normalizePath (identityFile (partyAddressName P))))

private theorem foldl_setEntry_dir_preserve {k : FsPath} :
    ∀ (l : List FsPath) (fs : FsState),
    fs.entries k = some .dir →
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k = some .dir
  | [], _, h => h
  | _ :: ps, fs, h => by
    refine foldl_setEntry_dir_preserve ps _ ?_
    unfold FsState.setEntry
    dsimp only
    split
    · rfl
    · exact h

private theorem foldl_setEntry_dir_miss {k : FsPath} :
    ∀ (l : List FsPath) (fs : FsState),
    (∀ p ∈ l, p ≠ k) →
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k = fs.entries k
  | [], _, _ => rfl
  | p :: ps, fs, h => by
    rw [List.foldl_cons, foldl_setEntry_dir_miss ps _ (fun x hx => h x (List.Mem.tail _ hx))]
    have hne : (k == p) = false := beq_false_of_ne (fun he => h p (List.Mem.head _) he.symm)
    unfold FsState.setEntry
    dsimp only
    rw [hne]
    rfl

private def initDirsFold (dirs : List String) : FsState :=
  dirs.foldl (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
    (fun acc pref => acc.setEntry pref (some .dir)) fs) {}

private def initFilesFold (files : List (String × List (BitVec 8))) (base : FsState) : FsState :=
  files.foldl (fun fs (p, bs) =>
    let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs
    withAnc.setFile p (some (.file bs))) base

private theorem initFilesFold_dir {k : FsPath} :
    ∀ (files : List (String × List (BitVec 8))) (base : FsState),
    base.entries k = some .dir →
    (∀ f ∈ files, normalizePath f.1 ≠ k) →
    (initFilesFold files base).entries k = some .dir
  | [], _, hb, _ => hb
  | (p, bs) :: rest, base, hb, hnf => by
    refine initFilesFold_dir rest _ ?_ (fun f hf => hnf f (List.Mem.tail _ hf))
    have hanc : (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) base).entries k = some .dir :=
      foldl_setEntry_dir_preserve _ base hb
    have hne : (k == normalizePath p) = false :=
      beq_false_of_ne (fun he => hnf (p, bs) (List.Mem.head _) he.symm)
    unfold FsState.setFile FsState.setEntry
    dsimp only
    rw [hne]
    exact hanc

private theorem initFilesFold_lookup {q : String} :
    ∀ (files : List (String × List (BitVec 8))) (base : FsState),
    (∀ f ∈ files,
      (normalizePath f.1 = normalizePath q → f.1 = q) ∧
      (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast, pref ≠ normalizePath q)) →
    (initFilesFold files base).entries (normalizePath q) =
      ((files.reverse.find? (fun x => x.1 == q)).map (fun x => FsEntry.file x.2)).or
        (base.entries (normalizePath q))
  | [], _, _ => rfl
  | (p, bs) :: rest, base, hf => by
    obtain ⟨hp_eq, hp_anc⟩ := hf (p, bs) (List.Mem.head _)
    have hstep := initFilesFold_lookup rest
      ((((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) base).setFile p (some (.file bs)))
      (fun f hmem => hf f (List.Mem.tail _ hmem))
    have hanc : (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) base).entries (normalizePath q) =
        base.entries (normalizePath q) :=
      foldl_setEntry_dir_miss _ base hp_anc
    have hset : ((((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) base).setFile p (some (.file bs))).entries
        (normalizePath q) =
        if p == q then some (.file bs) else base.entries (normalizePath q) := by
      generalize (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) base) = w at hanc ⊢
      unfold FsState.setFile FsState.setEntry
      dsimp only
      rw [hanc]
      by_cases hpq : p = q
      · subst hpq; simp
      · have hne : (normalizePath q == normalizePath p) = false :=
          beq_false_of_ne (fun he => hpq (hp_eq he.symm))
        have hne' : (p == q) = false := beq_false_of_ne hpq
        simp [hne, hne']
    have hcons : initFilesFold ((p, bs) :: rest) base =
        initFilesFold rest
          ((((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
            (fun acc pref => acc.setEntry pref (some .dir)) base).setFile p (some (.file bs))) :=
      rfl
    rw [hcons, hstep, hset, List.reverse_cons, List.find?_append]
    cases hfind : rest.reverse.find? (fun x => x.1 == q) with
    | some x => simp
    | none =>
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      cases p == q <;> rfl

private theorem initFsState_files_nonstdio (inp : ProcessInputs) (x : String)
    (hne : (normalizePath x).isEmpty = false) :
    (initFsState inp).files x =
      (initFilesFold inp.files (initDirsFold inp.dirs)).entries (normalizePath x) := by
  unfold initFsState initFilesFold initDirsFold FsState.files FsState.getEntry
  simp only [hne, Bool.false_eq_true, ↓reduceIte, FsState.setFd]

private theorem dirGet_opened_runFiles {i : Inputs} {d : DirGhost} {name : List (BitVec 8)}
    {dir q : String} {bs : List (BitVec 8)}
    (hc : d.changed = []) (hp : pathStr (pathOf d.path name) = q)
    (hq_case : (dir = "sessions" ∧ ∃ P : Party, q = sessionFile (partyAddress P)) ∨
               (dir = "identities" ∧ ∃ P : Party, q = identityFile (partyAddressName P)))
    (hdirs : i.dirs = partyDirs ∨ i.dirs = partyDirs ++ [bundleDir])
    (hsafe : ∀ f ∈ i.files, SafeFile f.1)
    (hlk : (lookupLast i.files q).getD [] = bs)
    (hcap : bs.length ≤ fileCapBytes) :
    d.get cliIo.rd (runFiles i) name = .ok bs := by
  have hfacts :
      ancestors q = [dir] ∧
      normalizePath dir = [dir] ∧
      (normalizePath dir).isEmpty = false ∧
      (initDirsFold i.dirs).entries [dir] = some .dir ∧
      (normalizePath q).isEmpty = false ∧
      (initDirsFold i.dirs).entries (normalizePath q) = none ∧
      (∀ f ∈ i.files, normalizePath f.1 ≠ [dir]) ∧
      (∀ f ∈ i.files,
        (normalizePath f.1 = normalizePath q → f.1 = q) ∧
        (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast,
          pref ≠ normalizePath q)) := by
    rcases hq_case with ⟨rfl, P, rfl⟩ | ⟨rfl, P, rfl⟩
    · refine ⟨ancestors_session P, of_decide_eq_true rfl, of_decide_eq_true rfl,
        by rcases hdirs with h | h <;> rw [h] <;> exact of_decide_eq_true rfl,
        by cases P <;> exact of_decide_eq_true rfl,
        by rcases hdirs with h | h <;> rw [h] <;> cases P <;> exact of_decide_eq_true rfl,
        fun f hf => (hsafe f hf).1,
        fun f hf => ⟨((hsafe f hf).2.2 P).1, fun pref hp => (((hsafe f hf).2.2 P).2.2 pref hp).1⟩⟩
    · refine ⟨ancestors_identity P, of_decide_eq_true rfl, of_decide_eq_true rfl,
        by rcases hdirs with h | h <;> rw [h] <;> exact of_decide_eq_true rfl,
        by cases P <;> exact of_decide_eq_true rfl,
        by rcases hdirs with h | h <;> rw [h] <;> cases P <;> exact of_decide_eq_true rfl,
        fun f hf => (hsafe f hf).2.1,
        fun f hf => ⟨((hsafe f hf).2.2 P).2.1, fun pref hp => (((hsafe f hf).2.2 P).2.2 pref hp).2⟩⟩
  obtain ⟨hanc, hd_norm, hd_ne, hd_base, hq_ne, hq_base, hd_nf, hq_files⟩ := hfacts
  have hdir_val : runFiles i dir = some .dir := by
    unfold runFiles
    rw [initFsState_files_nonstdio (cliInputs i) dir hd_ne]
    show (initFilesFold i.files (initDirsFold i.dirs)).entries (normalizePath dir) = some .dir
    rw [hd_norm]
    exact initFilesFold_dir i.files (initDirsFold i.dirs) hd_base hd_nf
  have hb : blockingAncestorF (runFiles i) q = none := by
    unfold blockingAncestorF
    rw [hanc, Option.map_eq_none_iff, List.find?_eq_none]
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    rw [hdir_val]
    exact Bool.noConfusion
  unfold DirGhost.get
  rw [hc]
  show cliRd (runFiles i) (pathOf d.path name) = .ok bs
  unfold cliRd readViewF
  rw [hp, hb]
  dsimp only
  have hq_val : runFiles i q =
      ((i.files.reverse.find? (fun x => x.1 == q)).map (fun x => FsEntry.file x.2)) := by
    unfold runFiles
    rw [initFsState_files_nonstdio (cliInputs i) q hq_ne]
    show (initFilesFold i.files (initDirsFold i.dirs)).entries (normalizePath q) = _
    rw [initFilesFold_lookup i.files (initDirsFold i.dirs) hq_files, hq_base, Option.or_none]
  rw [hq_val]
  unfold lookupLast at hlk
  cases hf : i.files.reverse.find? (fun x => x.1 == q) with
  | none =>
    rw [hf] at hlk
    simp only [Option.map, Option.getD] at hlk ⊢
    subst hlk
    simp
  | some pb =>
    rw [hf] at hlk
    simp only [Option.map, Option.getD] at hlk ⊢
    subst hlk
    simp [hcap]

private def IsSessOrId (q : String) : Prop :=
  q = "sessions" ∨ q = "identities" ∨
    (∃ P : Party, q = sessionFile (partyAddress P)) ∨ (∃ P : Party, q = identityFile (partyAddressName P))

private theorem ne_of_toList_prefix {s q : String} {p rest : List Char}
    (hs : s.toList = p ++ rest) (hp : 2 ≤ p.length) (h : p.take 2 ≠ q.toList.take 2) :
    s ≠ q := by
  intro heq
  apply h
  rw [← heq, hs, List.take_append_of_le_length hp]

private theorem ne_of_isSessOrId_prefix {s : String} {p rest : List Char}
    (hs : s.toList = p ++ rest) (hp : 2 ≤ p.length)
    (h1 : p.take 2 ≠ "sessions".toList.take 2)
    (h2 : p.take 2 ≠ "identities".toList.take 2)
    (h3 : ∀ P : Party, p.take 2 ≠ (sessionFile (partyAddress P)).toList.take 2)
    (h4 : ∀ P : Party, p.take 2 ≠ (identityFile (partyAddressName P)).toList.take 2) :
    ∀ {q : String}, IsSessOrId q → s ≠ q := by
  rintro q (rfl | rfl | ⟨P, rfl⟩ | ⟨P, rfl⟩)
  · exact ne_of_toList_prefix hs hp h1
  · exact ne_of_toList_prefix hs hp h2
  · exact ne_of_toList_prefix hs hp (h3 P)
  · exact ne_of_toList_prefix hs hp (h4 P)

private theorem ne_of_isSessOrId_lit {s : String}
    (h1 : s ≠ "sessions") (h2 : s ≠ "identities")
    (h3 : ∀ P : Party, s ≠ sessionFile (partyAddress P))
    (h4 : ∀ P : Party, s ≠ identityFile (partyAddressName P)) :
    ∀ {q : String}, IsSessOrId q → s ≠ q := by
  rintro q (rfl | rfl | ⟨P, rfl⟩ | ⟨P, rfl⟩)
  · exact h1
  · exact h2
  · exact h3 P
  · exact h4 P

private theorem signedPreKeyFile_ne (id : BitVec 32) {q : String} (hq : IsSessOrId q) :
    signedPreKeyFile id ≠ q :=
  ne_of_isSessOrId_prefix String.toList_append (of_decide_eq_true rfl)
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem oneTimePreKeyFile_ne (id : BitVec 32) {q : String} (hq : IsSessOrId q) :
    oneTimePreKeyFile id ≠ q :=
  ne_of_isSessOrId_prefix String.toList_append (of_decide_eq_true rfl)
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem oneTimeKyberPreKeyFile_ne (id : BitVec 32) {q : String} (hq : IsSessOrId q) :
    oneTimeKyberPreKeyFile id ≠ q :=
  ne_of_isSessOrId_prefix String.toList_append (of_decide_eq_true rfl)
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem lastResortKyberPreKeyFile_ne (id : BitVec 32) {q : String} (hq : IsSessOrId q) :
    lastResortKyberPreKeyFile id ≠ q :=
  ne_of_isSessOrId_prefix String.toList_append (of_decide_eq_true rfl)
    (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem baseKeysFile_ne (id : BitVec 32) {q : String} (hq : IsSessOrId q) :
    baseKeysFile id ≠ q :=
  ne_of_isSessOrId_prefix
    (by unfold baseKeysFile; rw [String.toList_append, String.toList_append, List.append_assoc])
    (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem coinsFile_ne {q : String} (hq : IsSessOrId q) : coinsFile ≠ q :=
  ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem addressFile_ne {q : String} (hq : IsSessOrId q) : addressFile ≠ q :=
  ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem identityKeyPairFile_ne {q : String} (hq : IsSessOrId q) : identityKeyPairFile ≠ q :=
  ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem registrationIdFile_ne {q : String} (hq : IsSessOrId q) : registrationIdFile ≠ q :=
  ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl)
    (fun P => by cases P <;> exact of_decide_eq_true rfl) hq

private theorem sessionFile_ne_dir (P : Party) :
    sessionFile (partyAddress P) ≠ "sessions" ∧ sessionFile (partyAddress P) ≠ "identities" := by
  cases P <;> exact ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩

private theorem identityFile_ne_dir (P : Party) :
    identityFile (partyAddressName P) ≠ "sessions" ∧ identityFile (partyAddressName P) ≠ "identities" := by
  cases P <;> exact ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩

private theorem identity_ne_session (P1 P2 : Party) :
    identityFile (partyAddressName P1) ≠ sessionFile (partyAddress P2) := by
  cases P1 <;> cases P2 <;> exact of_decide_eq_true rfl

private theorem bundleFiles_ne (b : PublicBundle) {q : String} (hq : IsSessOrId q) :
    ∀ f ∈ b.files bundleDir, f.1 ≠ q := by
  intro f hf
  unfold PublicBundle.files bundleDir at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
        (fun P => by cases P <;> exact of_decide_eq_true rfl)
        (fun P => by cases P <;> exact of_decide_eq_true rfl) hq
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
          (fun P => by cases P <;> exact of_decide_eq_true rfl)
          (fun P => by cases P <;> exact of_decide_eq_true rfl) hq
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
            (fun P => by cases P <;> exact of_decide_eq_true rfl)
            (fun P => by cases P <;> exact of_decide_eq_true rfl) hq
        · rcases List.mem_singleton.mp hf with rfl
          exact ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
            (fun P => by cases P <;> exact of_decide_eq_true rfl)
            (fun P => by cases P <;> exact of_decide_eq_true rfl) hq
  · split at hf
    · rcases List.mem_singleton.mp hf with rfl
      exact ne_of_isSessOrId_lit (of_decide_eq_true rfl) (of_decide_eq_true rfl)
        (fun P => by cases P <;> exact of_decide_eq_true rfl)
        (fun P => by cases P <;> exact of_decide_eq_true rfl) hq
    · cases hf

private theorem safeFile_of_decide {s : String}
    (h1 : decide (normalizePath s ≠ ["sessions"]) = true)
    (h2 : decide (normalizePath s ≠ ["identities"]) = true)
    (h3 : ∀ P : Party,
      decide ((normalizePath s = normalizePath (sessionFile (partyAddress P)) → s = sessionFile (partyAddress P)) ∧
        (normalizePath s = normalizePath (identityFile (partyAddressName P)) → s = identityFile (partyAddressName P)) ∧
        (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath s)).dropLast,
          pref ≠ normalizePath (sessionFile (partyAddress P)) ∧
          pref ≠ normalizePath (identityFile (partyAddressName P)))) = true) :
    SafeFile s :=
  ⟨of_decide_eq_true h1, of_decide_eq_true h2, fun P => of_decide_eq_true (h3 P)⟩

private theorem splitSlash_go_prefix :
    ∀ (cs1 cur cs2 : List Char), '/' ∉ cs1 →
      splitSlash.go cur (cs1 ++ '/' :: cs2) =
        String.ofList (cur.reverse ++ cs1) :: splitSlash.go [] cs2
  | [], cur, cs2, _ => by simp [splitSlash.go]
  | c :: cs, cur, cs2, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.Mem.head _)
    have hcs : '/' ∉ cs := fun hm => h (List.Mem.tail _ hm)
    have hstep : splitSlash.go cur (c :: (cs ++ '/' :: cs2)) =
        splitSlash.go (c :: cur) (cs ++ '/' :: cs2) := by
      conv => lhs; unfold splitSlash.go
      split
      · contradiction
      · rename_i _ _ heq
        injection heq with h1 _
        exact absurd h1 hc
      · rename_i _ _ _ _ heq
        injection heq with h1 h2
        subst h1 h2
        rfl
    rw [List.cons_append, hstep, splitSlash_go_prefix cs (c :: cur) cs2 hcs]
    simp [List.reverse_cons, List.append_assoc]

private theorem mem_of_mem_dropLast {α : Type} {x : α} :
    ∀ {l : List α}, x ∈ l.dropLast → x ∈ l
  | [], h => nomatch h
  | [_], h => nomatch h
  | _ :: _ :: _, h => by
    simp only [List.dropLast] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.Mem.head _
    · exact List.Mem.tail _ (mem_of_mem_dropLast h)

private theorem nonEmptyPrefixes_head {d : String} :
    ∀ (tail : FsPath) (pref : FsPath),
      pref ∈ FsPath.nonEmptyPrefixes (d :: tail) → ∃ rest, pref = d :: rest := by
  intro tail pref hmem
  simp only [FsPath.nonEmptyPrefixes, List.mem_cons, List.mem_map] at hmem
  rcases hmem with rfl | ⟨p, _, rfl⟩
  · exact ⟨[], rfl⟩
  · exact ⟨p, rfl⟩

private theorem safeFile_of_slash_prefix {s d : String} {rest : List Char}
    (hs : s.toList = d.toList ++ ('/' :: rest))
    (hnoslash : decide ('/' ∉ d.toList) = true)
    (hd_rt : String.ofList d.toList = d)
    (hd_ok : (!d.isEmpty && d != ".") = true)
    (h1 : decide (d ≠ "sessions") = true)
    (h2 : decide (d ≠ "identities") = true) :
    SafeFile s := by
  have ⟨tail, hnorm⟩ : ∃ tail, normalizePath s = d :: tail := by
    refine ⟨(splitSlash.go [] rest).filter (fun seg => !seg.isEmpty && seg != "."), ?_⟩
    unfold normalizePath splitSlash
    rw [hs, splitSlash_go_prefix d.toList [] rest (of_decide_eq_true hnoslash)]
    simp [hd_rt, hd_ok]
  have hd1 : d ≠ "sessions" := of_decide_eq_true h1
  have hd2 : d ≠ "identities" := of_decide_eq_true h2
  have hsess : ∀ P : Party, ∃ t, normalizePath (sessionFile (partyAddress P)) = "sessions" :: t := by
    intro P; cases P <;> exact ⟨_, rfl⟩
  have hid : ∀ P : Party, ∃ t, normalizePath (identityFile (partyAddressName P)) = "identities" :: t := by
    intro P; cases P <;> exact ⟨_, rfl⟩
  refine ⟨by rw [hnorm]; intro h; injection h with h; exact hd1 h,
          by rw [hnorm]; intro h; injection h with h; exact hd2 h, fun P => ?_⟩
  obtain ⟨ts, hts⟩ := hsess P
  obtain ⟨ti, hti⟩ := hid P
  refine ⟨by rw [hnorm, hts]; intro h; injection h with h; exact absurd h hd1,
          by rw [hnorm, hti]; intro h; injection h with h; exact absurd h hd2,
          fun pref hpref => ?_⟩
  rw [hnorm] at hpref
  obtain ⟨r, rfl⟩ := nonEmptyPrefixes_head tail pref (mem_of_mem_dropLast hpref)
  exact ⟨by rw [hts]; intro h; injection h with h; exact hd1 h,
         by rw [hti]; intro h; injection h with h; exact hd2 h⟩

private theorem signedPreKeyFile_safe (id : BitVec 32) : SafeFile (signedPreKeyFile id) :=
  safeFile_of_slash_prefix (d := "signed-pre-keys")
    (by unfold signedPreKeyFile; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl

private theorem oneTimePreKeyFile_safe (id : BitVec 32) : SafeFile (oneTimePreKeyFile id) :=
  safeFile_of_slash_prefix (d := "one-time-pre-keys")
    (by unfold oneTimePreKeyFile; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl

private theorem oneTimeKyberPreKeyFile_safe (id : BitVec 32) :
    SafeFile (oneTimeKyberPreKeyFile id) :=
  safeFile_of_slash_prefix (d := "one-time-kyber-pre-keys")
    (by unfold oneTimeKyberPreKeyFile; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl

private theorem lastResortKyberPreKeyFile_safe (id : BitVec 32) :
    SafeFile (lastResortKyberPreKeyFile id) :=
  safeFile_of_slash_prefix (d := "last-resort-kyber-pre-keys")
    (by unfold lastResortKyberPreKeyFile; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl

private theorem baseKeysFile_safe (id : BitVec 32) : SafeFile (baseKeysFile id) :=
  safeFile_of_slash_prefix (d := "last-resort-kyber-pre-keys")
    (by unfold baseKeysFile; rw [String.toList_append, String.toList_append, List.append_assoc]; rfl)
    rfl rfl rfl rfl rfl

private theorem coinsFile_safe : SafeFile coinsFile :=
  safeFile_of_decide rfl rfl (fun P => by cases P <;> rfl)

private theorem addressFile_safe : SafeFile addressFile :=
  safeFile_of_decide rfl rfl (fun P => by cases P <;> rfl)

private theorem identityKeyPairFile_safe : SafeFile identityKeyPairFile :=
  safeFile_of_decide rfl rfl (fun P => by cases P <;> rfl)

private theorem registrationIdFile_safe : SafeFile registrationIdFile :=
  safeFile_of_decide rfl rfl (fun P => by cases P <;> rfl)

private theorem sessionFile_safe (P0 : Party) : SafeFile (sessionFile (partyAddress P0)) := by
  cases P0 <;> exact safeFile_of_decide rfl rfl (fun P => by cases P <;> rfl)

private theorem identityFile_safe (P0 : Party) : SafeFile (identityFile (partyAddressName P0)) := by
  cases P0 <;> exact safeFile_of_decide rfl rfl (fun P => by cases P <;> rfl)

private theorem bundleFiles_safe (b : PublicBundle) :
    ∀ f ∈ b.files bundleDir, SafeFile f.1 := by
  intro f hf
  unfold PublicBundle.files bundleDir at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact safeFile_of_slash_prefix (d := "bundle")
        (by dsimp only; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact safeFile_of_slash_prefix (d := "bundle")
          (by dsimp only; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact safeFile_of_slash_prefix (d := "bundle")
            (by dsimp only; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl
        · rcases List.mem_singleton.mp hf with rfl
          exact safeFile_of_slash_prefix (d := "bundle")
            (by dsimp only; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl
  · split at hf
    · rcases List.mem_singleton.mp hf with rfl
      exact safeFile_of_slash_prefix (d := "bundle")
        (by dsimp only; rw [String.toList_append]; rfl) rfl rfl rfl rfl rfl
    · cases hf

private theorem smFiles_safe (g : GhostState Bytes) (coins : List (BitVec 8)) :
    ∀ f ∈ dirOfE g.party (encodeRecord g) ++ [(coinsFile, coins)], SafeFile f.1 := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact addressFile_safe
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact identityFile_safe g.party.other
      · rcases List.mem_singleton.mp hf with rfl
        exact sessionFile_safe g.party.other
  · rcases List.mem_singleton.mp hf with rfl
    exact coinsFile_safe

theorem smSessGet (g : GhostState Bytes) (cmd : Cmd) (coins stdin : List (BitVec 8))
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    StoresGhost.opened.sessions.get cliIo.rd (runFiles (smInputs g cmd coins stdin))
        (Cli.addressText (partyAddr g.party.other)) = .ok (E2E.encodeRecord g) := by
  refine dirGet_opened_runFiles rfl (pathStr_session g.party.other)
    (.inl ⟨rfl, g.party.other, rfl⟩) (.inl rfl) (smFiles_safe g coins) ?_ hcap
  show (lookupLast (dirOfE g.party (encodeRecord g) ++ [(coinsFile, coins)])
      (sessionFile (partyAddress g.party.other))).getD [] = E2E.encodeRecord g
  rw [lookupLast_append_none (fun f hf => by
      rcases List.mem_singleton.mp hf with rfl
      exact coinsFile_ne (.inr (.inr (.inl ⟨g.party.other, rfl⟩))))]
  have heq : dirOfE g.party (encodeRecord g) =
      [(addressFile, textBytes (partyAddress g.party).text),
        (identityFile (partyAddressName g.party.other), (partyIdentityKey g.party.other).serialize)] ++
        [(sessionFile (partyAddress g.party.other), encodeRecord g)] := rfl
  rw [heq, lookupLast_append_hit]
  rfl

theorem smIdGet (g : GhostState Bytes) (cmd : Cmd) (coins stdin : List (BitVec 8)) :
    StoresGhost.opened.identity.peers.get cliIo.rd (runFiles (smInputs g cmd coins stdin))
        (partyAddr g.party.other).name = .ok (partyIdentityKey g.party.other).serialize := by
  refine dirGet_opened_runFiles rfl (pathStr_identity g.party.other)
    (.inr ⟨rfl, g.party.other, rfl⟩) (.inl rfl) (smFiles_safe g coins) ?_
    (by simp [IdentityKey.serialize, PublicKey.serialize, fileCapBytes])
  show (lookupLast (dirOfE g.party (encodeRecord g) ++ [(coinsFile, coins)])
      (identityFile (partyAddressName g.party.other))).getD [] = (partyIdentityKey g.party.other).serialize
  have heq : dirOfE g.party (encodeRecord g) ++ [(coinsFile, coins)] =
      ([(addressFile, textBytes (partyAddress g.party).text)] ++
        [(identityFile (partyAddressName g.party.other), (partyIdentityKey g.party.other).serialize)]) ++
        [(sessionFile (partyAddress g.party.other), encodeRecord g), (coinsFile, coins)] := rfl
  rw [heq, lookupLast_append_none (fun f hf => by
      rcases List.mem_cons.mp hf with rfl | hf
      · exact (identity_ne_session g.party.other g.party.other).symm
      · rcases List.mem_singleton.mp hf with rfl
        exact coinsFile_ne (.inr (.inr (.inr ⟨g.party.other, rfl⟩)))),
    lookupLast_append_hit]
  rfl

private def pqOwnHdr (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  [(addressFile, textBytes (partyAddress st.party).text),
   (identityKeyPairFile, RecordCodecs.IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩),
   (registrationIdFile, SignalSession.le32 st.me.regId)]

private def pqIdPart (st : PqParty) : List (String × List (BitVec 8)) :=
  match st.peerId with
  | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
  | none => []

private def pqSessPart (st : PqParty) : List (String × List (BitVec 8)) :=
  match st.session with
  | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
  | none => []

private def pqPkTail (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)) ++
  st.oneTime.map (fun (i, k) =>
    (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) =>
    (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten

private theorem encodeDir_eq_parts (W : PEParams) (st : PqParty) :
    encodeDir W st = pqOwnHdr W st ++ pqIdPart st ++ pqSessPart st ++ pqPkTail W st := by
  unfold encodeDir pqOwnHdr pqIdPart pqSessPart pqPkTail
  simp only [List.append_assoc]
  congr 1

private theorem pqOwnHdr_ne (W : PEParams) (st : PqParty) {q : String} (hq : IsSessOrId q) :
    ∀ f ∈ pqOwnHdr W st, f.1 ≠ q := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact addressFile_ne hq
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact identityKeyPairFile_ne hq
    · rcases List.mem_singleton.mp hf with rfl
      exact registrationIdFile_ne hq

private theorem pqPkTail_ne (W : PEParams) (st : PqParty) {q : String} (hq : IsSessOrId q) :
    ∀ f ∈ pqPkTail W st, f.1 ≠ q := by
  intro f hf
  unfold pqPkTail at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hf
        exact signedPreKeyFile_ne i hq
      · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hf
        exact oneTimePreKeyFile_ne i hq
    · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hf
      exact oneTimeKyberPreKeyFile_ne i hq
  · obtain ⟨l, hl, hfl⟩ := List.mem_flatten.mp hf
    obtain ⟨⟨i, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_cons.mp hfl with rfl | hfl
    · exact lastResortKyberPreKeyFile_ne i hq
    · rcases List.mem_singleton.mp hfl with rfl
      exact baseKeysFile_ne i hq

private theorem pqOwnHdr_safe (W : PEParams) (st : PqParty) :
    ∀ f ∈ pqOwnHdr W st, SafeFile f.1 := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact addressFile_safe
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact identityKeyPairFile_safe
    · rcases List.mem_singleton.mp hf with rfl
      exact registrationIdFile_safe

private theorem pqPkTail_safe (W : PEParams) (st : PqParty) :
    ∀ f ∈ pqPkTail W st, SafeFile f.1 := by
  intro f hf
  unfold pqPkTail at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hf
        exact signedPreKeyFile_safe i
      · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hf
        exact oneTimePreKeyFile_safe i
    · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hf
      exact oneTimeKyberPreKeyFile_safe i
  · obtain ⟨l, hl, hfl⟩ := List.mem_flatten.mp hf
    obtain ⟨⟨i, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_cons.mp hfl with rfl | hfl
    · exact lastResortKyberPreKeyFile_safe i
    · rcases List.mem_singleton.mp hfl with rfl
      exact baseKeysFile_safe i

private theorem pqFiles_safe (W : PEParams) (st : PqParty)
    (extra : List (String × List (BitVec 8)))
    (hextra : ∀ f ∈ extra, SafeFile f.1)
    (coins : List (BitVec 8)) :
    ∀ f ∈ encodeDir W st ++ extra ++ [(coinsFile, coins)], SafeFile f.1 := by
  intro f hf
  rw [encodeDir_eq_parts] at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · rcases List.mem_append.mp hf with hf | hf
          · exact pqOwnHdr_safe W st f hf
          · unfold pqIdPart at hf; split at hf
            · rcases List.mem_singleton.mp hf with rfl; exact identityFile_safe st.party.other
            · cases hf
        · unfold pqSessPart at hf; split at hf
          · rcases List.mem_singleton.mp hf with rfl; exact sessionFile_safe st.party.other
          · cases hf
      · exact pqPkTail_safe W st f hf
    · exact hextra f hf
  · rcases List.mem_singleton.mp hf with rfl
    exact coinsFile_safe

private theorem pqLookup_sess (W : PEParams) (st : PqParty)
    (extra : List (String × List (BitVec 8)))
    (hextra : ∀ f ∈ extra, ∀ {q : String}, IsSessOrId q → f.1 ≠ q)
    (coins : List (BitVec 8)) :
    (lookupLast (encodeDir W st ++ extra ++ [(coinsFile, coins)])
      (sessionFile (partyAddress st.party.other))).getD [] = pqSessBytes st := by
  have hq : IsSessOrId (sessionFile (partyAddress st.party.other)) :=
    .inr (.inr (.inl ⟨st.party.other, rfl⟩))
  have hassoc : encodeDir W st ++ extra ++ [(coinsFile, coins)] =
      (pqOwnHdr W st ++ pqIdPart st ++ pqSessPart st) ++
        (pqPkTail W st ++ extra ++ [(coinsFile, coins)]) := by
    rw [encodeDir_eq_parts]
    simp only [List.append_assoc]
  rw [hassoc, lookupLast_append_none (fun f hf => by
    rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · exact pqPkTail_ne W st hq f hf
      · exact hextra f hf hq
    · rcases List.mem_singleton.mp hf with rfl
      exact coinsFile_ne hq)]
  unfold pqSessPart pqSessBytes
  cases st.session with
  | some xg =>
    rcases xg with ⟨x, g⟩
    rw [lookupLast_append_hit]
    rfl
  | none =>
    rw [List.append_nil, lookupLast_eq_none (fun f hf => by
      rcases List.mem_append.mp hf with hf | hf
      · exact pqOwnHdr_ne W st hq f hf
      · unfold pqIdPart at hf
        split at hf
        · rcases List.mem_singleton.mp hf with rfl
          exact identity_ne_session st.party.other st.party.other
        · cases hf)]
    rfl

private theorem pqLookup_id (W : PEParams) (st : PqParty)
    (extra : List (String × List (BitVec 8)))
    (hextra : ∀ f ∈ extra, ∀ {q : String}, IsSessOrId q → f.1 ≠ q)
    (coins : List (BitVec 8)) :
    (lookupLast (encodeDir W st ++ extra ++ [(coinsFile, coins)])
      (identityFile (partyAddressName st.party.other))).getD [] = pqIdBytes st := by
  have hq : IsSessOrId (identityFile (partyAddressName st.party.other)) :=
    .inr (.inr (.inr ⟨st.party.other, rfl⟩))
  have hassoc : encodeDir W st ++ extra ++ [(coinsFile, coins)] =
      (pqOwnHdr W st ++ pqIdPart st) ++
        (pqSessPart st ++ pqPkTail W st ++ extra ++ [(coinsFile, coins)]) := by
    rw [encodeDir_eq_parts]
    simp only [List.append_assoc]
  rw [hassoc, lookupLast_append_none (fun f hf => by
    rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · unfold pqSessPart at hf
          split at hf
          · rcases List.mem_singleton.mp hf with rfl
            exact (identity_ne_session st.party.other st.party.other).symm
          · cases hf
        · exact pqPkTail_ne W st hq f hf
      · exact hextra f hf hq
    · rcases List.mem_singleton.mp hf with rfl
      exact coinsFile_ne hq)]
  unfold pqIdPart pqIdBytes
  cases st.peerId with
  | some k =>
    rw [lookupLast_append_hit]
    rfl
  | none =>
    rw [List.append_nil, lookupLast_eq_none (pqOwnHdr_ne W st hq)]
    rfl

theorem pqSessGet_init (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen)
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    StoresGhost.opened.sessions.get cliIo.rd (runFiles (pqInitInputs W st b t))
        (Cli.addressText (partyAddr st.party.other)) = .ok (pqSessBytes st) := by
  exact dirGet_opened_runFiles rfl (pathStr_session st.party.other)
    (.inl ⟨rfl, st.party.other, rfl⟩) (.inr rfl)
    (pqFiles_safe W st _ (bundleFiles_safe (publicBundleOf b)) _)
    (pqLookup_sess W st _ (fun f hf _ hq => bundleFiles_ne (publicBundleOf b) hq f hf) _) hcap

theorem pqSessGet_send (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64)
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    StoresGhost.opened.sessions.get cliIo.rd (runFiles (pqSendInputs W st m r))
        (Cli.addressText (partyAddr st.party.other)) = .ok (pqSessBytes st) := by
  exact dirGet_opened_runFiles rfl (pathStr_session st.party.other)
    (.inl ⟨rfl, st.party.other, rfl⟩) (.inl rfl)
    (pqFiles_safe W st [] (fun _ hf => nomatch hf) _)
    (pqLookup_sess W st [] (fun _ hf => nomatch hf) _) hcap

theorem pqSessGet_recv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    StoresGhost.opened.sessions.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
        (Cli.addressText (partyAddr st.party.other)) = .ok (pqSessBytes st) := by
  exact dirGet_opened_runFiles rfl (pathStr_session st.party.other)
    (.inl ⟨rfl, st.party.other, rfl⟩) (.inl rfl)
    (pqFiles_safe W st [] (fun _ hf => nomatch hf) _)
    (pqLookup_sess W st [] (fun _ hf => nomatch hf) _) hcap

theorem pqIdGet_init (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    StoresGhost.opened.identity.peers.get cliIo.rd (runFiles (pqInitInputs W st b t))
        (partyAddr st.party.other).name = .ok (pqIdBytes st) := by
  exact dirGet_opened_runFiles rfl (pathStr_identity st.party.other)
    (.inr ⟨rfl, st.party.other, rfl⟩) (.inr rfl)
    (pqFiles_safe W st _ (bundleFiles_safe (publicBundleOf b)) _)
    (pqLookup_id W st _ (fun f hf _ hq => bundleFiles_ne (publicBundleOf b) hq f hf) _)
    (pqIdBytes_le_fileCapBytes st)

theorem pqIdGet_send (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    StoresGhost.opened.identity.peers.get cliIo.rd (runFiles (pqSendInputs W st m r))
        (partyAddr st.party.other).name = .ok (pqIdBytes st) := by
  exact dirGet_opened_runFiles rfl (pathStr_identity st.party.other)
    (.inr ⟨rfl, st.party.other, rfl⟩) (.inl rfl)
    (pqFiles_safe W st [] (fun _ hf => nomatch hf) _)
    (pqLookup_id W st [] (fun _ hf => nomatch hf) _)
    (pqIdBytes_le_fileCapBytes st)

theorem pqIdGet_recv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    StoresGhost.opened.identity.peers.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
        (partyAddr st.party.other).name = .ok (pqIdBytes st) := by
  exact dirGet_opened_runFiles rfl (pathStr_identity st.party.other)
    (.inr ⟨rfl, st.party.other, rfl⟩) (.inl rfl)
    (pqFiles_safe W st [] (fun _ hf => nomatch hf) _)
    (pqLookup_id W st [] (fun _ hf => nomatch hf) _)
    (pqIdBytes_le_fileCapBytes st)

/-! ## `FilesOkPeer` on domain inputs -/

theorem filesOkPeer_sm {Scope : SessionRecord (List (BitVec 8)) → Prop} (g : GhostState Bytes)
    (cmd : Cmd) (coins stdin : List (BitVec 8))
    (hS : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    FilesOkPeer Scope (runFiles (smInputs g cmd coins stdin)) (partyAddr g.party.other) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := partyAddr_peerOk g.party.other
  exact ⟨h1, h2, h3, h4, h5, h6,
    ⟨_, smSessGet g cmd coins stdin hcap, .inr ⟨_, (E2E.Reach.encodeRecord_eq_toRecord g).symm, hS⟩⟩,
    ⟨_, smIdGet g cmd coins stdin, .inr ⟨partyIdentityKey g.party.other, rfl⟩⟩⟩

theorem filesOkPeer_smSend {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (g : GhostState Bytes) (m : List (BitVec 8))
    (hS : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    FilesOkPeer Scope (runFiles (smSendInputs g m)) (partyAddr g.party.other) := by
  exact filesOkPeer_sm g (.send (partyAddress g.party.other)) [] m hS hcap

theorem filesOkPeer_smRecv {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256)
    (hS : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    FilesOkPeer Scope (runFiles (smRecvInputs g c rc)) (partyAddr g.party.other) := by
  exact filesOkPeer_sm g (.recv (partyAddress g.party.other)) (HMAC.keyToBytes32 rc)
    (msgTypeWhisper :: c) hS hcap

private theorem pqSessBytes_wf {Scope : SessionRecord (List (BitVec 8)) → Prop} (st : PqParty)
    (hS : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g)) :
    SessFileWf Scope (pqSessBytes st) := by
  unfold pqSessBytes
  cases hs : st.session with
  | none => exact .inl rfl
  | some xg =>
    rcases xg with ⟨x, g⟩
    exact .inr ⟨_, (E2E.RecordX.encodeRecordX_eq_toRecord (fun _ => x) g).symm, hS x g hs⟩

private theorem pqIdBytes_wf (st : PqParty) : IdFileWf (pqIdBytes st) := by
  unfold pqIdBytes
  cases st.peerId with
  | none => exact .inl rfl
  | some k => exact .inr ⟨k, rfl⟩

theorem filesOkPeer_pqInit {Scope : SessionRecord (List (BitVec 8)) → Prop} (W : PEParams)
    (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hS : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    FilesOkPeer Scope (runFiles (pqInitInputs W st b t)) (partyAddr st.party.other) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := partyAddr_peerOk st.party.other
  exact ⟨h1, h2, h3, h4, h5, h6,
    ⟨_, pqSessGet_init W st b t hcap, pqSessBytes_wf st hS⟩,
    ⟨_, pqIdGet_init W st b t, pqIdBytes_wf st⟩⟩

theorem filesOkPeer_pqSend {Scope : SessionRecord (List (BitVec 8)) → Prop} (W : PEParams)
    (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64)
    (hS : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    FilesOkPeer Scope (runFiles (pqSendInputs W st m r)) (partyAddr st.party.other) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := partyAddr_peerOk st.party.other
  exact ⟨h1, h2, h3, h4, h5, h6,
    ⟨_, pqSessGet_send W st m r hcap, pqSessBytes_wf st hS⟩,
    ⟨_, pqIdGet_send W st m r, pqIdBytes_wf st⟩⟩

theorem filesOkPeer_pqRecv {Scope : SessionRecord (List (BitVec 8)) → Prop} (W : PEParams)
    (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hS : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    FilesOkPeer Scope (runFiles (pqRecvInputs W st c rc)) (partyAddr st.party.other) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := partyAddr_peerOk st.party.other
  exact ⟨h1, h2, h3, h4, h5, h6,
    ⟨_, pqSessGet_recv W st c rc hcap, pqSessBytes_wf st hS⟩,
    ⟨_, pqIdGet_recv W st c rc, pqIdBytes_wf st⟩⟩

/-! ## Bridge to `RunFilesOk` -/

/-- Reduces `RunFilesOk S i` on a domain command `cmd` to `partyAddress P` with local `address` file
`partyAddress P_me` to `S.filesOk (runFiles i) (partyAddr P) (partyAddr P_me)`. -/
theorem runFilesOk_of_peer {S : RunSem} {i : Inputs} (cmd : Cmd) {P P_me : Party}
    (hP : cmdPeer cmd = partyAddress P) (hargv : i.argv = cmd.argv)
    (hown : StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") =
      .ok (textBytes (partyAddress P_me).text))
    (hok : S.filesOk (runFiles i) (partyAddr P) (partyAddr P_me)) : RunFilesOk S i := by
  intro c peer ownB meV hc hp hget hm
  rw [hargv] at hc
  rw [hown] at hget
  injection hget with hget
  subst hget
  rw [addrParse_party_textBytes P_me] at hm
  injection hm with hm
  subst hm
  rw [callPeer_of_cmd cmd hP hc hp]
  exact hok

end CryptoVerification.SignalSession.Cli.Slots
