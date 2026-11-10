/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SelfKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet

/-!
# Initial Store Invariants and Kit/Model Agreement

Establishes initial store invariants (`CliSessInv`, `CliIdOwnInv`, `CliIdInv`, `CliPkInv`,
`CliSpkInv`, `CliKpkInvFull`) at `StoresGhost.opened` from `Slots.FilesOkPeer` and `DecPkOk₀`,
together with pure store-answer totality, determinism, and `decPkDef` commit agreement lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Session & Identity Initial Store Invariants (`StoresGhost.opened`) -/

/-- Lift `Slots.FilesOkPeer Scope F peer` along `Scope ⊆ Slots.scopeIn` to
`Slots.FilesOkPeer Slots.scopeKit F peer`. -/
theorem filesOkPeer_scopeKit {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal}
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hf : Slots.FilesOkPeer Scope F peer) :
    Slots.FilesOkPeer Slots.scopeKit F peer where
  nameLt := hf.nameLt
  textLt := hf.textLt
  sessPathOk := hf.sessPathOk
  idPathOk := hf.idPathOk
  sessPathLt := hf.sessPathLt
  idPathLt := hf.idPathLt
  sessGet := by
    obtain ⟨bs, hget, hwf⟩ := hf.sessGet
    refine ⟨bs, hget, ?_⟩
    rcases hwf with rfl | ⟨r, rfl, hsc⟩
    · exact .inl rfl
    · exact .inr ⟨r, rfl, Slots.scopeKit_of_scopeIn (hsub r hsc)⟩
  idGet := hf.idGet

private theorem storeDir_len_lt {d : List (BitVec 8)} (hd : d ∈ storeDirs) : d.length < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (storeDirs_ok d hd).2 (by decide)

private theorem mem_storeDirs_identities :
    StoresGhost.opened.identity.peers.path ∈ storeDirs := .head _

private theorem mem_storeDirs_signed :
    StoresGhost.opened.signed.path ∈ storeDirs := .tail _ (.head _)

private theorem mem_storeDirs_kyberOneTime :
    StoresGhost.opened.kyber.oneTime.path ∈ storeDirs := .tail _ (.tail _ (.head _))

private theorem mem_storeDirs_kyberLastResort :
    StoresGhost.opened.kyber.lastResort.path ∈ storeDirs :=
  .tail _ (.tail _ (.tail _ (.head _)))

private theorem mem_storeDirs_oneTime :
    StoresGhost.opened.oneTime.path ∈ storeDirs :=
  .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

private theorem mem_storeDirs_sessions :
    StoresGhost.opened.sessions.path ∈ storeDirs :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

/-- Initial session kit invariant at `Slots.scopeKit` and `cliWrOk` on `StoresGhost.opened.sessions`. -/
theorem cliSessInv_opened_scopeKit {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost}
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hf : Slots.FilesOkPeer Scope F peer.val) :
    CliSessInv cliIo.rd F cliWrOk Slots.scopeKit peer StoresGhost.opened.sessions :=
  ⟨hf.nameLt, hf.textLt, storeDir_len_lt mem_storeDirs_sessions, ⟨hf.sessPathOk, hf.sessPathLt⟩,
    (filesOkPeer_scopeKit hsub hf).sessGet,
    ⟨show (0 : Nat) < 2 ^ 32 by decide, .inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩⟩

/-- Initial self-identity `CliIdOwnInv` on `StoresGhost.opened.identity.own`. -/
theorem cliIdOwnInv_opened {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F peer me pm) :
    CliIdOwnInv cliIo.rd F cliWrOk StoresGhost.opened.identity.own where
  ownPathLt := show (0 : Nat) < 2 ^ 32 by decide
  kpPathOk := cliWrOk_ownFile (.tail _ (.head _))
  regPathOk := cliWrOk_ownFile (.tail _ (.tail _ (.head _)))
  kpSizeOk := hd.keyPairLt

/-! ## 2. Pre-Key Store Name, Path, & Size Guards at `StoresGhost.opened` -/

theorem pkNameOk_opened_oneTime (id : BitVec 32) :
    PkNameOk cliWrOk StoresGhost.opened.oneTime id :=
  ⟨by have := keyName_length id; omega, storeDir_len_lt mem_storeDirs_oneTime,
    cliWrOk_keyName mem_storeDirs_oneTime id⟩

theorem pkNameOk_opened_signed (id : BitVec 32) :
    PkNameOk cliWrOk StoresGhost.opened.signed id :=
  ⟨by have := keyName_length id; omega, storeDir_len_lt mem_storeDirs_signed,
    cliWrOk_keyName mem_storeDirs_signed id⟩

theorem pkNameOk_opened_kyberOneTime (id : BitVec 32) :
    PkNameOk cliWrOk StoresGhost.opened.kyber.oneTime id :=
  ⟨by have := keyName_length id; omega, storeDir_len_lt mem_storeDirs_kyberOneTime,
    cliWrOk_keyName mem_storeDirs_kyberOneTime id⟩

theorem pkNameOk_opened_kyberLastResort (id : BitVec 32) :
    PkNameOk cliWrOk StoresGhost.opened.kyber.lastResort id :=
  ⟨by have := keyName_length id; omega, storeDir_len_lt mem_storeDirs_kyberLastResort,
    cliWrOk_keyName mem_storeDirs_kyberLastResort id⟩

theorem kpkBaseKeysOk_opened (id : BitVec 32) :
    KpkBaseKeysOk cliWrOk StoresGhost.opened.kyber.lastResort id :=
  ⟨by have := baseKeysName_length id; omega, storeDir_len_lt mem_storeDirs_kyberLastResort,
    cliWrOk_baseKeys id⟩

private theorem encodeVarintAux_length_le :
    ∀ (k : Nat) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have := encodeVarintAux_length_le k (v >>> 7)
      omega

private theorem encodeVarint_length_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v

private theorem encodeKey_length_le (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le _

private theorem encodeUint32_3_length_le (tag : Nat) (v : BitVec 32) :
    (RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold RecordCodecs.encodeProto3Uint32Field
  split
  · decide
  · simp only [encodeUint32Field, List.length_append]
    have := encodeKey_length_le tag .varint
    have := encodeVarint_length_le (v.zeroExtend 64)
    omega

private theorem encodeBytes3_length_le (tag : Nat) (v : List (BitVec 8)) :
    (RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold RecordCodecs.encodeProto3BytesField
  split
  · simp
  · simp only [encodeBytesField, List.length_append]
    have := encodeKey_length_le tag .lengthDelimited
    have := encodeVarint_length_le (BitVec.ofNat 64 v.length)
    omega

private theorem encodeFixed64_3_length_le (tag : Nat) (v : BitVec 64) :
    (RecordCodecs.encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold RecordCodecs.encodeProto3Fixed64Field
  split
  · decide
  · simp only [List.length_append]
    have := encodeKey_length_le tag .sixtyFourBit
    have h8 : (RecordCodecs.le64Bytes v).length = 8 := rfl
    omega

theorem oneTimeRecordBytes_length_lt (C : Crypto) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    (oneTimeRecordBytes C id sk).length < 2 ^ 32 := by
  unfold oneTimeRecordBytes RecordCodecs.PreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeUint32_3_length_le 1 id
  have h2 := encodeBytes3_length_le 2 (djbKey (keyPairOf C sk).publicKey.bytes)
  have h3 := encodeBytes3_length_le 3 sk.toList
  have hd : (djbKey (keyPairOf C sk).publicKey.bytes).length = 33 := by
    simp [djbKey]
  have hs : sk.toList.length = 32 := sk.toList_length
  omega

theorem signedRecordBytes_length_lt (C : Crypto) (id : BitVec 32) (k : PqSignedKey) :
    (signedRecordBytes C id k).length < 2 ^ 32 := by
  unfold signedRecordBytes RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeUint32_3_length_le 1 id
  have h2 := encodeBytes3_length_le 2 (djbKey (keyPairOf C k.priv).publicKey.bytes)
  have h3 := encodeBytes3_length_le 3 k.priv.toList
  have h4 := encodeBytes3_length_le 4 k.sig.toList
  have h5 := encodeFixed64_3_length_le 5 k.timestamp
  have hd : (djbKey (keyPairOf C k.priv).publicKey.bytes).length = 33 := by
    simp [djbKey]
  have hp : k.priv.toList.length = 32 := k.priv.toList_length
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

theorem kyberRecordBytes_length_lt (id : BitVec 32) (k : PqKyberKey) :
    (kyberRecordBytes id k).length < 2 ^ 32 := by
  unfold kyberRecordBytes RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeUint32_3_length_le 1 id
  have h2 := encodeBytes3_length_le 2 (kyberKey k.pub)
  have h3 := encodeBytes3_length_le 3 (0x08#8 :: k.sec.toList)
  have h4 := encodeBytes3_length_le 4 k.sig.toList
  have h5 := encodeFixed64_3_length_le 5 k.timestamp
  have hkpub : (kyberKey k.pub).length = 1569 := by
    simp [kyberKey]
  have hksec : (0x08#8 :: k.sec.toList).length = 3169 := by
    simp [k.sec.toList_length]
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

/-! ## 3. Initial Pre-Key Store Invariants (`CliPkInv`, `CliSpkInv`, `CliKpkInvFull`, `CliIdInv`) -/

theorem cliIdInv_opened_peer {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost}
    (hf : Slots.FilesOkPeer Scope F peer.val) :
    CliIdInv cliIo.rd F cliWrOk peer StoresGhost.opened.identity :=
  ⟨hf.nameLt, storeDir_len_lt mem_storeDirs_identities, ⟨hf.idPathOk, hf.idPathLt⟩, hf.idGet,
    ⟨show (0 : Nat) < 2 ^ 32 by decide, .inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩⟩

theorem cliPkInv_opened {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F peer me pm) (pid : BitVec 32) :
    CliPkInv cliIo.rd F cliWrOk pid StoresGhost.opened.oneTime where
  nameOk := pkNameOk_opened_oneTime pid
  sizeOk := by
    intro bs hget
    rcases hd.preKeysWf.oneTime pid bs hget with rfl | ⟨sk, rfl⟩
    · decide
    · exact oneTimeRecordBytes_length_lt W.C pid sk
  oneLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩

theorem cliSpkInv_opened {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F peer me pm) (sid : BitVec 32) :
    CliSpkInv cliIo.rd F cliWrOk sid StoresGhost.opened.signed where
  nameOk := pkNameOk_opened_signed sid
  sizeOk := by
    intro bs hget
    rcases hd.preKeysWf.signed sid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact signedRecordBytes_length_lt W.C sid k

theorem cliKpkInvFull_opened {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F peer me pm)
    (kid ksid : BitVec 32) (kbk : PublicKey) :
    CliKpkInvFull cliIo.rd F cliWrOk kid ksid kbk StoresGhost.opened.kyber where
  markInv := {
    nameOk := pkNameOk_opened_kyberOneTime kid
    baseOk := kpkBaseKeysOk_opened kid
    seenOk := fun bs hget _ _ => hd.baseKeysLt kid bs hget
    oneLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩
    lastLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩
  }
  lastNameOk := pkNameOk_opened_kyberLastResort kid
  oneSizeOk := by
    intro bs hget
    rcases hd.preKeysWf.kyberOneTime kid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact kyberRecordBytes_length_lt kid k
  lastSizeOk := by
    intro bs hget
    rcases hd.preKeysWf.kyberLastResort kid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact kyberRecordBytes_length_lt kid k

/-! ## 4. Commit Write-Path Guards (`StoresWrOk cliWrOk`) & `removePreKey` / Stage P1 Totality -/

theorem storesWrOk_pathB {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal} {ik : IdentityKey} {bs : List (BitVec 8)}
    (hf : Slots.FilesOkPeer Scope F peer) :
    let g := StoresGhost.opened
    let g' : StoresGhost :=
      { g with
        identity := g.identity.saveUpd cliIo.rd F peer ik
        sessions := g.sessions.put (Cli.addressText peer) bs }
    ∀ pw ∈ g'.writes, cliWrOk pw.1 := by
  intro g g'
  refine StoresWrOk.writes ?_
  have h0 := StoresWrOk.opened cliWrOk
  refine ⟨?_, ?_, h0.signed, h0.kyberOneTime, h0.kyberLastResort, h0.oneTime, ?_, h0.pub⟩
  · show DirWrOk cliWrOk (g.identity.saveUpd cliIo.rd F peer ik).own
    rw [saveUpd_own]
    exact h0.own
  · show DirWrOk cliWrOk (g.identity.saveUpd cliIo.rd F peer ik).peers
    exact h0.peers.saveUpd ⟨hf.idPathOk, hf.idPathLt⟩
  · show DirWrOk cliWrOk (g.sessions.put (Cli.addressText peer) bs)
    exact h0.sessions.put ⟨hf.sessPathOk, hf.sessPathLt⟩ bs

theorem storesWrOk_pathA {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal} {ik : IdentityKey}
    {kpkId spkId : BitVec 32} {bk : PublicKey} {opkId : Option (BitVec 32)}
    {bs : List (BitVec 8)}
    (hf : Slots.FilesOkPeer Scope F peer) :
    let g := StoresGhost.opened
    let kyber' := (g.kyber.mark cliIo.rd F kpkId spkId bk).2
    let oneTime' := match opkId with
      | none => g.oneTime
      | some j => (Cli.removePreKey cliIo.rd F g.oneTime j).2
    let g' : StoresGhost :=
      { g with
        identity := g.identity.saveUpd cliIo.rd F peer ik
        kyber := kyber'
        oneTime := oneTime'
        sessions := g.sessions.put (Cli.addressText peer) bs }
    ∀ pw ∈ g'.writes, cliWrOk pw.1 := by
  intro g kyber' oneTime' g'
  refine StoresWrOk.writes ?_
  have h0 := StoresWrOk.opened cliWrOk
  refine ⟨?_, ?_, h0.signed, ?_, ?_, ?_, ?_, h0.pub⟩
  · show DirWrOk cliWrOk (g.identity.saveUpd cliIo.rd F peer ik).own
    rw [saveUpd_own]
    exact h0.own
  · show DirWrOk cliWrOk (g.identity.saveUpd cliIo.rd F peer ik).peers
    exact h0.peers.saveUpd ⟨hf.idPathOk, hf.idPathLt⟩
  · exact h0.kyberOneTime.mark_oneTime (cliWrOk_keyName mem_storeDirs_kyberOneTime kpkId)
  · exact h0.kyberLastResort.mark_lastResort (cliWrOk_baseKeys kpkId)
  · cases opkId with
    | none => exact h0.oneTime
    | some j => exact h0.oneTime.removePreKey (cliWrOk_keyName mem_storeDirs_oneTime j)
  · exact h0.sessions.put ⟨hf.sessPathOk, hf.sessPathLt⟩ bs

/-- Every `cliSessionStoreSpec.loadRel` answer is `.ok _` (`SessLoadAns` on `.ok bs` never errors). -/
theorem cliSess_loadRel_isOk {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {d : DirGhost} {rem : AddrVal}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (h : (cliSessionStoreSpec A b rd F0 pathOk Scope peer s1 s2 s3 s4).loadRel d rem ans) :
    ans.isOk = true := by
  obtain ⟨bs, _, hans⟩ := h
  rcases bs with _ | ⟨x, xs⟩
  · subst hans; rfl
  · obtain ⟨_, rfl, _, _⟩ := hans; rfl

/-- Under `FilesOkPeer`, `StoresGhost.opened.identity.trusted` always returns `.ok b` for some `b`. -/
theorem trusted_ok_of_filesOkPeer {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} (hf : Slots.FilesOkPeer Scope F peer.val)
    (ik : IdentityKey) :
    ∃ b : Bool, StoresGhost.opened.identity.trusted cliIo.rd F peer.val ik = .ok b := by
  have hinv := cliIdInv_opened_peer hf
  obtain ⟨pk?, hpk⟩ := hinv.peer_ok
  unfold IdGhost.trusted
  rw [hpk]
  exact ⟨_, rfl⟩

/-- Under `g.trusted rd F0 rem k =.ok b`, `cliIdStoreSpecFull.trustRel` forces `ans =.ok b`. -/
theorem cliId_trustRel_eq_of_trusted {A : RustAlloc} {b0 : BitVec 64} {rd : ReadRule}
    {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {dir : Direction}
    {b : Bool} (ht : g.trusted rd F0 rem k = .ok b) {ans : Except Unit Bool}
    (hrel : (cliIdStoreSpecFull A b0 rd F0 pathOk peer s1 s2 s3 s4).trustRel g rem k dir ans) :
    ans = .ok b := by
  obtain ⟨t, ht', rfl⟩ := hrel
  rw [ht] at ht'
  injection ht' with htb
  rw [← htb]

/-- Once `getPreKey` has succeeded on `(F, d, j)`, `d.get` cannot be `.error ()`, so
`removePreKey` on `(F, d, j)` always returns `.ok ()` on its first component. -/
theorem removePreKey_fst_ok_of_getPreKey_ok {rd : ReadRule} {F : FsFiles}
    {d : DirGhost} {j : BitVec 32} {r : PreKeyRecord}
    (hget : getPreKey rd F d j = .ok r) :
    (Cli.removePreKey rd F d j).1 = .ok () := by
  rw [getPreKey_eq] at hget
  rw [removePreKey_eq_pkRemoveOf]
  rcases hd : d.get rd F (keyName j) with _ | _ | ⟨b, bs⟩
  · rw [hd] at hget; cases hget
  · rfl
  · rfl

/-- Corollary at kit level: `cliPreKeyStoreSpec.removeRel` cannot produce `.error _` after
`getRel` produced `.ok r`. -/
theorem cliPk_removeRel_not_error_of_getRel_ok {A : RustAlloc} {b : BitVec 64}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {pid : BitVec 32}
    {s1 s2 s3 s4 : Nat} {d : DirGhost} {r : PreKeyRecord}
    (hget : (cliPreKeyStoreSpec A b rd F0 pathOk pid s1 s2 s3 s4).getRel d pid (.ok r))
    (e : CliReadErr) :
    ¬ (cliPreKeyStoreSpec A b rd F0 pathOk pid s1 s2 s3 s4).removeRel d pid (.error e) := by
  have hg : getPreKey rd F0 d pid = .ok r :=
    (cliPk_getRel_ok_iff rd F0 pathOk pid s1 s2 s3 s4 d pid r).mp hget
  have hok := removePreKey_fst_ok_of_getPreKey_ok hg
  intro herr
  change (Cli.removePreKey rd F0 d pid).1 = .error () at herr
  rw [hok] at herr
  cases herr

/-! ## 5. Pure `decPkDef` Branch Agreement Lemmas -/

/-- Under `hinjK : Slots.EncodeInjOn Slots.scopeKit`, `hsub : Scope ⊆ Slots.scopeIn`, and
`hf : Slots.FilesOkPeer Scope F peer`, `Slots.loadRec Slots.scopeKit F peer = Slots.loadRec Scope F peer`. -/
theorem loadRec_scopeKit_eq {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hf : Slots.FilesOkPeer Scope F peer) :
    Slots.loadRec Slots.scopeKit F peer = Slots.loadRec Scope F peer :=
  (Slots.loadRec_of_sub hinjK (fun r h => Slots.scopeKit_of_scopeIn (hsub r h)) hf).symm

theorem decPkDef_of_load_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    (herr : Slots.loadRec Scope F peer = .error ()) :
    decPkDef X W Scope F peer me pm coins = some none := by
  dsimp only [decPkDef]
  rw [herr]

theorem decPkDef_of_trust_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : Option (SessionRecord (List (BitVec 8)))}
    (hload : Slots.loadRec Scope F peer = .ok r)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .error () ∨
              StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok false) :
    decPkDef X W Scope F peer me pm coins = some none := by
  dsimp only [decPkDef]
  rw [hload]
  dsimp only
  rcases htrust with ht | ht <;> rw [ht]

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
