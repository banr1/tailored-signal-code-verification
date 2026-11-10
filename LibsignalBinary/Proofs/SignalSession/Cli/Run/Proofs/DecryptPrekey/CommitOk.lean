/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Pksm
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCommit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# `PksmCanonical`, `PksmTyped`, and Pre-Key `CommitOk` (`DecryptPrekey/CommitOk`)

Discharges the parse-canonicality, domain, and store-commit path-safety obligations for
`Pksm.pksmParse` and `decPkDef`:
1. `pksmCanonical_S0`, `pksmTyped_S0`, `pksmParseAgrees_S0`, and `pksmParse_bytes_typed`.
2. `decPkDef_namedWrites_sub`, `commitOk_pqRecvPrekey_S0`, and `decPkCommitOk_cli`: every store
   write produced on an accepting `decPkDef` call targets one of the five canonical party-directory
   paths (`identityFile`, `sessionFile`, `oneTimeKyberPreKeyFile`, `baseKeysFile`,
   `oneTimePreKeyFile`), satisfying `WriteOk` on `pqRecvInputs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes

/-! ## 1. `PksmCanonical`, `PksmTyped`, `PksmParseAgrees`, and `decPkDomOk_cli` -/

/-- `S.pksmParse = Pksm.pksmParse` satisfies `RunRefine.PksmCanonical S`. -/
theorem pksmCanonical_S0 {S : RunSem} (hS : S.pksmParse = Pksm.pksmParse) :
    RunRefine.PksmCanonical S := by
  intro x hx
  rw [hS, Pksm.pksmParse_bytes x hx]
  rfl

/-- `S.pksmParse = Pksm.pksmParse` satisfies `RunProofs.PksmTyped S`. -/
theorem pksmTyped_S0 {S : RunSem} (hS : S.pksmParse = Pksm.pksmParse) :
    PksmTyped S := by
  intro m pm hm hparse
  exact (RunRefine.pksmParse_bytes_iff (pksmCanonical_S0 hS) m hm pm).mp hparse

/-- `S.pksmParse = Pksm.pksmParse` satisfies `RunRefine.PksmParseAgrees S`. -/
theorem pksmParseAgrees_S0 {S : RunSem} (hS : S.pksmParse = Pksm.pksmParse) :
    RunRefine.PksmParseAgrees S :=
  RunRefine.pksmParseAgrees_of_canonical (pksmCanonical_S0 hS)

/-- Direct inversion of `Pksm.pksmParse m.bytes = some pm` on a typed `PreKeyMessageFields`. -/
theorem pksmParse_bytes_typed {m : PreKeyMessageFields} {pm : PreKeySignalMessage}
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hparse : Pksm.pksmParse m.bytes = some pm) :
    ∃ i : SignalMessage, SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
      pm = pmOfE m i := by
  have h := Pksm.pksmParse_bytes (RunRefine.argsOf m) hm
  change Pksm.pksmParse m.bytes =
    (match SignalMessage.tryFrom protoSignalCodec m.inner with
     | .ok i => some (pmOfE m i)
     | .error _ => none) at h
  rw [h] at hparse
  cases hi : SignalMessage.tryFrom protoSignalCodec m.inner with
  | ok i =>
    rw [hi] at hparse
    exact ⟨i, rfl, (Option.some.inj hparse).symm⟩
  | error _ =>
    rw [hi] at hparse
    cases hparse

/-! ## 2. Write-path classification for `decPkDef` and `CommitOk` on `pqRecvInputs` -/

private theorem kyberMark_writes {F : FsFiles} {kpkId spkId : BitVec 32} {bk : PublicKey}
    {kyber' : KyberGhost}
    (hkm : StoresGhost.opened.kyber.mark cliIo.rd F kpkId spkId bk = (.ok (), kyber')) :
    ∃ w8 w9 : List (String × List (BitVec 8)),
      ((∀ pw ∈ kyber'.oneTime.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
        kyber'.oneTime.writes.map (fun pw => (pathStr pw.1, pw.2)) = w8) ∧
      ((∀ pw ∈ kyber'.lastResort.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
        kyber'.lastResort.writes.map (fun pw => (pathStr pw.1, pw.2)) = w9) ∧
      (∀ pw ∈ w8, pw.1 = oneTimeKyberPreKeyFile kpkId) ∧
      (∀ pw ∈ w9, pw.1 = baseKeysFile kpkId) := by
  unfold KyberGhost.mark at hkm
  cases hot : StoresGhost.opened.kyber.oneTime.get cliIo.rd F (keyName kpkId) with
  | error _ =>
    rw [hot] at hkm; cases hkm
  | ok bs =>
    rw [hot] at hkm
    cases bs with
    | cons _ _ =>
      dsimp only at hkm
      injection hkm with _ hk
      subst hk
      obtain ⟨hkot_str, hkot_asc⟩ := DecPkS0.kyberOneTime_path_eq kpkId
      refine ⟨[(oneTimeKyberPreKeyFile kpkId, [])], [], ⟨?_, ?_⟩,
        ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩, ?_,
        fun _ h => False.elim (List.not_mem_nil h)⟩
      · intro pw hpw bt hbt
        change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
        rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw
        subst hpw; exact hkot_asc bt hbt
      · change ((DirGhost.new _).put _ _).writes.map _ = _
        rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hkot_str]
      · intro pw hpw
        rw [List.mem_singleton] at hpw; subst hpw; rfl
    | nil =>
      dsimp only at hkm
      cases hlr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F (baseKeysName kpkId) with
      | error _ =>
        rw [hlr] at hkm; cases hkm
      | ok seen =>
        rw [hlr] at hkm
        dsimp only at hkm
        split at hkm
        · cases hkm
        · split at hkm
          · cases hkm
          · injection hkm with _ hk
            subst hk
            obtain ⟨hbk_str, hbk_asc⟩ := DecPkS0.baseKeys_path_eq kpkId
            refine ⟨[], [(baseKeysFile kpkId, seen ++ baseKeyEntry spkId bk)],
              ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩, ⟨?_, ?_⟩,
              fun _ h => False.elim (List.not_mem_nil h), ?_⟩
            · intro pw hpw bt hbt
              change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
              rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw
              subst hpw; exact hbk_asc bt hbt
            · change ((DirGhost.new _).put _ _).writes.map _ = _
              rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hbk_str]
            · intro pw hpw
              rw [List.mem_singleton] at hpw; subst hpw; rfl

private theorem oneTimeUpdate_writes (F : FsFiles) (opk : Option (BitVec 32)) :
    let otDir : DirGhost := match opk with
      | none => StoresGhost.opened.oneTime
      | some j => (removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
    ∃ (opkId : BitVec 32) (w7 : List (String × List (BitVec 8))),
      ((∀ pw ∈ otDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
        otDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w7) ∧
      (∀ pw ∈ w7, pw.1 = oneTimePreKeyFile opkId) := by
  cases opk with
  | none =>
    exact ⟨0#32, [], ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩,
      fun _ h => False.elim (List.not_mem_nil h)⟩
  | some j =>
    dsimp only
    unfold removePreKey
    cases hot : StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
    | error _ =>
      dsimp only
      exact ⟨j, [], ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩,
        fun _ h => False.elim (List.not_mem_nil h)⟩
    | ok bs =>
      cases bs with
      | nil =>
        dsimp only
        exact ⟨j, [], ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩,
          fun _ h => False.elim (List.not_mem_nil h)⟩
      | cons _ _ =>
        dsimp only
        obtain ⟨hot_str, hot_asc⟩ := DecPkS0.oneTime_path_eq j
        refine ⟨j, [(oneTimePreKeyFile j, [])], ⟨?_, ?_⟩, ?_⟩
        · intro pw hpw bt hbt
          change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
          rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw
          subst hpw; exact hot_asc bt hbt
        · change ((DirGhost.new _).put _ _).writes.map _ = _
          rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hot_str]
        · intro pw hpw
          rw [List.mem_singleton] at hpw; subst hpw; rfl

/-- Every store write produced on an accepting `decPkDef` call targets one of the five canonical
party-directory file paths (`identityFile`, `sessionFile`, `oneTimeKyberPreKeyFile`, `baseKeysFile`,
or `oneTimePreKeyFile`). -/
theorem decPkDef_namedWrites_sub {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F (RunRefine.addrValE P) me pm coins = some (some (g', pt))) :
    ∃ kpkId opkId : BitVec 32,
      ∀ pw ∈ namedWrites g'.writes,
        pw.1 = identityFile (partyAddressName P) ∨
        pw.1 = sessionFile (partyAddress P) ∨
        pw.1 = oneTimeKyberPreKeyFile kpkId ∨
        pw.1 = baseKeysFile kpkId ∨
        pw.1 = oneTimePreKeyFile opkId := by
  unfold decPkDef at h
  dsimp only at h
  cases hload : Slots.loadRec Scope F (RunRefine.addrValE P) with
  | error _ => rw [hload] at h; cases h
  | ok r =>
    rw [hload] at h
    dsimp only at h
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F (RunRefine.addrValE P)
        pm.identityKey with
    | error _ => rw [htr] at h; cases h
    | ok tb =>
      cases tb with
      | false => rw [htr] at h; cases h
      | true =>
        rw [htr] at h
        dsimp only at h
        have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd F (RunRefine.addrValE P)
            pm.identityKey =
            { StoresGhost.opened.identity with
              peers := StoresGhost.opened.identity.peers.put (RunRefine.addrValE P).name
                pm.identityKey.serialize } := by
          unfold IdGhost.trusted at htr
          unfold IdGhost.saveUpd
          cases hp : StoresGhost.opened.identity.peer cliIo.rd F (RunRefine.addrValE P) with
          | error _ => rw [hp] at htr; cases htr
          | ok _ => rfl
        cases hcur : r.bind (·.currentSession) with
        | some s =>
          rw [hcur] at h
          dsimp only at h
          split at h
          · split at h
            · cases h
            · cases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                  ((pqxdhSessionParams W).expectedAddrs (initParty (RunRefine.addrValE P)))
                  pm.message .preKey (pkRecvCoins coins) s.state with
              | mk res st1 =>
                rw [hdec] at h
                cases res with
                | ok _ =>
                  dsimp only at h
                  injection h with h1
                  injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  refine ⟨0#32, 0#32, fun pw hpw => ?_⟩
                  rw [hsave] at hpw
                  have hw := DecPkS0.namedWrites_of_dirs P pm.identityKey.serialize
                    (Record.encodeRecord
                      { currentSession := some
                          { state := st1, pendingPreKey := none, pendingKyberPreKey := none,
                            localRegistrationId := s.localRegistrationId,
                            remoteRegistrationId := s.remoteRegistrationId,
                            aliceBaseKey := s.aliceBaseKey } })
                    StoresGhost.opened.kyber.oneTime
                    StoresGhost.opened.kyber.lastResort
                    StoresGhost.opened.oneTime
                    (w8 := []) (w9 := []) (w7 := [])
                    ⟨fun _ hm => False.elim (List.not_mem_nil hm), rfl⟩
                    ⟨fun _ hm => False.elim (List.not_mem_nil hm), rfl⟩
                    ⟨fun _ hm => False.elim (List.not_mem_nil hm), rfl⟩
                  have hpw' :
                      pw ∈ [(identityFile (partyAddressName P), pm.identityKey.serialize)] ++
                        ([] : List (String × List (BitVec 8))) ++ [] ++ [] ++
                        [(sessionFile (partyAddress P),
                          Record.encodeRecord
                            { currentSession := some
                                { state := st1, pendingPreKey := none, pendingKyberPreKey := none,
                                  localRegistrationId := s.localRegistrationId,
                                  remoteRegistrationId := s.remoteRegistrationId,
                                  aliceBaseKey := s.aliceBaseKey } })] := by
                    rw [← hw]
                    exact hpw
                  simp only [List.append_nil, List.singleton_append, List.mem_cons,
                    List.not_mem_nil, or_false] at hpw'
                  rcases hpw' with rfl | rfl
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inl rfl)
                | error err =>
                  cases err <;> cases h
          · cases h
        | none =>
          rw [hcur] at h
          dsimp only at h
          cases hpk : pkToE? pm with
          | none => rw [hpk] at h; cases h
          | some m =>
            rw [hpk] at h
            dsimp only at h
            cases hsk : pkStoreKeys F m with
            | none => rw [hsk] at h; cases h
            | some k =>
              rw [hsk] at h
              cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd F with
              | error _ => rw [hkp] at h; cases h
              | ok kp =>
                rw [hkp] at h
                cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
                | error _ => rw [hreg] at h; cases h
                | ok reg =>
                  rw [hreg] at h
                  dsimp only at h
                  cases hrecv : recvPrekeyState X W (initParty (RunRefine.addrValE P))
                      ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
                  | none => rw [hrecv] at h; cases h
                  | some o =>
                    rw [hrecv] at h
                    cases o with
                    | none => cases h
                    | some triple =>
                      rcases triple with ⟨x, gs, _⟩
                      dsimp only at h
                      cases hkm : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId
                          pm.signedPreKeyId pm.baseKey with
                      | mk kres kyber' =>
                        rw [hkm] at h
                        cases kres with
                        | error _ => cases h
                        | ok u =>
                          cases u
                          dsimp only at h
                          injection h with h1
                          injection h1 with h2
                          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                          obtain ⟨w8, w9, hkot, hklr, hw8, hw9⟩ := kyberMark_writes hkm
                          obtain ⟨opkId, w7, hot, hw7⟩ := oneTimeUpdate_writes F pm.preKeyId
                          refine ⟨m.kpkId, opkId, fun pw hpw => ?_⟩
                          rw [hsave] at hpw
                          have hw := DecPkS0.namedWrites_of_dirs P pm.identityKey.serialize
                            (encodeRecordUnderExtras (fun _ => x) gs)
                            kyber'.oneTime kyber'.lastResort _ hkot hklr hot
                          have hpw' :
                              pw ∈ [(identityFile (partyAddressName P), pm.identityKey.serialize)] ++
                                w8 ++ w9 ++ w7 ++
                                [(sessionFile (partyAddress P), encodeRecordUnderExtras (fun _ => x) gs)] := by
                            rw [← hw]
                            exact hpw
                          simp only [List.mem_append, List.mem_singleton, or_assoc] at hpw'
                          rcases hpw' with rfl | h8 | h9 | h7 | rfl
                          · exact Or.inl rfl
                          · exact Or.inr (Or.inr (Or.inl (hw8 pw h8)))
                          · exact Or.inr (Or.inr (Or.inr (Or.inl (hw9 pw h9))))
                          · exact Or.inr (Or.inr (Or.inr (Or.inr (hw7 pw h7))))
                          · exact Or.inr (Or.inl rfl)

private def dummyKyberKey : PqKyberKey where
  pub := List.Vector.replicate 1568 0#8
  sec := List.Vector.replicate 3168 0#8
  sig := List.Vector.replicate 64 0#8
  timestamp := 0#64

private def stWithAllRecvTargets (W : PEParams) (st : PqParty)
    (kpkId opkId : BitVec 32) : PqParty :=
  { st with
    peerId := some (partyIdentityKey .A)
    session := some (E2E.seedRecordExtras .A,
      (pqxdhSessionParams W).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩)
    oneTime := [(opkId, none)]
    kyberOneTime := [(kpkId, none)]
    kyberLastResort := [(kpkId, (dummyKyberKey, []))] }

private theorem writeOk_pqRecvInputs_allTargets (W : PEParams) (st : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256) (kpkId opkId : BitVec 32)
    {p : String}
    (hp : p = identityFile (partyAddressName st.party.other) ∨
          p = sessionFile (partyAddress st.party.other) ∨
          p = oneTimeKyberPreKeyFile kpkId ∨
          p = baseKeysFile kpkId ∨
          p = oneTimePreKeyFile opkId) :
    WriteOk (pqRecvInputs W st c rc) p := by
  have hw := writeOk_pqRecvInputs W st (stWithAllRecvTargets W st kpkId opkId) c rc
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hw (identityFile (partyAddressName st.party.other), (partyIdentityKey .A).serialize)
      (by simp [encodeDir, stWithAllRecvTargets])
  · exact hw (sessionFile (partyAddress st.party.other),
      encodeRecordUnderExtras (fun _ => E2E.seedRecordExtras .A)
        ((pqxdhSessionParams W).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩))
      (by simp [encodeDir, stWithAllRecvTargets])
  · exact hw (oneTimeKyberPreKeyFile kpkId, [])
      (by simp [encodeDir, stWithAllRecvTargets])
  · exact hw (baseKeysFile kpkId, baseKeysBytes [])
      (by simp [encodeDir, stWithAllRecvTargets])
  · exact hw (oneTimePreKeyFile opkId, [])
      (by simp [encodeDir, stWithAllRecvTargets])

/-- Every pre-key `recv` run at `S.decryptPrekey = decPkDef X W Scope` satisfies `CommitOk` on
`pqRecvInputs W st (wirePrekey :: c) rc` for arbitrary wire payload `c`. -/
theorem commitOk_pqRecvPrekey_decPkDef {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hdec : S.decryptPrekey = decPkDef X W Scope)
    (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    CommitOk (pqRecvInputs W st (wirePrekey :: c) rc)
      (MainResult.ofAnswer (runAns S (pqRecvInputs W st (wirePrekey :: c) rc))) := by
  rw [RunRefine.runAns_pqRecvPrekey_eq]
  cases S.pksmParse c with
  | none =>
    dsimp only
    intro _ h; cases h
  | some pm =>
    dsimp only
    rw [hdec]
    cases ha : decPkDef X W Scope (runFiles (pqRecvInputs W st (wirePrekey :: c) rc))
        (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm
        (HMAC.keyToBytes32 rc) with
    | none =>
      trivial
    | some o =>
      cases o with
      | none => intro _ h; cases h
      | some gp =>
        rcases gp with ⟨g', pt⟩
        obtain ⟨kpkId, opkId, hsub⟩ := decPkDef_namedWrites_sub ha
        intro pw hpw
        exact writeOk_pqRecvInputs_allTargets W st (wirePrekey :: c) rc kpkId opkId (hsub pw hpw)

/-- `CommitOk` on the PQXDH pre-key `recv` domain, matching the `decPkCommitOk` field of
`CliPqPrekeyBundle` / `CliPqPrekeyBundleS0`. -/
theorem commitOk_pqRecvPrekey_S0 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (S : RunSem) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hdec : S.decryptPrekey = decPkDef X W Scope)
    (_hpksm : S.pksmParse = Pksm.pksmParse)
    (_hwf : PqxdhPartyInSpecDomain W st)
    (_hm : m.inner.length + 2048 < 2 ^ 32)
    (_hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    CommitOk (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
      (MainResult.ofAnswer (runAns S (pqRecvInputs W st (wirePrekey :: m.bytes) rc))) :=
  commitOk_pqRecvPrekey_decPkDef hdec st m.bytes rc

theorem decPkCommitOk_cli {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (S : RunSem) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hdec : S.decryptPrekey = decPkDef X W Slots.scopeIn)
    (hpksm : S.pksmParse = Pksm.pksmParse)
    (hwf : PqxdhPartyInSpecDomain W st)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    CommitOk (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
      (MainResult.ofAnswer (runAns S (pqRecvInputs W st (wirePrekey :: m.bytes) rc))) :=
  commitOk_pqRecvPrekey_S0 S st m rc hdec hpksm hwf hm hmatch

end CryptoVerification.SignalSession.Cli.RunProofs
