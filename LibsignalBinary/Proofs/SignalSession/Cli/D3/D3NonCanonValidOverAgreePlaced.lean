/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverAuxPlaced
public import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidMatchAuxPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCommit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeKeys
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# `CommitOk`, `DecPkOkOverD3`, and Model Agreement for Non-Canonical Overwrite `recv`

Proves `CommitOk` for `decPkOverDef`, `DecPkOkOverD3` on non-matching sessions, and
`OutcomeMatchesModelExceptPath ∧ D3NoMatchSessionFile` agreement for `runAns` on arbitrary
wire payloads `body` satisfying `Pksm.pksmParse body = some pm` and `pkToE? pm = some m`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.RecordX
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. `CommitOk` for `decPkOverDef` on Arbitrary Wire Payloads -/

private theorem kyberMark_writes_over {F : FsFiles} {kpkId spkId : BitVec 32} {bk : PublicKey}
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
  cases hkot : StoresGhost.opened.kyber.oneTime.get cliIo.rd F (keyName kpkId) with
  | error _ => rw [hkot] at hkm; cases hkm
  | ok bs =>
    rw [hkot] at hkm
    cases bs with
    | cons _ _ =>
      dsimp only at hkm
      injection hkm with _ hk; subst hk
      obtain ⟨hkot_str, hkot_asc⟩ := DecPkS0.kyberOneTime_path_eq kpkId
      refine ⟨[(oneTimeKyberPreKeyFile kpkId, [])], [],
        ⟨?_, ?_⟩, ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩,
        ?_, fun _ h => False.elim (List.not_mem_nil h)⟩
      · intro pw hpw bt hbt
        change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
        rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw
        subst hpw; exact hkot_asc bt hbt
      · change ((DirGhost.new _).put _ _).writes.map _ = _
        rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hkot_str]
      · intro pw hpw; rw [List.mem_singleton] at hpw; subst hpw; rfl
    | nil =>
      dsimp only at hkm
      cases hlr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F (baseKeysName kpkId) with
      | error _ => rw [hlr] at hkm; cases hkm
      | ok seen =>
        rw [hlr] at hkm; dsimp only at hkm
        split at hkm
        · cases hkm
        · split at hkm
          · cases hkm
          · injection hkm with _ hk; subst hk
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
            · intro pw hpw; rw [List.mem_singleton] at hpw; subst hpw; rfl

private theorem oneTimeUpdate_writes_over (F : FsFiles) (opk : Option (BitVec 32)) :
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
    dsimp only; unfold removePreKey
    cases hot : StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
    | error _ =>
      exact ⟨j, [], ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩,
        fun _ h => False.elim (List.not_mem_nil h)⟩
    | ok bs =>
      cases bs with
      | nil =>
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
        · intro pw hpw; rw [List.mem_singleton] at hpw; subst hpw; rfl

theorem decPkOverDef_namedWrites_sub {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkOverDef X W Scope F (RunRefine.addrValE P) me pm coins = some (some (g', pt))) :
    ∃ kpkId opkId : BitVec 32,
      ∀ pw ∈ namedWrites g'.writes,
        pw.1 = identityFile (partyAddressName P) ∨
        pw.1 = sessionFile (partyAddress P) ∨
        pw.1 = oneTimeKyberPreKeyFile kpkId ∨
        pw.1 = baseKeysFile kpkId ∨
        pw.1 = oneTimePreKeyFile opkId := by
  unfold decPkOverDef at h
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
        | none =>
          rw [hcur] at h
          exact decPkDef_namedWrites_sub h
        | some s =>
          rw [hcur] at h
          dsimp only at h
          by_cases hm_s : SessMatchesPm s pm
          · rw [ite_eq_left hm_s] at h
            exact decPkDef_namedWrites_sub h
          · rw [ite_eq_right hm_s] at h
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
                        rcases triple with ⟨_x, gs, _⟩
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
                            obtain ⟨w8, w9, hkot, hklr, hw8, hw9⟩ := kyberMark_writes_over hkm
                            obtain ⟨opkId, w7, hot, hw7⟩ := oneTimeUpdate_writes_over F pm.preKeyId
                            refine ⟨m.kpkId, opkId, fun pw hpw => ?_⟩
                            rw [hsave] at hpw
                            let ses' : Session (List (BitVec 8)) :=
                              { state := gs.session
                                pendingPreKey := none
                                pendingKyberPreKey := none
                                localRegistrationId := reg
                                remoteRegistrationId := m.regId
                                aliceBaseKey := djbKey m.baseKey }
                            let enc := E2E.Record.encSession (Over.clearPending s)
                            have hw := DecPkS0.namedWrites_of_dirs P pm.identityKey.serialize
                              (Over.encodeRecordPrev1 ses' enc)
                              kyber'.oneTime kyber'.lastResort _ hkot hklr hot
                            have hpw' :
                                pw ∈ [(identityFile (partyAddressName P), pm.identityKey.serialize)] ++
                                  w8 ++ w9 ++ w7 ++
                                  [(sessionFile (partyAddress P), Over.encodeRecordPrev1 ses' enc)] := by
                              rw [← hw]
                              exact hpw
                            simp only [List.mem_append, List.mem_singleton, or_assoc] at hpw'
                            rcases hpw' with rfl | h8 | h9 | h7 | rfl
                            · exact Or.inl rfl
                            · exact Or.inr (Or.inr (Or.inl (hw8 pw h8)))
                            · exact Or.inr (Or.inr (Or.inr (Or.inl (hw9 pw h9))))
                            · exact Or.inr (Or.inr (Or.inr (Or.inr (hw7 pw h7))))
                            · exact Or.inr (Or.inl rfl)

private def dummyKyberKeyOver : PqKyberKey where
  pub := List.Vector.replicate 1568 0#8
  sec := List.Vector.replicate 3168 0#8
  sig := List.Vector.replicate 64 0#8
  timestamp := 0#64

private def stWithAllRecvTargetsOver (W : PEParams) (st : PqParty)
    (kpkId opkId : BitVec 32) : PqParty :=
  { st with
    peerId := some (partyIdentityKey .A)
    session := some (E2E.seedRecordExtras .A,
      (pqxdhSessionParams W).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩)
    oneTime := [(opkId, none)]
    kyberOneTime := [(kpkId, none)]
    kyberLastResort := [(kpkId, (dummyKyberKeyOver, []))] }

private theorem writeOk_pqRecvInputs_allTargetsOver (W : PEParams) (st : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256) (kpkId opkId : BitVec 32)
    {p : String}
    (hp : p = identityFile (partyAddressName st.party.other) ∨
          p = sessionFile (partyAddress st.party.other) ∨
          p = oneTimeKyberPreKeyFile kpkId ∨
          p = baseKeysFile kpkId ∨
          p = oneTimePreKeyFile opkId) :
    WriteOk (pqRecvInputs W st c rc) p := by
  have hw := writeOk_pqRecvInputs W st (stWithAllRecvTargetsOver W st kpkId opkId) c rc
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hw (identityFile (partyAddressName st.party.other), (partyIdentityKey .A).serialize)
      (by simp [encodeDir, stWithAllRecvTargetsOver])
  · exact hw (sessionFile (partyAddress st.party.other),
      encodeRecordUnderExtras (fun _ => E2E.seedRecordExtras .A)
        ((pqxdhSessionParams W).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩))
      (by simp [encodeDir, stWithAllRecvTargetsOver])
  · exact hw (oneTimeKyberPreKeyFile kpkId, [])
      (by simp [encodeDir, stWithAllRecvTargetsOver])
  · exact hw (baseKeysFile kpkId, baseKeysBytes [])
      (by simp [encodeDir, stWithAllRecvTargetsOver])
  · exact hw (oneTimePreKeyFile opkId, [])
      (by simp [encodeDir, stWithAllRecvTargetsOver])

/-- Every pre-key `recv` run at `S.decryptPrekey = decPkOverDef X W Scope` satisfies `CommitOk` on
`pqRecvInputs W st (wirePrekey :: c) rc` for arbitrary wire payload `c`. -/
theorem commitOk_pqRecvPrekey_decPkOverDef {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hdec : S.decryptPrekey = decPkOverDef X W Scope)
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
    cases ha : decPkOverDef X W Scope (runFiles (pqRecvInputs W st (wirePrekey :: c) rc))
        (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm
        (HMAC.keyToBytes32 rc) with
    | none =>
      trivial
    | some o =>
      cases o with
      | none => intro _ h; cases h
      | some gp =>
        rcases gp with ⟨g', pt⟩
        obtain ⟨kpkId, opkId, hsub⟩ := decPkOverDef_namedWrites_sub ha
        intro pw hpw
        exact writeOk_pqRecvInputs_allTargetsOver W st (wirePrekey :: c) rc kpkId opkId (hsub pw hpw)

/-! ## 2. `DecPkOkOverD3` & `decPkOkOverD3_pqRecv` -/

/-- Domain predicate on `(F, peer, me, pm)` for `decPkOverDef` when the peer holds a non-matching
session in `Scope`: combines `DecPkOkD3 W (fun _ => False) F peer me pm` (giving `pkToE? pm = some m`,
inner `SignalMessage.tryFrom` witness, and `DecPkOk₀` at `fun _ => False`) with the loaded non-matching
session witness in `Scope`. -/
def DecPkOkOverD3 (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  DecPkOkD3 W (fun _ => False) F peer me pm ∧
  ∃ r s, Slots.loadRec Scope F peer = .ok (some r) ∧
    r.currentSession = some s ∧
    ¬ SessMatchesPm s pm

theorem not_sessMatchesPm_toRecord_of_not_pqSessionMatches
    (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (hIn : Slots.scopeIn (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hpk : pkToE? pm = some m)
    (hnot : ¬ PqSessionMatches x g m) :
    ∀ s, (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g).currentSession = some s →
      ¬ SessMatchesPm s pm := by
  intro s hcur hmatch
  have hmatch0 : SessMatchesPm s (pmOfE m pm.message) :=
    (sessMatchesPm_pmOfE_iff hpk s).mpr hmatch
  dsimp only [E2E.Record.toRecord, E2E.RecordX.extrasOf, E2E.RecordX.toSessionExtras] at hcur
  injection hcur with hs_eq
  subst hs_eq
  rcases hIn with ⟨⟨_, _, hRep⟩, _⟩
  obtain ⟨hRep1, _, _, _⟩ := hRep _ rfl
  dsimp only [SessMatchesPm, SessionState.version] at hmatch0 hRep1
  obtain ⟨hver, habk⟩ := hmatch0
  have hver4 : (pmOfE m pm.message).messageVersion.zeroExtend 32 = 4#32 := rfl
  have hbk_djb : (pmOfE m pm.message).baseKey.serialize = djbKey m.baseKey := rfl
  rw [hver4] at hver
  rw [hbk_djb] at habk
  apply hnot
  refine ⟨habk, ?_⟩
  by_cases hv0 : g.session.sessionVersion = 0
  · simp [hv0] at hver
  · simp only [hv0, ↓reduceIte] at hver
    have hnat := congrArg BitVec.toNat hver
    simp only [BitVec.toNat_ofNat] at hnat
    omega

/-- `DecPkOkOverD3` holds on `pqRecvInputs W st (wirePrekey :: body) rc` whenever `PqxdhPartyInSpecDomain W st`,
`st.session = some (x, g)`, `¬ PqSessionMatches x g m`, `Pksm.pksmParse body = some pm`,
`pkToE? pm = some m`, and `m.inner.length + 2048 < 2 ^ 32`. -/
theorem decPkOkOverD3_pqRecv (W : PEParams) (st : PqParty)
    (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st)
    (hsess : st.session = some (x, g))
    (hnot : ¬ PqSessionMatches x g m)
    (hparse : Pksm.pksmParse body = some pm)
    (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    DecPkOkOverD3 W Slots.scopeIn
      (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm := by
  have hd3 := decPkOkD3_pqRecv_false W st body pm m rc hwf hparse hpk hm
  have hload := DecPkS0.loadRec_pqRecv_eq encodeInjOn_scopeIn_placed (ratchetScopeCoversPq_scopeIn_placed W)
    st (wirePrekey :: body) rc hwf
  rw [hsess] at hload
  dsimp only [Option.map_some] at hload
  have hIn : Slots.scopeIn (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) :=
    ratchetScopeCoversPq_scopeIn_placed W st x g hwf hsess
  refine ⟨hd3, E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g, _, hload, rfl,
    not_sessMatchesPm_toRecord_of_not_pqSessionMatches x g hIn hpk hnot _ rfl⟩

/-! ## 3. `filesOf_append_singleton_ne` & `OutcomeMatchesModelExceptPath` Agreement -/

/-- Overwriting the very last `(p0, _)` entry in `filesOf` leaves every path `q` with
`Arm64.normalizePath q ≠ Arm64.normalizePath p0` unchanged. -/
theorem filesOf_append_singleton_ne (L : List (String × List (BitVec 8)))
    (p0 : String) (b1 b2 : List (BitVec 8)) {q : String}
    (hne : Arm64.normalizePath q ≠ Arm64.normalizePath p0) :
    filesOf (L ++ [(p0, b1)]) q = filesOf (L ++ [(p0, b2)]) q := by
  unfold filesOf fsView
  split
  · rfl
  · rename_i hnot
    unfold Arm64.FsState.files Arm64.FsState.getEntry
    cases hemp : (Arm64.normalizePath q).isEmpty
    · rw [initFsState_entries { files := L ++ [(p0, b1)] } (Arm64.normalizePath q) hnot,
        initFsState_entries { files := L ++ [(p0, b2)] } (Arm64.normalizePath q) hnot]
      simp [filesFold, Arm64.FsState.setFile, Arm64.FsState.setEntry, hne]
    · rfl

private theorem filesOf_namedWrites_swap_session_ne
    (F0 : List (String × List (BitVec 8))) (P : Party)
    (idBytes sess1 sess2 : List (BitVec 8))
    (kotDir klrDir otDir : DirGhost)
    {w8 w9 w7 : List (String × List (BitVec 8))}
    (hkot : (∀ pw ∈ kotDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
      kotDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w8)
    (hklr : (∀ pw ∈ klrDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
      klrDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w9)
    (hot : (∀ pw ∈ otDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
      otDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w7)
    {q : String}
    (hne : Arm64.normalizePath q ≠ Arm64.normalizePath (sessionFile (partyAddress P))) :
    filesOf (F0 ++ namedWrites ({ StoresGhost.opened with
      identity := { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put (RunRefine.addrValE P).name idBytes }
      kyber := { oneTime := kotDir, lastResort := klrDir }
      oneTime := otDir
      sessions := StoresGhost.opened.sessions.put
        (Cli.addressText (RunRefine.addrValE P)) sess1 }).writes) q =
    filesOf (F0 ++ namedWrites ({ StoresGhost.opened with
      identity := { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put (RunRefine.addrValE P).name idBytes }
      kyber := { oneTime := kotDir, lastResort := klrDir }
      oneTime := otDir
      sessions := StoresGhost.opened.sessions.put
        (Cli.addressText (RunRefine.addrValE P)) sess2 }).writes) q := by
  have hw1 := DecPkS0.namedWrites_of_dirs P idBytes sess1 kotDir klrDir otDir hkot hklr hot
  have hw2 := DecPkS0.namedWrites_of_dirs P idBytes sess2 kotDir klrDir otDir hkot hklr hot
  rw [hw1, hw2]
  simp only [← List.append_assoc]
  exact filesOf_append_singleton_ne _ (sessionFile (partyAddress P)) sess1 sess2 hne

private theorem markKyberUsed_session_none (st : PqParty) (m : PreKeyMessageFields) :
    markKyberUsed { st with session := none } m =
      (markKyberUsed st m).map (fun st1 => { st1 with session := none }) := by
  unfold markKyberUsed
  dsimp only
  cases List.lookup m.kpkId st.kyberOneTime with
  | some opt =>
    cases opt <;> dsimp only
    · cases List.lookup m.kpkId st.kyberLastResort with
      | none => rfl
      | some p =>
        rcases p with ⟨k, seen⟩
        dsimp only
        by_cases hmem : (m.spkId, m.baseKey) ∈ seen
        · simp [hmem]
        · by_cases hcap : fileCapBytes < 37 * seen.length <;> simp [hmem, hcap]
    · rfl
  | none =>
    dsimp only
    cases List.lookup m.kpkId st.kyberLastResort with
    | none => rfl
    | some p =>
      rcases p with ⟨k, seen⟩
      dsimp only
      by_cases hmem : (m.spkId, m.baseKey) ∈ seen
      · simp [hmem]
      · by_cases hcap : fileCapBytes < 37 * seen.length <;> simp [hmem, hcap]

private theorem removeOpk_session_none_overwrite (st1 : PqParty) (m : PreKeyMessageFields)
    (idA : IdentityKey) (x : RecordExtras) (gs : GhostState (List (BitVec 8))) :
    { removeOpk { st1 with session := none } m with peerId := some idA, session := some (x, gs) } =
      { removeOpk st1 m with peerId := some idA, session := some (x, gs) } := by
  rcases st1 with ⟨_, _, _, _, _, _, _, _⟩
  unfold removeOpk
  cases m.opkId <;> rfl

private theorem opk_upd_pqRecv (W : PEParams) (st st1 : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (m : PreKeyMessageFields) (k : ResponderPreKeySecrets)
    (hwf : PqxdhPartyInSpecDomain W st) (hkeys : preKeysNamedBy st m = some k) :
    ∃ (w7 : List (String × List (BitVec 8))) (otDir : DirGhost),
      (m.opkId = none → otDir = StoresGhost.opened.oneTime) ∧
      (∀ j, m.opkId = some j →
        otDir = (removePreKey cliIo.rd (runFiles (pqRecvInputs W st c rc))
          StoresGhost.opened.oneTime j).2) ∧
      ((∀ pw ∈ otDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
       otDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w7) ∧
      (∀ z ∈ w7, DecPkS0.recvBucket z.1 = 7) ∧
      (∀ z ∈ w7, DecPkS0.IsRecvFile z.1) ∧
      ((removeOpk st1 m).oneTime = (removeOpk st m).oneTime →
        st1.oneTime = st.oneTime →
        ∀ q, (DecPkS0.blockDir7 W st ++ w7).reverse.find? (fun u => u.1 == q) =
          (DecPkS0.blockDir7 W st ++ DecPkS0.blockDir7 W (removeOpk st1 m)).reverse.find?
            (fun u => u.1 == q)) := by
  cases hopk : m.opkId with
  | none =>
    refine ⟨[], StoresGhost.opened.oneTime, ?_, ?_,
      ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩,
      fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h), fun _ hst1 q => ?_⟩
    · intro _; rfl
    · intro _ h; nomatch h
    · have h7eq : DecPkS0.blockDir7 W (removeOpk st1 m) = DecPkS0.blockDir7 W st := by
        simp only [removeOpk, hopk, DecPkS0.blockDir7, hst1]
      rw [h7eq, List.append_nil]
      exact DecPkS0.find?_self_double _ q
  | some j =>
    have hsk_ex : ∃ sk, List.lookup j st.oneTime = some (some sk) := by
      rw [DecPkS0.keysFor_eq] at hkeys
      cases hspk : List.lookup m.spkId st.signed with
      | none => rw [hspk] at hkeys; nomatch hkeys
      | some s0 =>
        rw [hspk] at hkeys
        cases hkyb : DecPkS0.kyberLookup st m.kpkId with
        | none => rw [hkyb] at hkeys; nomatch hkeys
        | some kv =>
          rw [hkyb, hopk] at hkeys
          try dsimp only at hkeys
          cases hotl : List.lookup j st.oneTime with
          | none => simp [hotl] at hkeys
          | some ov =>
            cases ov with
            | none => simp [hotl] at hkeys
            | some sk => exact ⟨sk, rfl⟩
    obtain ⟨sk, hsk⟩ := hsk_ex
    have hrem_ot := DecPkS0.removePreKey_pqRecv W st c rc hwf.2.2.2.1 hsk
    obtain ⟨hot_str, hot_asc⟩ := DecPkS0.oneTime_path_eq j
    refine ⟨[(oneTimePreKeyFile j, [])],
      StoresGhost.opened.oneTime.put (keyName j) [], ?_, ?_,
      ⟨?_, ?_⟩, ?_, ?_, fun _ hst1 q => ?_⟩
    · intro h; nomatch h
    · intro j' hj'; cases hj'; exact hrem_ot.symm
    · intro pw hpw bt hbt
      change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
      rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw
      subst hpw; exact hot_asc bt hbt
    · change ((DirGhost.new _).put _ _).writes.map _ = _
      rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hot_str]
    · intro z hz
      rw [List.mem_singleton] at hz; subst hz; exact DecPkS0.recvBucket_oneTimePreKey j
    · intro z hz
      rw [List.mem_singleton] at hz; subst hz; exact DecPkS0.isRecvFile_oneTimePreKey j
    · have hm0 : (j, some sk) ∈ st.oneTime := DecPkS0.mem_of_lookup_eq_some hsk
      have h7' : DecPkS0.blockDir7 W (removeOpk st1 m) =
          ((st.oneTime.map (fun (i, a) =>
            if i = j then (i, none) else (i, a))).map (fun (i, a) =>
            (oneTimePreKeyFile i,
              match a with
              | some s => oneTimeRecordBytes W.C i s
              | none => []))) := by
        unfold removeOpk
        rw [hopk]
        simp only [DecPkS0.blockDir7, hst1]; rfl
      rw [h7']
      exact DecPkS0.find?_map_update DecPkS0.oneTimePreKeyFile_inj hm0
        (fun i a => match a with
          | some s => oneTimeRecordBytes W.C i s | none => [])
        none [] rfl q

/-! ## 4. `noMatchRecordBytes`, `NoMatchSessionFile`, and Archived-Record Bridge -/

abbrev noMatchRecordBytes := d3NoMatchRecordBytes

abbrev NoMatchSessionFile := D3NoMatchSessionFile

/-- On an accepted `recvPrekeyState X W P me k m rc = some (some (x', gs, pt))`, the `Prev1` record
written by `decPkOverDef` over `(E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g)` equals
`noMatchRecordBytes x g x' gs`. -/
theorem encodeRecordPrev1_recvPrekeyState_eq {X : UnreachedPqxdhPrimitives} {W : PEParams} {P : Party}
    {me : LocalIdentity} {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} {rc : BitVec 256}
    {x x' : RecordExtras} {g gs : GhostState (List (BitVec 8))} {pt : List (BitVec 8)}
    {s : Session (List (BitVec 8))}
    (hcur : (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g).currentSession = some s)
    (hrecv : recvPrekeyState X W P me k m rc = some (some (x', gs, pt))) :
    Over.encodeRecordPrev1
      { state := gs.session
        pendingPreKey := none
        pendingKyberPreKey := none
        localRegistrationId := me.regId
        remoteRegistrationId := m.regId
        aliceBaseKey := djbKey m.baseKey }
      (E2E.Record.encSession (Over.clearPending s)) =
    noMatchRecordBytes x g x' gs := by
  dsimp only [E2E.Record.toRecord] at hcur
  injection hcur with hs_eq; subst hs_eq
  unfold recvPrekeyState at hrecv
  cases hi : SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rw [hi] at hrecv; cases hrecv
  | ok inner =>
    rw [hi] at hrecv; dsimp only at hrecv
    split at hrecv
    · cases hrecv
    · cases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
      | none => rw [hacc] at hrecv; cases hrecv
      | some dk =>
        rw [hacc] at hrecv; dsimp only at hrecv
        cases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc (Poll.pathAInitState W me k m dk) with
        | mk res st' =>
          have hdec' := hdec; dsimp only [Poll.pathAInitState] at hdec'; rw [hdec'] at hrecv
          cases res with
          | error e => cases e <;> simp at hrecv
          | ok pt' =>
            dsimp only at hrecv
            injection hrecv with hsome
            injection hsome with htuple
            rcases Prod.mk.inj htuple with ⟨rfl, hrest⟩
            rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
            have hpend : st'.pendingPreKey = false :=
              (SessionState.tryDecryptFromRecord_ok W.C (pqxdhSpqrSession W) _ inner .preKey rc hdec).1
            unfold Over.encodeRecordPrev1 noMatchRecordBytes d3NoMatchRecordBytes
            rw [E2E.RecordX.encodeRecordX_eq_toRecord]
            unfold E2E.Record.toRecord E2E.RecordX.extrasOf E2E.RecordX.toSessionExtras responderRecordExtras
            dsimp only
            rw [hpend]
            rfl

private theorem splitSlash_go_no_slash :
    ∀ (cs cur : List Char), '/' ∉ cs →
      Arm64.splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by simp [Arm64.splitSlash.go]
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    have hstep : Arm64.splitSlash.go cur (c :: cs) = Arm64.splitSlash.go (c :: cur) cs := by
      rw [Arm64.splitSlash.go.eq_def]
      split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq
        injection heq with h1 h2
        subst h1 h2
        rfl
    rw [hstep, splitSlash_go_no_slash cs (c :: cur) (fun m => h (List.mem_cons_of_mem _ m))]
    simp [List.reverse_cons, List.append_assoc]

private theorem two_not_mem_stdioPaths (d sfx : String) :
    [d, sfx] ∉ stdioPaths.map Arm64.normalizePath := by
  intro hm
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hm
  have hns : '/' ∉ q.toList := by
    simp only [stdioPaths, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  have hle : (Arm64.normalizePath q).length ≤ 1 := by
    unfold Arm64.normalizePath Arm64.splitSlash
    rw [splitSlash_go_no_slash q.toList [] hns]
    exact List.length_filter_le _ [_]
  rw [heq] at hle
  nomatch hle

/-- Reading `sessionFile (partyAddress P)` after appending `(sessionFile (partyAddress P), b)` returns `some b`. -/
theorem filesOf_append_sessionFile_self (L : List (String × List (BitVec 8)))
    (P : Party) (b : List (BitVec 8)) :
    filesOf (L ++ [(sessionFile (partyAddress P), b)]) (sessionFile (partyAddress P)) = some b := by
  have hp_hne : Arm64.normalizePath (sessionFile (partyAddress P)) ∉
        stdioPaths.map Arm64.normalizePath ∧
      (Arm64.normalizePath (sessionFile (partyAddress P))).isEmpty = false := by
    rcases DecPkS0.isRecvFile_norm_shape (DecPkS0.isRecvFile_sessionFile P) with
      ⟨hr, hnq⟩ | ⟨d, sfx, _, _, hnq⟩
    · rw [hnq]; exact ⟨(DecPkS0.recvRootFiles_props hr).2.2.1, rfl⟩
    · rw [hnq]; exact ⟨two_not_mem_stdioPaths d sfx, rfl⟩
  obtain ⟨hp, hne⟩ := hp_hne
  unfold filesOf fsView
  rw [ite_eq_right_iff.mpr (fun h => absurd h hp)]
  unfold Arm64.FsState.files Arm64.FsState.getEntry
  rw [hne, initFsState_entries { files := L ++ [(sessionFile (partyAddress P), b)] }
    (Arm64.normalizePath (sessionFile (partyAddress P))) hp]
  simp [filesFold, Arm64.FsState.setFile, Arm64.FsState.setEntry]

private theorem filesOf_namedWrites_session_self
    (F0 : List (String × List (BitVec 8))) (P : Party)
    (idBytes sessBytes : List (BitVec 8))
    (kotDir klrDir otDir : DirGhost)
    {w8 w9 w7 : List (String × List (BitVec 8))}
    (hkot : (∀ pw ∈ kotDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
      kotDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w8)
    (hklr : (∀ pw ∈ klrDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
      klrDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w9)
    (hot : (∀ pw ∈ otDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
      otDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w7) :
    filesOf (F0 ++ namedWrites ({ StoresGhost.opened with
      identity := { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put (RunRefine.addrValE P).name idBytes }
      kyber := { oneTime := kotDir, lastResort := klrDir }
      oneTime := otDir
      sessions := StoresGhost.opened.sessions.put
        (Cli.addressText (RunRefine.addrValE P)) sessBytes }).writes)
      (sessionFile (partyAddress P)) = some sessBytes := by
  have hw := DecPkS0.namedWrites_of_dirs P idBytes sessBytes kotDir klrDir otDir hkot hklr hot
  rw [hw]
  simp only [← List.append_assoc]
  exact filesOf_append_sessionFile_self _ P sessBytes

/-! ## 5. Full `OutcomeMatchesModelExceptPath ∧ NoMatchSessionFile` Agreement on `runAns` -/

private theorem over_commit_files_agree (W : PEParams) (st : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256) (m : PreKeyMessageFields) (k : ResponderPreKeySecrets)
    (x' : RecordExtras) (gs : GhostState (List (BitVec 8)))
    (sessBytes : List (BitVec 8)) {kyber' : KyberGhost} {st1 : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) (hkeys : preKeysNamedBy st m = some k)
    (hlr_some : List.lookup m.kpkId st.kyberOneTime = none ∨
                List.lookup m.kpkId st.kyberOneTime = some none →
                (List.lookup m.kpkId st.kyberLastResort).isSome)
    (hkm : StoresGhost.opened.kyber.mark cliIo.rd
      (runFiles (pqRecvInputs W st c rc)) m.kpkId m.spkId ⟨m.baseKey⟩ = (.ok (), kyber'))
    (hm_mod : markKyberUsed st m = some st1) :
    let oneTime' := match m.opkId with
      | none => StoresGhost.opened.oneTime
      | some j => (removePreKey cliIo.rd (runFiles (pqRecvInputs W st c rc))
          StoresGhost.opened.oneTime j).2
    let g_out : StoresGhost := { StoresGhost.opened with
      identity := { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put
          (RunRefine.addrValE st.party.other).name (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize }
      kyber := kyber'
      oneTime := oneTime'
      sessions := StoresGhost.opened.sessions.put
        (Cli.addressText (RunRefine.addrValE st.party.other)) sessBytes }
    let st_out : PqParty :=
      { removeOpk st1 m with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', gs) }
    (∀ q, Arm64.normalizePath q ≠ Arm64.normalizePath (sessionFile (partyAddress st.party.other)) →
      filesOf ((pqRecvInputs W st c rc).files ++ namedWrites g_out.writes) q =
        filesOf ((pqRecvInputs W st c rc).files ++ encodeDir W st_out) q) ∧
    filesOf ((pqRecvInputs W st c rc).files ++ namedWrites g_out.writes)
      (sessionFile (partyAddress st.party.other)) = some sessBytes := by
  intro oneTime' g_out st_out
  have hmark := DecPkS0.kyberMark_pqRecv W st c rc hwf m hlr_some
  rw [hkm, hm_mod] at hmark
  obtain ⟨w7, otDir, hot_none, hot_some, hot_wr, hb7, hw7, heq7_fn⟩ :=
    opk_upd_pqRecv W st st1 c rc m k hwf hkeys
  have hotDir_eq : oneTime' = otDir := by
    dsimp only [oneTime']
    cases hopk0 : m.opkId
    · exact (hot_none hopk0).symm
    · next j0 => exact (hot_some j0 hopk0).symm
  have hswap_and_self :
      (∀ q, Arm64.normalizePath q ≠ Arm64.normalizePath (sessionFile (partyAddress st.party.other)) →
        filesOf ((pqRecvInputs W st c rc).files ++ namedWrites g_out.writes) q =
          filesOf ((pqRecvInputs W st c rc).files ++ namedWrites ({ g_out with
            sessions := StoresGhost.opened.sessions.put
              (Cli.addressText (RunRefine.addrValE st.party.other))
              (encodeRecordUnderExtras (fun _ => x') gs) }).writes) q) ∧
      filesOf ((pqRecvInputs W st c rc).files ++ namedWrites g_out.writes)
        (sessionFile (partyAddress st.party.other)) = some sessBytes ∧
      filesOf ((pqRecvInputs W st c rc).files ++ namedWrites ({ g_out with
          sessions := StoresGhost.opened.sessions.put
            (Cli.addressText (RunRefine.addrValE st.party.other))
            (encodeRecordUnderExtras (fun _ => x') gs) }).writes) =
        filesOf ((pqRecvInputs W st c rc).files ++ encodeDir W st_out) := by
    dsimp only [g_out, st_out]; rw [hotDir_eq]
    have h8_rem (st0 : PqParty) : (removeOpk st0 m).kyberOneTime = st0.kyberOneTime := by
      unfold removeOpk; cases m.opkId <;> rfl
    have h9_rem (st0 : PqParty) : (removeOpk st0 m).kyberLastResort = st0.kyberLastResort := by
      unfold removeOpk; cases m.opkId <;> rfl
    have h1_rem (st0 : PqParty) : (removeOpk st0 m).party = st0.party := by
      unfold removeOpk; cases m.opkId <;> rfl
    have h2_rem (st0 : PqParty) : (removeOpk st0 m).me = st0.me := by
      unfold removeOpk; cases m.opkId <;> rfl
    have h6_rem (st0 : PqParty) : (removeOpk st0 m).signed = st0.signed := by
      unfold removeOpk; cases m.opkId <;> rfl
    have hb_id : ∀ x ∈ [(identityFile (partyAddressName st.party.other), (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize)],
        DecPkS0.recvBucket x.1 = 4 := fun _ h => by
      rw [List.mem_singleton] at h; subst h; exact DecPkS0.recvBucket_identityFile _
    have hb_ss : ∀ x ∈ [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x') gs)],
        DecPkS0.recvBucket x.1 = 5 := fun _ h => by
      rw [List.mem_singleton] at h; subst h; exact DecPkS0.recvBucket_sessionFile _
    have hemp_wr (d : DirGhost) (hd : d.writes = []) :
        (∀ pw ∈ d.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
        d.writes.map (fun pw => (pathStr pw.1, pw.2)) = [] := by
      rw [hd]; exact ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
    rcases hmark with ⟨k1, hkot1, rfl, rfl⟩ | ⟨k2, seen, hklr2, _, rfl, rfl⟩
    · obtain ⟨hkot_str, hkot_asc⟩ := DecPkS0.kyberOneTime_path_eq m.kpkId
      have hkot_wr :
          (∀ pw ∈ (StoresGhost.opened.kyber.oneTime.put (keyName m.kpkId) []).writes,
            ∀ bt ∈ pw.1, bt.toNat < 128) ∧
          (StoresGhost.opened.kyber.oneTime.put (keyName m.kpkId) []).writes.map
            (fun pw => (pathStr pw.1, pw.2)) = [(oneTimeKyberPreKeyFile m.kpkId, [])] :=
        ⟨fun pw hpw bt hbt => by
           change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
           rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw; subst hpw; exact hkot_asc bt hbt,
         by change ((DirGhost.new _).put _ _).writes.map _ = _
            rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hkot_str]⟩
      have hklr_wr := hemp_wr StoresGhost.opened.kyber.lastResort rfl
      refine ⟨fun q hne => filesOf_namedWrites_swap_session_ne _ _ _ _ _ _ _ _ hkot_wr hklr_wr hot_wr hne,
        filesOf_namedWrites_session_self _ _ _ _ _ _ _ hkot_wr hklr_wr hot_wr, ?_⟩
      rw [DecPkS0.namedWrites_of_dirs st.party.other _ _ _ _ _ hkot_wr hklr_wr hot_wr]
      have hm_kot := DecPkS0.mem_of_lookup_eq_some hkot1
      exact DecPkS0.filesOf_commit_master W st _ c rc _ rfl hb_id hb_ss hb7
        (fun _ h => by rw [List.mem_singleton] at h; subst h; exact DecPkS0.recvBucket_oneTimeKyberPreKey _)
        (fun _ h => False.elim (List.not_mem_nil h)) hw7
        (fun _ h => by rw [List.mem_singleton] at h; subst h; exact DecPkS0.isRecvFile_oneTimeKyberPreKey _)
        (fun _ h => False.elim (List.not_mem_nil h))
        (by simp only [DecPkS0.blockDir1, h1_rem]) (by simp only [DecPkS0.blockDir2, h2_rem])
        (by simp only [DecPkS0.blockDir3, h2_rem]) (by simp only [DecPkS0.blockDir4, h1_rem])
        (by simp only [DecPkS0.blockDir5, h1_rem]) (by simp only [DecPkS0.blockDir6, h6_rem])
        (fun q => heq7_fn (by unfold removeOpk; cases m.opkId <;> rfl) rfl q)
        (fun q => by
          simp only [DecPkS0.blockDir8, h8_rem]
          exact DecPkS0.find?_map_update DecPkS0.oneTimeKyberPreKeyFile_inj hm_kot
            (fun i a => match a with | some kv => kyberRecordBytes i kv | none => []) none [] rfl q)
        (fun q => by simp only [DecPkS0.blockDir9, h9_rem, List.append_nil]; exact DecPkS0.find?_self_double _ q)
    · obtain ⟨_, _, _, _, _, hnd_klr⟩ := hwf
      have hm_klr := DecPkS0.mem_of_lookup_eq_some hklr2
      have huniq_seen : ∀ {l : List (BitVec 32 × PqKyberKey ×
          List (BitVec 32 × List.Vector (BitVec 8) 32))},
          (l.map Prod.fst).Nodup → (m.kpkId, (k2, seen)) ∈ l →
          ∀ {k s}, (m.kpkId, (k, s)) ∈ l → s = seen := by
        intro l hnd hm1 k s hm2
        induction l with
        | nil => nomatch hm1
        | cons hd tl ih =>
          obtain ⟨hnot, hnd_tl⟩ := List.nodup_cons.mp hnd
          rcases List.mem_cons.mp hm1 with rfl | hm1' <;> rcases List.mem_cons.mp hm2 with h2 | hm2'
          · exact (Prod.mk.inj (Prod.mk.inj h2).2).2
          · exact False.elim (hnot (List.mem_map.mpr ⟨_, hm2', rfl⟩))
          · subst h2; exact False.elim (hnot (List.mem_map.mpr ⟨_, hm1', rfl⟩))
          · exact ih hnd_tl hm1' hm2'
      have hklr_map_eq :
          st.kyberLastResort.map (fun (i, k, s) =>
            if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s)) =
          st.kyberLastResort.map (fun (i, k, s) =>
            if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)]) else (i, k, s)) := by
        refine List.map_congr_left fun ⟨i, k, s⟩ hmem => ?_; dsimp only
        by_cases hi : i = m.kpkId
        · subst hi; rw [huniq_seen hnd_klr hm_klr hmem]
        · simp only [hi, ↓reduceIte]
      rw [hklr_map_eq] at heq7_fn ⊢
      obtain ⟨hbk_str, hbk_asc⟩ := DecPkS0.baseKeys_path_eq m.kpkId
      have hkot_wr := hemp_wr StoresGhost.opened.kyber.oneTime rfl
      have hklr_wr :
          (∀ pw ∈ (StoresGhost.opened.kyber.lastResort.put (baseKeysName m.kpkId)
            (baseKeysBytes (seen ++ [(m.spkId, m.baseKey)]))).writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
          (StoresGhost.opened.kyber.lastResort.put (baseKeysName m.kpkId)
            (baseKeysBytes (seen ++ [(m.spkId, m.baseKey)]))).writes.map (fun pw => (pathStr pw.1, pw.2)) =
            [(baseKeysFile m.kpkId, baseKeysBytes (seen ++ [(m.spkId, m.baseKey)]))] :=
        ⟨fun pw hpw bt hbt => by
           change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
           rw [DecPkS0.new_put_writes, List.mem_singleton] at hpw; subst hpw; exact hbk_asc bt hbt,
         by change ((DirGhost.new _).put _ _).writes.map _ = _
            rw [DecPkS0.new_put_writes, List.map_cons, List.map_nil, hbk_str]⟩
      refine ⟨fun q hne => filesOf_namedWrites_swap_session_ne _ _ _ _ _ _ _ _ hkot_wr hklr_wr hot_wr hne,
        filesOf_namedWrites_session_self _ _ _ _ _ _ _ hkot_wr hklr_wr hot_wr, ?_⟩
      rw [DecPkS0.namedWrites_of_dirs st.party.other _ _ _ _ _ hkot_wr hklr_wr hot_wr]
      exact DecPkS0.filesOf_commit_master W st _ c rc _ rfl hb_id hb_ss hb7
        (fun _ h => False.elim (List.not_mem_nil h))
        (fun _ h => by rw [List.mem_singleton] at h; subst h; exact DecPkS0.recvBucket_baseKeysFile _)
        hw7 (fun _ h => False.elim (List.not_mem_nil h))
        (fun _ h => by rw [List.mem_singleton] at h; subst h; exact DecPkS0.isRecvFile_baseKeysFile _)
        (by simp only [DecPkS0.blockDir1, h1_rem]) (by simp only [DecPkS0.blockDir2, h2_rem])
        (by simp only [DecPkS0.blockDir3, h2_rem]) (by simp only [DecPkS0.blockDir4, h1_rem])
        (by simp only [DecPkS0.blockDir5, h1_rem]) (by simp only [DecPkS0.blockDir6, h6_rem])
        (fun q => heq7_fn (by unfold removeOpk; cases m.opkId <;> rfl) rfl q)
        (fun q => by simp only [DecPkS0.blockDir8, h8_rem, List.append_nil]; exact DecPkS0.find?_self_double _ q)
        (fun q => by simp only [DecPkS0.blockDir9, h9_rem]; exact DecPkS0.find?_lr_update hm_klr q)
  exact ⟨fun q hne => (hswap_and_self.1 q hne).trans (congrFun hswap_and_self.2.2 q),
    hswap_and_self.2.1⟩

/-- Full `OutcomeMatchesModelExceptPath ∧ NoMatchSessionFile` agreement for `runAns S` on ANY `body` with
`Pksm.pksmParse body = some pm` and `pkToE? pm = some m` when `st.session = some (x, g)` does not match `m`. -/
theorem observedExcept_and_noMatchSessionFile_runAns_decPkOverDef
    {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hdec : S.decryptPrekey = decPkOverDef X W Slots.scopeIn)
    (hparseS : ∀ b, S.pksmParse b = Pksm.pksmParse b)
    {st : PqParty} (hwf : PqxdhPartyInSpecDomain W st)
    {x : RecordExtras} {g : GhostState (List (BitVec 8))} (hsess : st.session = some (x, g))
    {body : List (BitVec 8)} {pm : PreKeySignalMessage} {m : PreKeyMessageFields} {rc : BitVec 256}
    (hparse : Pksm.pksmParse body = some pm)
    (hpk : pkToE? pm = some m)
    (hnomatch : ¬ PqSessionMatches x g m) :
    let inp := pqRecvInputs W st (wirePrekey :: body) rc
    OutcomeMatchesModelExceptPath W inp (sessionFile (partyAddress st.party.other))
      (pqRecvPrekeyModel X W { st with session := none } m rc)
      (observe inp.files (runAns S inp)) ∧
    NoMatchSessionFile X W st x g m rc (observe inp.files (runAns S inp)) := by
  intro inp
  have hpeer_id := DecPkS0.idPeer_pqRecv W st (wirePrekey :: body) rc
  have hload := DecPkS0.loadRec_pqRecv_eq encodeInjOn_scopeIn_placed (ratchetScopeCoversPq_scopeIn_placed W)
    st (wirePrekey :: body) rc hwf
  rw [hsess] at hload
  dsimp only [Option.map_some] at hload
  have hIn : Slots.scopeIn (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) :=
    ratchetScopeCoversPq_scopeIn_placed W st x g hwf hsess
  have hnot_pm := not_sessMatchesPm_toRecord_of_not_pqSessionMatches x g hIn hpk hnomatch _ rfl
  have hp_eq : initParty (RunRefine.addrValE st.party.other) = st.party := InitS0.initParty_eq st.party
  have hcoins : pkRecvCoins (HMAC.keyToBytes32 rc) = rc := DecPkS0.pkRecvCoins_keyToBytes32 rc
  obtain ⟨_, _, hopk_eq, hspk_eq, hbk_eq, hid_eq, _, _⟩ := pm_fields_of_pkToE hpk rfl
  have htrust : StoresGhost.opened.identity.trusted cliIo.rd (runFiles inp)
      (RunRefine.addrValE st.party.other) pm.identityKey = .ok (st.trusts ⟨⟨m.idPub⟩⟩) := by
    rw [hid_eq]; unfold IdGhost.trusted PqParty.trusts; rw [hpeer_id]; cases st.peerId <;> rfl
  have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd (runFiles inp)
      (RunRefine.addrValE st.party.other) pm.identityKey =
      { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put
          (RunRefine.addrValE st.party.other).name (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize } := by
    rw [hid_eq]; unfold IdGhost.saveUpd; rw [hpeer_id]
  have hi := tryFrom_inner_of_pksmParse_pkToE hparse hpk
  have htrust_none : ({ st with session := none } : PqParty).trusts ⟨⟨m.idPub⟩⟩ = st.trusts ⟨⟨m.idPub⟩⟩ := rfl
  have hkeys_none : preKeysNamedBy { st with session := none } m = preKeysNamedBy st m := rfl
  rw [RunRefine.runAns_pqRecvPrekey_eq, hparseS body, hparse, hdec]
  dsimp only [inp] at hload htrust hsave ⊢
  unfold decPkOverDef NoMatchSessionFile D3NoMatchSessionFile pqRecvPrekeyModel; dsimp only
  rw [hi, htrust_none, hload, htrust, hp_eq, hcoins, hkeys_none]
  cases ht : st.trusts ⟨⟨m.idPub⟩⟩ with
  | false => exact ⟨rfl, fun _ _ _ _ h => nomatch h⟩
  | true =>
    rw [show (!true) = false from rfl, ite_eq_right Bool.noConfusion]
    dsimp only [Option.bind_some, E2E.Record.toRecord]; rw [ite_eq_right hnot_pm, hpk]; dsimp only
    have hpk_fn : pkStoreKeys = DecPkS0.pkStoreKeys := rfl
    rw [hpk_fn, DecPkS0.pkStoreKeys_pqRecv W st (wirePrekey :: body) rc hwf m,
      DecPkS0.keyPair_pqRecv W st (wirePrekey :: body) rc,
      DecPkS0.regId_pqRecv W st (wirePrekey :: body) rc]
    cases hkeys : preKeysNamedBy st m with
    | none => exact ⟨rfl, fun _ _ _ _ h => nomatch h⟩
    | some k =>
      dsimp only; rw [DecPkS0.recvPrekeyState_clampScalar]
      cases hrecv : recvPrekeyState X W st.party st.me k m rc with
      | none => exact ⟨rfl, fun _ _ _ _ h => nomatch h⟩
      | some o =>
        cases o with
        | none => exact ⟨rfl, fun _ _ _ _ h => nomatch h⟩
        | some triple =>
          rcases triple with ⟨x', gs, pt⟩; dsimp only
          have hlr_some : List.lookup m.kpkId st.kyberOneTime = none ∨
              List.lookup m.kpkId st.kyberOneTime = some none →
              (List.lookup m.kpkId st.kyberLastResort).isSome := by
            intro hno; unfold preKeysNamedBy at hkeys
            cases hspk : List.lookup m.spkId st.signed with
            | none => rw [hspk] at hkeys; nomatch hkeys
            | some _ =>
              rw [hspk] at hkeys; rcases hno with hn | hn <;> rw [hn] at hkeys <;>
                (cases hlr : List.lookup m.kpkId st.kyberLastResort with
                 | none => simp [hlr] at hkeys | some _ => rfl)
          rw [hspk_eq, hbk_eq, hopk_eq, markKyberUsed_session_none st m]
          have hmark_rel := DecPkS0.kyberMark_pqRecv W st (wirePrekey :: body) rc hwf m hlr_some
          cases hkm : StoresGhost.opened.kyber.mark cliIo.rd
              (runFiles (pqRecvInputs W st (wirePrekey :: body) rc)) m.kpkId m.spkId ⟨m.baseKey⟩ with
          | mk kres kyber' =>
            cases hm_mod : markKyberUsed st m with
            | none =>
              rw [hkm, hm_mod] at hmark_rel
              cases kres with | error _ => exact ⟨rfl, fun _ _ _ _ h => nomatch h⟩ | ok _ => nomatch hmark_rel
            | some st1 =>
              rw [hkm, hm_mod] at hmark_rel
              cases kres with | error _ => nomatch hmark_rel | ok u =>
                cases u; dsimp only [Option.map_some, finish, observe, pqxdhExpectedOutcome, OutcomeMatchesModelExceptPath, Outcome.AgreeExcept]
                rw [hsave, removeOpk_session_none_overwrite]
                have hrec_eq := encodeRecordPrev1_recvPrekeyState_eq (x := x) (g := g) rfl hrecv
                obtain ⟨hexcept, hself⟩ := over_commit_files_agree W st (wirePrekey :: body) rc m k x' gs _ hwf hkeys hlr_some hkm hm_mod
                refine ⟨⟨rfl, rfl, hexcept⟩, fun st' out x'' g'' hmod hsess' code out' fs hex => ?_⟩
                injection hmod with hmod'; injection hmod' with hpair; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
                injection hsess' with hxg'; rcases Prod.mk.inj hxg' with ⟨rfl, rfl⟩
                injection hex with _ _ hfs; subst hfs; exact hself.trans (congrArg some hrec_eq)

theorem observedExcept_runAns_decPkOverDef
    {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hdec : S.decryptPrekey = decPkOverDef X W Slots.scopeIn)
    (hparseS : ∀ b, S.pksmParse b = Pksm.pksmParse b)
    {st : PqParty} (hwf : PqxdhPartyInSpecDomain W st)
    {x : RecordExtras} {g : GhostState (List (BitVec 8))} (hsess : st.session = some (x, g))
    {body : List (BitVec 8)} {pm : PreKeySignalMessage} {m : PreKeyMessageFields} {rc : BitVec 256}
    (hparse : Pksm.pksmParse body = some pm)
    (hpk : pkToE? pm = some m)
    (hnomatch : ¬ PqSessionMatches x g m) :
    let inp := pqRecvInputs W st (wirePrekey :: body) rc
    OutcomeMatchesModelExceptPath W inp (sessionFile (partyAddress st.party.other))
      (pqRecvPrekeyModel X W { st with session := none } m rc)
      (observe inp.files (runAns S inp)) :=
  (observedExcept_and_noMatchSessionFile_runAns_decPkOverDef
    hdec hparseS hwf hsess hparse hpk hnomatch).1

/-- Canonical (`body := m.bytes`) `OutcomeMatchesModelExceptPath ∧ NoMatchSessionFile` agreement under
`hm : m.inner.length + 2048 < 2 ^ 32`, covering both valid and invalid inner `SignalMessage` bytes. -/
theorem observedExcept_and_noMatchSessionFile_runAns_canonical
    {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hdec : S.decryptPrekey = decPkOverDef X W Slots.scopeIn)
    (hparseS : ∀ b, S.pksmParse b = Pksm.pksmParse b)
    {st : PqParty} (hwf : PqxdhPartyInSpecDomain W st)
    {x : RecordExtras} {g : GhostState (List (BitVec 8))} (hsess : st.session = some (x, g))
    {m : PreKeyMessageFields} {rc : BitVec 256}
    (hm : m.inner.length + 2048 < 2 ^ 32) (hnomatch : ¬ PqSessionMatches x g m) :
    let inp := pqRecvInputs W st (wirePrekey :: m.bytes) rc
    OutcomeMatchesModelExceptPath W inp (sessionFile (partyAddress st.party.other))
      (pqRecvPrekeyModel X W { st with session := none } m rc)
      (observe inp.files (runAns S inp)) ∧
    NoMatchSessionFile X W st x g m rc (observe inp.files (runAns S inp)) := by
  have hb := Pksm.pksmParse_bytes (RunRefine.argsOf m) hm
  rw [RunRefine.argsOf_bytes] at hb
  have hinner : (RunRefine.argsOf m).inner = m.inner := rfl
  cases hi : SignalMessage.tryFrom protoSignalCodec m.inner with
  | ok inner =>
    have hparse : Pksm.pksmParse m.bytes = some (pmOfE m inner) := by rw [hb, hinner, hi]; rfl
    exact observedExcept_and_noMatchSessionFile_runAns_decPkOverDef
      hdec hparseS hwf hsess hparse (DecPkS0.pkToE?_pmOfE m inner hi) hnomatch
  | error _ =>
    have hparse : Pksm.pksmParse m.bytes = none := by rw [hb, hinner, hi]
    have hmod_none : pqRecvPrekeyModel X W { st with session := none } m rc = some none := by
      unfold pqRecvPrekeyModel; rw [hi]
    intro inp; rw [RunRefine.runAns_pqRecvPrekey_eq, hparseS m.bytes, hparse, hmod_none]
    exact ⟨rfl, fun _ _ _ _ h => by rw [hmod_none] at h; cases h⟩

theorem observedExcept_runAns_canonical
    {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hdec : S.decryptPrekey = decPkOverDef X W Slots.scopeIn)
    (hparseS : ∀ b, S.pksmParse b = Pksm.pksmParse b)
    {st : PqParty} (hwf : PqxdhPartyInSpecDomain W st)
    {x : RecordExtras} {g : GhostState (List (BitVec 8))} (hsess : st.session = some (x, g))
    {m : PreKeyMessageFields} {rc : BitVec 256}
    (hm : m.inner.length + 2048 < 2 ^ 32) (hnomatch : ¬ PqSessionMatches x g m) :
    let inp := pqRecvInputs W st (wirePrekey :: m.bytes) rc
    OutcomeMatchesModelExceptPath W inp (sessionFile (partyAddress st.party.other))
      (pqRecvPrekeyModel X W { st with session := none } m rc)
      (observe inp.files (runAns S inp)) :=
  (observedExcept_and_noMatchSessionFile_runAns_canonical
    hdec hparseS hwf hsess hm hnomatch).1

end LibsignalBinary.Proofs.SignalSession.Cli.D3
