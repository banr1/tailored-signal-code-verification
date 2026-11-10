/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCommit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeKeys
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Proof of `pqDecryptPrekeyAgrees_decPkDef`

Combines store lookups, pre-key consumption updates, matched-session and fresh-session branches,
and pathwise `filesOf` overwrite lemmas to prove `DecPkS0.pqDecryptPrekeyAgrees_decPkDef`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes

theorem pqDecryptPrekeyAgrees_decPkDef (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS : S.decryptPrekey = decPkDef X W Scope) (hpksm : PksmTyped S)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope) :
    RunRefine.PqDecryptPrekeyAgrees S X W := by
  intro st m rc pm hwf hm hmatch hparse
  obtain ⟨inner, htry, rfl⟩ := hpksm m pm hm hparse
  have hpeer_id := idPeer_pqRecv W st (wirePrekey :: m.bytes) rc
  have hload := loadRec_pqRecv_eq hinj hcov st (wirePrekey :: m.bytes) rc hwf
  have hp_eq : initParty (RunRefine.addrValE st.party.other) = st.party :=
    InitS0.initParty_eq st.party
  have hcoins : pkRecvCoins (HMAC.keyToBytes32 rc) = rc := pkRecvCoins_keyToBytes32 rc
  have htrust : StoresGhost.opened.identity.trusted cliIo.rd
      (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
      (RunRefine.addrValE st.party.other) (pmOfE m inner).identityKey =
      .ok (st.trusts ⟨⟨m.idPub⟩⟩) := by
    unfold IdGhost.trusted PqParty.trusts
    rw [hpeer_id]
    cases st.peerId <;> rfl
  have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd
      (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
      (RunRefine.addrValE st.party.other) (⟨⟨m.idPub⟩⟩ : IdentityKey) =
      { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put
          (RunRefine.addrValE st.party.other).name (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize } := by
    unfold IdGhost.saveUpd
    rw [hpeer_id]
  rw [hS]
  unfold decPkDef pqRecvPrekeyModel pqxdhExpectedOutcome
  rw [htry]
  try dsimp only
  rw [hload, htrust, hp_eq, hcoins]
  cases ht : st.trusts ⟨⟨m.idPub⟩⟩ with
  | false => rfl
  | true =>
    rw [show (!true) = false from rfl, ite_eq_right (c := false = true) Bool.noConfusion]
    try dsimp only
    cases hs : st.session with
    | some xg =>
      rcases xg with ⟨x, gp, gs0, gep, gce⟩
      have hg_party : gp = st.party := (hwf.1 x ⟨gp, gs0, gep, gce⟩ hs).2.1
      subst hg_party
      have hm_pq : PqSessionMatches x ⟨st.party, gs0, gep, gce⟩ m :=
        hmatch x ⟨st.party, gs0, gep, gce⟩ hs
      have hm_pm : SessMatchesPm
          { state := gs0
            pendingPreKey := if gs0.pendingPreKey then some x.pending else none
            pendingKyberPreKey := if gs0.pendingPreKey then x.kyber else none
            localRegistrationId := x.localRegistrationId
            remoteRegistrationId := x.remoteRegistrationId
            aliceBaseKey := x.aliceBaseKey }
          (pmOfE m inner) :=
        sessMatchesPm_toRecord x ⟨st.party, gs0, gep, gce⟩ m inner hm_pq
      try dsimp only [Option.map_some, Option.bind_some, E2E.Record.toRecord, E2E.RecordX.extrasOf,
        E2E.RecordX.toSessionExtras]
      rw [ite_eq_left hm_pm, ite_eq_left hm_pq]
      have hrem_iff : (pmOfE m inner).identityKey = ⟨⟨m.idPub⟩⟩ := rfl
      have hmsg_eq : (pmOfE m inner).message = inner := rfl
      rw [hrem_iff, hmsg_eq]
      by_cases hrem : gs0.remoteIdentity ≠ some ⟨⟨m.idPub⟩⟩
      · rw [ite_eq_left hrem, ite_eq_left hrem]; rfl
      · rw [ite_eq_right hrem, ite_eq_right hrem]
        cases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs st.party) inner .preKey rc gs0 with
        | mk res st' =>
          cases res with
          | error err =>
            cases err <;> rfl
          | ok pt =>
            dsimp only
            have hpend : st'.pendingPreKey = false :=
              (SessionState.tryDecryptFromRecord_ok W.C (pqxdhSpqrSession W) _ inner .preKey rc hdec).1
            rw [hsave, encodeRecord_cleared_eq_encodeRecordX x ⟨st.party, gs0, gep, gce⟩ st' hpend]
            dsimp only [finish, Option.map_some, observe]
            refine congrArg (Outcome.exited 0 pt) ?_
            have hw := namedWrites_of_dirs st.party.other
              (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize
              (encodeRecordUnderExtras (fun _ => x) { party := st.party, session := st', epoch := gep, chainEpochs := gce })
              StoresGhost.opened.kyber.oneTime
              StoresGhost.opened.kyber.lastResort
              StoresGhost.opened.oneTime
              (w8 := []) (w9 := []) (w7 := [])
              ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
              ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
              ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
            rw [hw]
            exact filesOf_commit_master W st _ (wirePrekey :: m.bytes) rc _ rfl
              (fun _ h => by rw [List.mem_singleton] at h; subst h; exact recvBucket_identityFile _)
              (fun _ h => by rw [List.mem_singleton] at h; subst h; exact recvBucket_sessionFile _)
              (fun _ h => False.elim (List.not_mem_nil h))
              (fun _ h => False.elim (List.not_mem_nil h))
              (fun _ h => False.elim (List.not_mem_nil h))
              (fun _ h => False.elim (List.not_mem_nil h))
              (fun _ h => False.elim (List.not_mem_nil h))
              (fun _ h => False.elim (List.not_mem_nil h))
              rfl rfl rfl rfl rfl rfl
              (fun q => by rw [List.append_nil]; exact find?_self_double _ q)
              (fun q => by rw [List.append_nil]; exact find?_self_double _ q)
              (fun q => by rw [List.append_nil]; exact find?_self_double _ q)
    | none =>
      try dsimp only [Option.map_none, Option.bind_none]
      rw [pkToE?_pmOfE m inner htry]
      try dsimp only
      rw [pkStoreKeys_pqRecv W st (wirePrekey :: m.bytes) rc hwf m,
        keyPair_pqRecv W st (wirePrekey :: m.bytes) rc,
        regId_pqRecv W st (wirePrekey :: m.bytes) rc]
      cases hkeys : preKeysNamedBy st m with
      | none => rfl
      | some k =>
        try dsimp only
        rw [recvPrekeyState_clampScalar]
        cases hrecv : recvPrekeyState X W st.party st.me k m rc with
        | none => rfl
        | some o =>
          cases o with
          | none => rfl
          | some triple =>
            rcases triple with ⟨x, gs, pt⟩
            try dsimp only
            have hlr_some :
                List.lookup m.kpkId st.kyberOneTime = none ∨
                List.lookup m.kpkId st.kyberOneTime = some none →
                (List.lookup m.kpkId st.kyberLastResort).isSome := by
              intro hno
              unfold preKeysNamedBy at hkeys
              cases hspk : List.lookup m.spkId st.signed with
              | none => rw [hspk] at hkeys; nomatch hkeys
              | some s0 =>
                rw [hspk] at hkeys
                rcases hno with hn | hn <;> rw [hn] at hkeys
                · cases hlr : List.lookup m.kpkId st.kyberLastResort with
                  | none => simp [hlr] at hkeys
                  | some _ => rfl
                · cases hlr : List.lookup m.kpkId st.kyberLastResort with
                  | none => simp [hlr] at hkeys
                  | some _ => rfl
            have hspk_id : (pmOfE m inner).signedPreKeyId = m.spkId := rfl
            have hbk_eq : (pmOfE m inner).baseKey = ⟨m.baseKey⟩ := rfl
            have hopk_eq : (pmOfE m inner).preKeyId = m.opkId := rfl
            have hid_eq : (pmOfE m inner).identityKey = ⟨⟨m.idPub⟩⟩ := rfl
            rw [hspk_id, hbk_eq]
            have hmark := kyberMark_pqRecv W st (wirePrekey :: m.bytes) rc hwf m hlr_some
            cases hkm : StoresGhost.opened.kyber.mark cliIo.rd
                (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
                m.kpkId m.spkId ⟨m.baseKey⟩ with
            | mk kres kyber' =>
              cases hm_mod : markKyberUsed st m with
              | none =>
                rw [hkm, hm_mod] at hmark
                cases kres with
                | error _ => rfl
                | ok _ => nomatch hmark
              | some st1 =>
                rw [hkm, hm_mod] at hmark
                cases kres with
                | error _ => nomatch hmark
                | ok _ =>
                  dsimp only [finish, Option.map_some, observe]
                  rw [hopk_eq, hid_eq, hsave]
                  refine congrArg (Outcome.exited 0 pt) ?_
                  have hopk_upd :
                      ∃ (w7 : List (String × List (BitVec 8))) (otDir : DirGhost),
                        (m.opkId = none → otDir = StoresGhost.opened.oneTime) ∧
                        (∀ j, m.opkId = some j →
                          otDir = (removePreKey cliIo.rd
                            (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
                            StoresGhost.opened.oneTime j).2) ∧
                        ((∀ pw ∈ otDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
                         otDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w7) ∧
                        (∀ z ∈ w7, recvBucket z.1 = 7) ∧
                        (∀ z ∈ w7, IsRecvFile z.1) ∧
                        ((removeOpk st1 m).oneTime = (removeOpk st m).oneTime →
                          st1.oneTime = st.oneTime →
                          ∀ q, (blockDir7 W st ++ w7).reverse.find? (fun u => u.1 == q) =
                            (blockDir7 W st ++ blockDir7 W (removeOpk st1 m)).reverse.find?
                              (fun u => u.1 == q)) := by
                    cases hopk : m.opkId with
                    | none =>
                      refine ⟨[], StoresGhost.opened.oneTime, ?_, ?_,
                        ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩,
                        fun _ h => False.elim (List.not_mem_nil h),
                        fun _ h => False.elim (List.not_mem_nil h), fun _ hst1 q => ?_⟩
                      · intro _; rfl
                      · intro _ h; nomatch h
                      · have h7eq : blockDir7 W (removeOpk st1 m) = blockDir7 W st := by
                          simp only [removeOpk, hopk, blockDir7, hst1]; try rfl
                        rw [h7eq, List.append_nil]
                        exact find?_self_double _ q
                    | some j =>
                      have hsk_ex : ∃ sk, List.lookup j st.oneTime = some (some sk) := by
                        rw [keysFor_eq] at hkeys
                        cases hspk : List.lookup m.spkId st.signed with
                        | none => rw [hspk] at hkeys; nomatch hkeys
                        | some s0 =>
                          rw [hspk] at hkeys
                          cases hkyb : kyberLookup st m.kpkId with
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
                      have hrem_ot := removePreKey_pqRecv W st (wirePrekey :: m.bytes) rc
                        hwf.2.2.2.1 hsk
                      obtain ⟨hot_str, hot_asc⟩ := oneTime_path_eq j
                      refine ⟨[(oneTimePreKeyFile j, [])],
                        StoresGhost.opened.oneTime.put (keyName j) [], ?_, ?_,
                        ⟨?_, ?_⟩, ?_, ?_, fun _ hst1 q => ?_⟩
                      · intro h; nomatch h
                      · intro j' hj'; cases hj'; exact hrem_ot.symm
                      · intro pw hpw bt hbt
                        change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
                        rw [new_put_writes, List.mem_singleton] at hpw
                        subst hpw; exact hot_asc bt hbt
                      · change ((DirGhost.new _).put _ _).writes.map _ = _
                        rw [new_put_writes, List.map_cons, List.map_nil, hot_str]
                      · intro z hz
                        rw [List.mem_singleton] at hz; subst hz; exact recvBucket_oneTimePreKey j
                      · intro z hz
                        rw [List.mem_singleton] at hz; subst hz; exact isRecvFile_oneTimePreKey j
                      · have hm0 : (j, some sk) ∈ st.oneTime := mem_of_lookup_eq_some hsk
                        have h7' : blockDir7 W (removeOpk st1 m) =
                            ((st.oneTime.map (fun (i, a) =>
                              if i = j then (i, none) else (i, a))).map (fun (i, a) =>
                              (oneTimePreKeyFile i,
                                match a with
                                | some s => oneTimeRecordBytes W.C i s
                                | none => []))) := by
                          simp only [removeOpk, hopk, blockDir7, hst1]; try rfl
                        rw [h7']
                        exact find?_map_update oneTimePreKeyFile_inj hm0
                          (fun i a => match a with
                            | some s => oneTimeRecordBytes W.C i s | none => [])
                          none [] rfl q
                  obtain ⟨w7, otDir, hot_none, hot_some, hot_wr, hb7, hw7, heq7_fn⟩ := hopk_upd
                  suffices hcommit : filesOf
                      ((pqRecvInputs W st (wirePrekey :: m.bytes) rc).files ++
                        namedWrites
                          ({ StoresGhost.opened with
                             identity := { StoresGhost.opened.identity with
                               peers := StoresGhost.opened.identity.peers.put
                                 (RunRefine.addrValE st.party.other).name
                                 (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize }
                             kyber := kyber'
                             oneTime := otDir
                             sessions := StoresGhost.opened.sessions.put
                               (addressText (RunRefine.addrValE st.party.other))
                               (encodeRecordUnderExtras (fun _ => x) gs) }).writes) =
                      filesOf
                        ((pqRecvInputs W st (wirePrekey :: m.bytes) rc).files ++
                          encodeDir W
                            { removeOpk st1 m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, gs) }) by
                    cases hopk0 : m.opkId
                    · dsimp only; rw [hot_none hopk0] at hcommit; exact hcommit
                    · next j0 => dsimp only; rw [hot_some j0 hopk0] at hcommit; exact hcommit
                  rcases hmark with ⟨k1, hkot1, rfl, rfl⟩ | ⟨k2, seen, hklr2, _, rfl, rfl⟩
                  · dsimp only
                    obtain ⟨hkot_str, hkot_asc⟩ := kyberOneTime_path_eq m.kpkId
                    have hw := namedWrites_of_dirs st.party.other
                      (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize
                      (encodeRecordUnderExtras (fun _ => x) gs)
                      (StoresGhost.opened.kyber.oneTime.put (keyName m.kpkId) [])
                      StoresGhost.opened.kyber.lastResort
                      otDir
                      (w8 := [(oneTimeKyberPreKeyFile m.kpkId, [])])
                      (w9 := [])
                      (w7 := w7)
                      ⟨fun pw hpw bt hbt => by
                         change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
                         rw [new_put_writes, List.mem_singleton] at hpw
                         subst hpw; exact hkot_asc bt hbt,
                       by change ((DirGhost.new _).put _ _).writes.map _ = _
                          rw [new_put_writes, List.map_cons, List.map_nil, hkot_str]⟩
                      ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
                      hot_wr
                    rw [hw]
                    have hparty_eq : ∀ q,
                        (blockDir7 W st ++ w7).reverse.find? (fun u => u.1 == q) =
                          (blockDir7 W st ++ blockDir7 W
                            { removeOpk
                                { st with kyberOneTime := st.kyberOneTime.map (fun (i, k) =>
                                    if i = m.kpkId then (i, none) else (i, k)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, gs) }).reverse.find?
                            (fun u => u.1 == q) := by
                      intro q
                      have hsame_ot :
                          (removeOpk
                            { st with kyberOneTime := st.kyberOneTime.map (fun (i, k) =>
                                if i = m.kpkId then (i, none) else (i, k)) } m).oneTime =
                          (removeOpk st m).oneTime := by
                        unfold removeOpk; cases m.opkId <;> rfl
                      exact heq7_fn hsame_ot rfl q
                    have hm_kot : (m.kpkId, some k1) ∈ st.kyberOneTime :=
                      mem_of_lookup_eq_some hkot1
                    have h8_rem : ∀ st0 : PqParty,
                        (removeOpk st0 m).kyberOneTime = st0.kyberOneTime := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h9_rem : ∀ st0 : PqParty,
                        (removeOpk st0 m).kyberLastResort = st0.kyberLastResort := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h1_rem : ∀ st0 : PqParty, (removeOpk st0 m).party = st0.party := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h2_rem : ∀ st0 : PqParty, (removeOpk st0 m).me = st0.me := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h6_rem : ∀ st0 : PqParty, (removeOpk st0 m).signed = st0.signed := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    exact filesOf_commit_master W st _ (wirePrekey :: m.bytes) rc _ rfl
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h; exact recvBucket_identityFile _)
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h; exact recvBucket_sessionFile _)
                      hb7
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact recvBucket_oneTimeKyberPreKey _)
                      (fun _ h => False.elim (List.not_mem_nil h))
                      hw7
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact isRecvFile_oneTimeKyberPreKey _)
                      (fun _ h => False.elim (List.not_mem_nil h))
                      (by simp only [blockDir1, h1_rem]; try rfl)
                      (by simp only [blockDir2, h2_rem]; try rfl)
                      (by simp only [blockDir3, h2_rem]; try rfl)
                      (by simp only [blockDir4, h1_rem]; try rfl)
                      (by simp only [blockDir5, h1_rem]; try rfl)
                      (by simp only [blockDir6, h6_rem]; try rfl)
                      hparty_eq
                      (fun q => by
                        have h8' : blockDir8
                            { removeOpk
                                { st with kyberOneTime := st.kyberOneTime.map (fun (i, k) =>
                                    if i = m.kpkId then (i, none) else (i, k)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, gs) } =
                            ((st.kyberOneTime.map (fun (i, a) =>
                              if i = m.kpkId then (i, none) else (i, a))).map (fun (i, a) =>
                              (oneTimeKyberPreKeyFile i,
                                match a with
                                | some kv => kyberRecordBytes i kv
                                | none => []))) := by
                          simp only [blockDir8, h8_rem]; try rfl
                        rw [h8']
                        exact find?_map_update oneTimeKyberPreKeyFile_inj hm_kot
                          (fun i a => match a with
                            | some kv => kyberRecordBytes i kv | none => [])
                          none [] rfl q)
                      (fun q => by
                        have h9' : blockDir9
                            { removeOpk
                                { st with kyberOneTime := st.kyberOneTime.map (fun (i, k) =>
                                    if i = m.kpkId then (i, none) else (i, k)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, gs) } =
                            blockDir9 st := by
                          simp only [blockDir9, h9_rem]; try rfl
                        rw [h9', List.append_nil]
                        exact find?_self_double _ q)
                  · dsimp only
                    obtain ⟨_, _, _, _, _, hnd_klr⟩ := hwf
                    have hm_klr : (m.kpkId, (k2, seen)) ∈ st.kyberLastResort :=
                      mem_of_lookup_eq_some hklr2
                    have huniq_seen : ∀ {l : List (BitVec 32 × PqKyberKey ×
                        List (BitVec 32 × List.Vector (BitVec 8) 32))},
                        (l.map Prod.fst).Nodup →
                        (m.kpkId, (k2, seen)) ∈ l →
                        ∀ {k s}, (m.kpkId, (k, s)) ∈ l → s = seen := by
                      intro l hnd hm1 k s hm2
                      induction l with
                      | nil => nomatch hm1
                      | cons hd tl ih =>
                        obtain ⟨hnot, hnd_tl⟩ := List.nodup_cons.mp hnd
                        rcases List.mem_cons.mp hm1 with rfl | hm1' <;>
                          rcases List.mem_cons.mp hm2 with h2 | hm2'
                        · exact (Prod.mk.inj (Prod.mk.inj h2).2).2
                        · exact False.elim (hnot (List.mem_map.mpr ⟨_, hm2', rfl⟩))
                        · subst h2; exact False.elim (hnot (List.mem_map.mpr ⟨_, hm1', rfl⟩))
                        · exact ih hnd_tl hm1' hm2'
                    have hklr_map_eq :
                        st.kyberLastResort.map (fun (i, k, s) =>
                          if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s)) =
                        st.kyberLastResort.map (fun (i, k, s) =>
                          if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                          else (i, k, s)) := by
                      refine List.map_congr_left fun ⟨i, k, s⟩ hmem => ?_
                      dsimp only
                      by_cases hi : i = m.kpkId
                      · subst hi
                        rw [huniq_seen hnd_klr hm_klr hmem]
                      · simp only [hi, ↓reduceIte]
                    rw [hklr_map_eq] at heq7_fn ⊢
                    obtain ⟨hbk_str, hbk_asc⟩ := baseKeys_path_eq m.kpkId
                    have hw := namedWrites_of_dirs st.party.other
                      (⟨⟨m.idPub⟩⟩ : IdentityKey).serialize
                      (encodeRecordUnderExtras (fun _ => x) gs)
                      StoresGhost.opened.kyber.oneTime
                      (StoresGhost.opened.kyber.lastResort.put (baseKeysName m.kpkId)
                        (baseKeysBytes (seen ++ [(m.spkId, m.baseKey)])))
                      otDir
                      (w8 := [])
                      (w9 := [(baseKeysFile m.kpkId, baseKeysBytes (seen ++ [(m.spkId, m.baseKey)]))])
                      (w7 := w7)
                      ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
                      ⟨fun pw hpw bt hbt => by
                         change pw ∈ ((DirGhost.new _).put _ _).writes at hpw
                         rw [new_put_writes, List.mem_singleton] at hpw
                         subst hpw; exact hbk_asc bt hbt,
                       by change ((DirGhost.new _).put _ _).writes.map _ = _
                          rw [new_put_writes, List.map_cons, List.map_nil, hbk_str]⟩
                      hot_wr
                    rw [hw]
                    have hparty_eq : ∀ q,
                        (blockDir7 W st ++ w7).reverse.find? (fun u => u.1 == q) =
                          (blockDir7 W st ++ blockDir7 W
                            { removeOpk
                                { st with kyberLastResort := st.kyberLastResort.map (fun (i, k, s) =>
                                    if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                                    else (i, k, s)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, gs) }).reverse.find?
                            (fun u => u.1 == q) := by
                      intro q
                      have hsame_ot :
                          (removeOpk
                            { st with kyberLastResort := st.kyberLastResort.map (fun (i, k, s) =>
                                if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                                else (i, k, s)) } m).oneTime =
                          (removeOpk st m).oneTime := by
                        unfold removeOpk; cases m.opkId <;> rfl
                      exact heq7_fn hsame_ot rfl q
                    have h8_rem : ∀ st0 : PqParty,
                        (removeOpk st0 m).kyberOneTime = st0.kyberOneTime := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h9_rem : ∀ st0 : PqParty,
                        (removeOpk st0 m).kyberLastResort = st0.kyberLastResort := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h1_rem : ∀ st0 : PqParty, (removeOpk st0 m).party = st0.party := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h2_rem : ∀ st0 : PqParty, (removeOpk st0 m).me = st0.me := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    have h6_rem : ∀ st0 : PqParty, (removeOpk st0 m).signed = st0.signed := by
                      intro st0; unfold removeOpk; cases m.opkId <;> rfl
                    exact filesOf_commit_master W st _ (wirePrekey :: m.bytes) rc _ rfl
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h; exact recvBucket_identityFile _)
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h; exact recvBucket_sessionFile _)
                      hb7
                      (fun _ h => False.elim (List.not_mem_nil h))
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact recvBucket_baseKeysFile _)
                      hw7
                      (fun _ h => False.elim (List.not_mem_nil h))
                      (fun _ h => by
                        rw [List.mem_singleton] at h; subst h
                        exact isRecvFile_baseKeysFile _)
                      (by simp only [blockDir1, h1_rem]; try rfl)
                      (by simp only [blockDir2, h2_rem]; try rfl)
                      (by simp only [blockDir3, h2_rem]; try rfl)
                      (by simp only [blockDir4, h1_rem]; try rfl)
                      (by simp only [blockDir5, h1_rem]; try rfl)
                      (by simp only [blockDir6, h6_rem]; try rfl)
                      hparty_eq
                      (fun q => by
                        have h8' : blockDir8
                            { removeOpk
                                { st with kyberLastResort := st.kyberLastResort.map (fun (i, k, s) =>
                                    if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                                    else (i, k, s)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, gs) } =
                            blockDir8 st := by
                          simp only [blockDir8, h8_rem]; try rfl
                        rw [h8', List.append_nil]
                        exact find?_self_double _ q)
                      (fun q => by
                        have h9' : blockDir9
                            { removeOpk
                                { st with kyberLastResort := st.kyberLastResort.map (fun (i, k, s) =>
                                    if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                                    else (i, k, s)) } m with
                              peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, gs) } =
                            (((st.kyberLastResort.map (fun (i, k, s) =>
                              if i = m.kpkId then (i, k, seen ++ [(m.spkId, m.baseKey)])
                              else (i, k, s))).map
                              (fun (i, k, s) =>
                              [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
                               (baseKeysFile i, baseKeysBytes s)])).flatten) := by
                          simp only [blockDir9, h9_rem]; try rfl
                        rw [h9']
                        exact find?_lr_update hm_klr q)

end CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
