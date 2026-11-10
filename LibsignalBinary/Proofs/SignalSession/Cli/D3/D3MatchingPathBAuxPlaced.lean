/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BinaryOomSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3ParseRejectPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeTop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.HsOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperState
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Common
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCommit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge

/-!
# Matching-Session Path-B Pure Model, Store Invariants, and `decPkDef` Bridges

Domain preconditions (`DecPkOkPathB`), pure state-transition model (`pqRecvMatchingModel`),
store-kit entry invariants, Path-B `decPkDef` agreement lemmas, poll entry unpack, and
untrusted-identity trap branch for arbitrary wire payloads parsing via `Pksm.pksmParse`
under a matching current session.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr hiding utf8
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Pure `DecPkOkPathB`, `pqSessionOf`, and `pqRecvMatchingModel` Bridges -/

/-- File-domain precondition for the matching-session Path-B branch of `decrypt_prekey`:
`peer` and `me` are domain party addresses, `Slots.loadRec` loads a current session matching `pm`,
and the store files opened before closure entry satisfy the length and canonicality bounds. -/
structure DecPkOkPathB (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop where
  party : ∃ P : Party, peer = RunRefine.addrValE P.other ∧ me = RunRefine.addrValE P
  loadedMatch : ∃ s : Session (List (BitVec 8)),
    Slots.loadRec Scope F peer = .ok (some ⟨some s⟩) ∧ SessMatchesPm s pm
  keyPairLt : ∀ bs,
    StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "identity-key-pair") = .ok bs →
    bs.length < 2 ^ 32
  preKeysWf : PreKeyFilesWf W F
  baseKeysLt : ∀ i bs,
    StoresGhost.opened.kyber.lastResort.get cliIo.rd F (baseKeysName i) = .ok bs →
    bs.length < 2 ^ 32

/-- Pure state-transition model for matching-session Path-B pre-key `recv` directly in terms of
`(x, g)` and the parsed `PreKeySignalMessage` `pm`. -/
noncomputable abbrev pqRecvMatchingModel := d3PqRecvMatchingModel

/-- `DecPkOkPathB` holds on `pqRecvInputs W st (wirePrekey :: body) rc` whenever
`PqxdhPartyInSpecDomain W st`, `st.session = some (x, g)`, and `SessMatchesPm (pqSessionOf x g) pm`. -/
theorem decPkOkPathB_pqRecv (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hmatch : SessMatchesPm (pqSessionOf x g) pm) :
    DecPkOkPathB W Scope
      (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm := by
  refine ⟨⟨st.party, rfl, rfl⟩, ⟨pqSessionOf x g, ?_, hmatch⟩,
    DecPkS0.keyPairLt_pqRecv W st _ rc hwf,
    ⟨DecPkS0.signedWf_pqRecv W st _ rc, DecPkS0.oneTimeWf_pqRecv W st _ rc,
      DecPkS0.kyberOneTimeWf_pqRecv W st _ rc, DecPkS0.kyberLastResortWf_pqRecv W st _ rc⟩,
    DecPkS0.baseKeysLt_pqRecv W st _ rc hwf⟩
  rw [DecPkS0.loadRec_pqRecv_eq hinj hcov st (wirePrekey :: body) rc hwf, hsess]; rfl

/-- `RunHsOk S` holds on `pqRecvInputs W st (wirePrekey :: body) rc` for arbitrary `body` parsing
via `Pksm.pksmParse body = some pm` when `st.session = some (x, g)` matches `pm`. -/
theorem runHsOk_pqRecv_matchingPathB (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hdec : ∀ F peer me pm, DecPkOkPathB W Scope F peer me pm → S.decPkOk F peer me pm)
    (hpksm : S.pksmParse = Pksm.pksmParse)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hparse : Pksm.pksmParse body = some pm)
    (hmatch : SessMatchesPm (pqSessionOf x g) pm) :
    RunHsOk S (pqRecvInputs W st (wirePrekey :: body) rc) := by
  have ha : (pqRecvInputs W st (wirePrekey :: body) rc).argv =
      (Cmd.recv (partyAddress st.party.other)).argv := rfl
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ hp; rw [ha, RunRefine.parseArgs_recv] at hp; cases hp
  · intro _ _ _ rest pm' hp hown had hin hparse'
    rw [ha, RunRefine.parseArgs_recv] at hp; cases hp
    rw [RunRefine.ownAddr_pqRecv] at hown; cases hown
    rw [RunRefine.addrParse_textBytes] at had; cases had
    have hstdin : (pqRecvInputs W st (wirePrekey :: body) rc).stdin = 3#8 :: body := rfl
    rw [hstdin] at hin; injection hin with _ hrest; subst hrest
    rw [hpksm, hparse] at hparse'; injection hparse' with hpm; subst hpm
    exact hdec _ _ _ _ (decPkOkPathB_pqRecv W Scope hinj hcov st x g body pm rc hwf hsess hmatch)

/-- `observe` of `runAns S` on `pqRecvInputs W st (wirePrekey :: body) rc` equals
`pqxdhExpectedOutcome W ... (pqRecvMatchingModel W st x g pm rc)` for arbitrary `body` parsing to `pm`
under a matching current session `st.session = some (x, g)`. -/
theorem observe_runAns_pqRecv_matchingPathB (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS : S.decryptPrekey = decPkDef X W Scope) (hpksm : S.pksmParse = Pksm.pksmParse)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hparse : Pksm.pksmParse body = some pm) (hmatch : SessMatchesPm (pqSessionOf x g) pm) :
    observe (pqRecvInputs W st (wirePrekey :: body) rc).files
      (runAns S (pqRecvInputs W st (wirePrekey :: body) rc)) =
    pqxdhExpectedOutcome W (pqRecvInputs W st (wirePrekey :: body) rc)
      (pqRecvMatchingModel W st x g pm rc) := by
  rw [RunRefine.runAns_pqRecvPrekey_eq, hpksm, hparse, hS]; dsimp only
  have hpeer_id := DecPkS0.idPeer_pqRecv W st (wirePrekey :: body) rc
  have hload := DecPkS0.loadRec_pqRecv_eq hinj hcov st (wirePrekey :: body) rc hwf
  have hp_eq : initParty (RunRefine.addrValE st.party.other) = st.party := InitS0.initParty_eq st.party
  have hcoins : pkRecvCoins (HMAC.keyToBytes32 rc) = rc := DecPkS0.pkRecvCoins_keyToBytes32 rc
  have htrust : StoresGhost.opened.identity.trusted cliIo.rd
      (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (RunRefine.addrValE st.party.other) pm.identityKey = .ok (st.trusts pm.identityKey) := by
    unfold IdGhost.trusted PqParty.trusts; rw [hpeer_id]; cases st.peerId <;> rfl
  have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd
      (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (RunRefine.addrValE st.party.other) pm.identityKey =
      { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put
          (RunRefine.addrValE st.party.other).name pm.identityKey.serialize } := by
    unfold IdGhost.saveUpd; rw [hpeer_id]
  rcases g with ⟨gp, gs0, gep, gce⟩
  have hg_party : gp = st.party := (hwf.1 x ⟨gp, gs0, gep, gce⟩ hsess).2.1
  subst hg_party
  unfold decPkDef pqRecvMatchingModel d3PqRecvMatchingModel pqxdhExpectedOutcome; dsimp only
  rw [hload, hsess, htrust, hp_eq, hcoins]
  cases ht : st.trusts pm.identityKey with
  | false => rfl
  | true =>
    rw [show (!true) = false from rfl, ite_eq_right (c := false = true) Bool.noConfusion]
    dsimp only [Option.map_some, Option.bind_some, Record.toRecord, RecordX.extrasOf,
      RecordX.toSessionExtras]
    have hmatch' : SessMatchesPm
        { state := gs0
          pendingPreKey := if gs0.pendingPreKey then some x.pending else none
          pendingKyberPreKey := if gs0.pendingPreKey then x.kyber else none
          localRegistrationId := x.localRegistrationId
          remoteRegistrationId := x.remoteRegistrationId
          aliceBaseKey := x.aliceBaseKey } pm := hmatch
    rw [ite_eq_left hmatch']
    by_cases hrem : gs0.remoteIdentity ≠ some pm.identityKey
    · rw [ite_eq_left hrem, ite_eq_left hrem]; rfl
    · rw [ite_eq_right hrem, ite_eq_right hrem]
      cases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs st.party) pm.message .preKey rc gs0 with
      | mk res st' =>
        cases res with
        | error err => cases err <;> rfl
        | ok pt =>
          dsimp only
          have hpend := (SessionState.tryDecryptFromRecord_ok W.C (pqxdhSpqrSession W) _ pm.message .preKey rc hdec).1
          have hclr := DecPkS0.encodeRecord_cleared_eq_encodeRecordX x ⟨st.party, gs0, gep, gce⟩ st' hpend
          dsimp only [Record.toRecord, RecordX.extrasOf, RecordX.toSessionExtras] at hclr
          rw [hsave, hclr]
          dsimp only [finish, Option.map_some, observe]
          refine congrArg (Outcome.exited 0 pt) ?_
          have hw := DecPkS0.namedWrites_of_dirs st.party.other pm.identityKey.serialize
            (encodeRecordUnderExtras (fun _ => x) { party := st.party, session := st', epoch := gep, chainEpochs := gce })
            StoresGhost.opened.kyber.oneTime StoresGhost.opened.kyber.lastResort StoresGhost.opened.oneTime
            (w8 := []) (w9 := []) (w7 := [])
            ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
            ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
            ⟨fun _ h => False.elim (List.not_mem_nil h), rfl⟩
          rw [hw]
          exact DecPkS0.filesOf_commit_master W st _ (wirePrekey :: body) rc _ rfl
            (fun _ h => by rw [List.mem_singleton] at h; subst h; exact DecPkS0.recvBucket_identityFile _)
            (fun _ h => by rw [List.mem_singleton] at h; subst h; exact DecPkS0.recvBucket_sessionFile _)
            (fun _ h => False.elim (List.not_mem_nil h)) (fun _ h => False.elim (List.not_mem_nil h))
            (fun _ h => False.elim (List.not_mem_nil h)) (fun _ h => False.elim (List.not_mem_nil h))
            (fun _ h => False.elim (List.not_mem_nil h)) (fun _ h => False.elim (List.not_mem_nil h))
            rfl rfl rfl rfl rfl rfl
            (fun q => by rw [List.append_nil]; exact DecPkS0.find?_self_double _ q)
            (fun q => by rw [List.append_nil]; exact DecPkS0.find?_self_double _ q)
            (fun q => by rw [List.append_nil]; exact DecPkS0.find?_self_double _ q)

/-! ## 2. Poll Store Invariants and Path-B `decPkDef` Lemmas under `DecPkOkPathB` -/

theorem cliIdOwnInv_opened_pathB {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOkPathB W Scope F peer me pm) :
    Poll.CliIdOwnInv cliIo.rd F cliWrOk StoresGhost.opened.identity.own where
  ownPathLt := show (0 : Nat) < 2 ^ 32 by decide
  kpPathOk := cliWrOk_ownFile (.tail _ (.head _))
  regPathOk := cliWrOk_ownFile (.tail _ (.tail _ (.head _)))
  kpSizeOk := hd.keyPairLt

theorem cliPkInv_opened_pathB {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOkPathB W Scope F peer me pm) (pid : BitVec 32) :
    KitInst.CliPkInv cliIo.rd F cliWrOk pid StoresGhost.opened.oneTime where
  nameOk := Poll.pkNameOk_opened_oneTime pid
  sizeOk := fun bs hget => by
    rcases hd.preKeysWf.oneTime pid bs hget with rfl | ⟨sk, rfl⟩
    · decide
    · exact Poll.oneTimeRecordBytes_length_lt W.C pid sk
  oneLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩

theorem cliSpkInv_opened_pathB {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOkPathB W Scope F peer me pm) (sid : BitVec 32) :
    KitInst.CliSpkInv cliIo.rd F cliWrOk sid StoresGhost.opened.signed where
  nameOk := Poll.pkNameOk_opened_signed sid
  sizeOk := fun bs hget => by
    rcases hd.preKeysWf.signed sid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact Poll.signedRecordBytes_length_lt W.C sid k

theorem cliKpkInvFull_opened_pathB {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOkPathB W Scope F peer me pm) (kid ksid : BitVec 32) (kbk : PublicKey) :
    Poll.CliKpkInvFull cliIo.rd F cliWrOk kid ksid kbk StoresGhost.opened.kyber where
  markInv := {
    nameOk := Poll.pkNameOk_opened_kyberOneTime kid
    baseOk := Poll.kpkBaseKeysOk_opened kid
    seenOk := fun bs hget _ _ => hd.baseKeysLt kid bs hget
    oneLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩
    lastLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩ }
  lastNameOk := Poll.pkNameOk_opened_kyberLastResort kid
  oneSizeOk := fun bs hget => by
    rcases hd.preKeysWf.kyberOneTime kid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact Poll.kyberRecordBytes_length_lt kid k
  lastSizeOk := fun bs hget => by
    rcases hd.preKeysWf.kyberLastResort kid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact Poll.kyberRecordBytes_length_lt kid k

theorem storesAt_opened_entails_cliPollStoresKitsAt_pathB {A : RustAlloc} (b : BitVec 64)
    {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : Poll.DpKitStk) (a : BitVec 64)
    (hsub : ∀ r, Scope r → Slots.scopeIn r) (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOkPathB W Scope F peer.val me.val pm) :
    storesAt A a StoresGhost.opened ⊢
      Poll.cliPollStoresKitsAt A b F Slots.scopeKit peer pid sid kid kbk σ a StoresGhost.opened :=
  Poll.storesAt_entails_cliPollStoresKitsAt b σ a StoresGhost.opened
    (Poll.cliSessInv_opened_scopeKit hsub hf) (cliIdOwnInv_opened_pathB hd)
    (Poll.cliIdInv_opened_peer hf) (cliPkInv_opened_pathB hd pid)
    (cliSpkInv_opened_pathB hd sid) (cliKpkInvFull_opened_pathB hd kid sid kbk)

theorem serializeAddresses_eq_expectedAddrs_pathB {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    (hd : DecPkOkPathB W Scope F peer.val me.val pm) :
    serializeAddresses (serviceIdParse uuidTryParse) peer me =
      (pqxdhSessionParams W).expectedAddrs (initParty peer.val) := by
  obtain ⟨P, hpeer, hme⟩ := hd.party
  have hp : initParty peer.val = P := by unfold initParty; rw [hpeer]; exact InitS0.initParty_eq P
  have hconv : serializeAddresses (serviceIdParse uuidTryParse) peer me =
      serializeAddrVals (serviceIdParse uuidTryParse) peer.val me.val := rfl
  rw [hconv, hp, hpeer, hme, Agree.serializeAddrVals_expectedAddrs_pq]

/-- Pure `SessionState.tryDecryptWithState` model evaluation at SPQR v1 (`spqrV1 C.F K`) and
`.preKey` message type. -/
abbrev genP3S5Model (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (rem loc : AddrGhost) (msg : SignalMessage) (rest : List (BitVec 8))
    (st : SessionState (List (BitVec 8))) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState (List (BitVec 8)) :=
  Mut.exec (SessionState.tryDecryptWithState C (LibsignalSpqrV1.spqrV1 C.F K).spqr
    (serializeAddresses (serviceIdParse uuidTryParse) rem loc) msg .preKey (coinsOf rest)) st

theorem ite_pos_d3 {α : Sort _} {c : Prop} [Decidable c] {t e : α} (hc : c) :
    (if c then t else e) = t := by
  split <;> [rfl; contradiction]

theorem ite_neg_d3 {α : Sort _} {c : Prop} [Decidable c] {t e : α} (hc : ¬ c) :
    (if c then t else e) = e := by
  split <;> [contradiction; rfl]

private theorem take_append_replicate_le_d3 {α : Type} (b : α) :
    ∀ (c : List α) (k n : Nat), k ≤ n →
      (c ++ List.replicate n b).take k = c.take k ++ List.replicate (k - c.length) b
  | [], k, n, hkn => by simp [Nat.min_eq_left hkn]
  | _ :: _, 0, _, _ => by simp
  | x :: xs, k + 1, n, hkn => by
    have hk : k ≤ n := Nat.le_of_succ_le hkn
    simp only [List.cons_append, List.take_succ_cons, List.length_cons,
      Nat.succ_sub_succ_eq_sub, take_append_replicate_le_d3 b xs k n hk]

theorem coinsOf_eq_pkRecvCoins_d3 (c : List (BitVec 8)) :
    LibsignalTripleRatchetRepr.coinsOf c = pkRecvCoins c := by
  unfold LibsignalTripleRatchetRepr.coinsOf pkRecvCoins
  rw [take_append_replicate_le_d3 0#8 c 32 32 (Nat.le_refl 32)]

theorem version_eq_zeroExtend_iff_d3 (st : SessionState (List (BitVec 8))) (msg : SignalMessage) :
    st.version.toNat = msg.messageVersion.toNat ↔
      st.version = msg.messageVersion.zeroExtend 32 := by
  have hz : (msg.messageVersion.zeroExtend 32).toNat = msg.messageVersion.toNat := by
    simp [BitVec.toNat_setWidth]; omega
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (h.trans hz.symm)
  · intro h; exact (congrArg BitVec.toNat h).trans hz

theorem recordError_eq_panic_iff_d3 (msgType : MessageType) (e : SignalProtocolError) :
    SessionState.recordError msgType e = .panic ↔ e = .panic :=
  match e with
  | .invalidSessionStructure _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .invalidKeyAgreement => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .duplicatedMessage _ _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .invalidMessage _ _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .invalidState => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .ciphertextMessageTooShort _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .legacyCiphertextVersion _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .unrecognizedCiphertextVersion _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .invalidProtobufEncoding => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .noKeyTypeIdentifier => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .badKeyType _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .badKeyLength _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .panic => Iff.rfl

private theorem stripPq_bounded_of_parts_d3 {s : Session (List (BitVec 8))}
    (hseeds : SeedsLen32 s.state)
    (hrc : s.state.receiverChains.length ≤ maxReceiverChains)
    (hrep : CryptoVerification.E2E.Reach.SessRepr s.state)
    (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p → p.timestamp = 0)
    (hk : ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length = 1569)
    (ha : s.aliceBaseKey = [] ∨ s.aliceBaseKey.length = 33) :
    CryptoVerification.E2E.RecordX.DeserializeScopeBounded ⟨some (Slots.PqValid.stripPq s)⟩ := by
  have hscP : CryptoVerification.E2E.RecordX.SessionScopeP (Slots.PqValid.stripPq s) :=
    ⟨hrc, hp, hk, ha⟩
  refine ⟨⟨?_, ?_, ?_⟩, Slots.PqValid.stripPq s, rfl,
    CryptoVerification.E2E.RecordX.sessionScopeBounded_of_sessionScopeP hscP⟩
  · intro t ht; injection ht with ht; subst ht
    refine ⟨hseeds, Nat.lt_of_le_of_lt hrc (by decide), fun k hk' => ?_⟩
    rw [hk k hk']; decide
  · intro t ht; injection ht with ht; subst ht; rfl
  · intro t ht; injection ht with ht; subst ht
    refine ⟨hrep.1, hrep.2, hwf, ?_⟩
    dsimp only [Slots.PqValid.stripPq]
    rcases ha with ha | ha <;> rw [ha] <;> decide

theorem tryDecryptFromRecord_preKey_recOk_of_scopeIn_d3
    {W : PEParams} {expected : Option (List (BitVec 8))}
    {msg : SignalMessage} {rc : BitVec 256}
    {ses : Session (List (BitVec 8))} {st' : SessionState (List (BitVec 8))}
    {pt : List (BitVec 8)}
    (hIn : Slots.scopeIn ⟨some ses⟩)
    (hTry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      expected msg .preKey rc ses.state = (.ok pt, st')) :
    let ses' : Session (List (BitVec 8)) :=
      { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }
    Slots.scopeKit ⟨some ses'⟩ ∧ (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 := by
  have hTryV1 : SessionState.tryDecryptFromRecord W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      expected msg .preKey rc ses.state = (.ok pt, st') := hTry
  obtain ⟨⟨hInP, hPqIn, hRep⟩, ses₀, hCur₀, hSessSc⟩ := hIn
  injection hCur₀ with hses; subst hses
  obtain ⟨hSeeds, _, _⟩ := hInP ses rfl
  have hPqSes : Slots.PqValid.PqInV1 ses.state.pqRatchetState := hPqIn ses rfl
  obtain ⟨hRep1, hRep2, _, _⟩ := hRep ses rfl
  obtain ⟨hRC, _, _, hAbk⟩ := hSessSc
  obtain ⟨hSeeds', hRC', _, _, key, hRecv⟩ :=
    CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      expected msg .preKey rc ses.state st' pt hSeeds hRC hTryV1
  have hRep' : CryptoVerification.E2E.Reach.SessRepr st' :=
    CryptoVerification.E2E.V1.sessRepr_tryDecryptFromRecord_gen W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      expected msg .preKey rc ses.state st' pt ⟨hRep1, hRep2⟩ hTryV1
  have hPqOut : Slots.PqValid.PqOutV1 st'.pqRatchetState :=
    (Slots.PqValid.pqStep_spqrV1 W.C.F W.Q.K).recv ses.state.pqRatchetState msg.pqRatchet
      st'.pqRatchetState key hPqSes hRecv
  have hPqLt : st'.pqRatchetState.length < 2 ^ 32 :=
    (Slots.PqValid.pqStep_spqrV1 W.C.F W.Q.K).out_bound st'.pqRatchetState hPqOut
  have hPendFalse : st'.pendingPreKey = false :=
    (SessionState.tryDecryptFromRecord_ok W.C (pqxdhSpqrSession W) expected msg .preKey rc hTry).1
  let ses' : Session (List (BitVec 8)) :=
    { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  have hWf' : ses'.Wf := by unfold Session.Wf; dsimp only [ses']; exact hPendFalse
  have hPendTs' : ∀ p, ses'.pendingPreKey = some p → p.timestamp = 0 := fun _ hp => by cases hp
  have hKyber' : ∀ k, ses'.pendingKyberPreKey = some k → k.ciphertext.length = 1569 :=
    fun _ hk => by cases hk
  have hScP' : CryptoVerification.E2E.RecordX.SessionScopeP ses' :=
    ⟨hRC', hPendTs', hKyber', hAbk⟩
  have hKit' : Slots.scopeKit ⟨some ses'⟩ := by
    refine ⟨⟨?_, ?_, ?_⟩, ses', rfl, hScP'⟩
    · intro s hs; injection hs with hs; subst hs
      exact ⟨hSeeds', Nat.lt_of_le_of_lt hRC' (by decide), fun _ hk => by cases hk⟩
    · intro s hs; injection hs with hs; subst hs; exact hPqLt
    · intro s hs; injection hs with hs; subst hs
      refine ⟨hRep'.1, hRep'.2, hWf', ?_⟩
      dsimp only [ses']; rcases hAbk with ha | ha <;> rw [ha] <;> decide
  have hBdd' : CryptoVerification.E2E.RecordX.DeserializeScopeBounded
      ⟨some (Slots.PqValid.stripPq ses')⟩ :=
    stripPq_bounded_of_parts_d3 hSeeds' hRC' hRep' hWf' hPendTs' hKyber' hAbk
  exact ⟨hKit', Slots.PqValid.encodeRecord_length_lt_32_of_stripPq_bounded hBdd' hPqOut⟩

theorem scope_of_loadRec_some_d3 {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal} {r : SessionRecord (List (BitVec 8))}
    (hf : Slots.FilesOkPeer Scope F peer)
    (hload : Slots.loadRec Scope F peer = .ok (some r)) :
    Scope r := by
  have hans := Slots.sessLoadAns_loadRec hf
  rw [hload] at hans
  rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with _ | bs
  · rw [hget] at hans; cases hans
  · cases bs with
    | nil => rw [hget] at hans; cases hans
    | cons b bs' =>
      rw [hget] at hans
      obtain ⟨r', hr', _, hsc⟩ := hans
      injection hr' with hr'; injection hr' with hr'; subst hr'
      exact hsc

theorem tryDecryptFromRecord_preKey_ver_eq_pathB {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {st : SessionState (List (BitVec 8))}
    (hd : DecPkOkPathB W Scope F peer.val me.val pm)
    (hver : st.version = pm.message.messageVersion.zeroExtend 32) :
    SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) st =
    match genP3S5Model W.C W.Q.K peer me pm.message coins st with
    | (.ok ptext, updated) => (.ok ptext, updated)
    | (.error e, _) => (.error (SessionState.recordError .preKey e), st) := by
  rw [← Agree.tryDecrypt_spqrV1W_eq_spqrPq, ← serializeAddresses_eq_expectedAddrs_pathB hd,
    ← coinsOf_eq_pkRecvCoins_d3 coins]
  have hspqr : (pqxdhSpqrModel W).spqr = (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr := rfl
  rw [hspqr]; unfold SessionState.tryDecryptFromRecord genP3S5Model
  rw [ite_neg_d3 (not_not.mpr ((version_eq_zeroExtend_iff_d3 st pm.message).mpr hver))]
  rcases (SessionState.tryDecryptWithState W.C
    (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
    (serializeAddresses (serviceIdParse uuidTryParse) peer me) pm.message .preKey
    (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)).exec st with ⟨_ | _, _⟩ <;> rfl

theorem pathB_scopeIn_and_match_of_decPkOkPathB {A : RustAlloc} {b : BitVec 64}
    {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    {s1 s2 s3 s4 : Nat} {r : SessionRecord (List (BitVec 8))}
    {s : Session (List (BitVec 8))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOkPathB W Scope F peer.val me.val pm)
    (hload_rel :
      (KitInst.cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit peer s1 s2 s3 s4).loadRel
        StoresGhost.opened.sessions peer.val (.ok (some r)))
    (hcur : r.currentSession = some s) :
    Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩) ∧ r = ⟨some s⟩ ∧ Slots.scopeIn ⟨some s⟩ ∧
      SessMatchesPm s pm ∧ SeedsLen32 s.state ∧ s.state.receiverChains.length < 2 ^ 32 ∧
      s.state.pqRatchetState.length < 2 ^ 32 := by
  have hr_eq : r = ⟨some s⟩ := by cases r; simpa using hcur
  subst hr_eq
  have hloadK : (.ok (some ⟨some s⟩)) = Slots.loadRec Slots.scopeKit F peer.val :=
    Slots.cliSessLoadRel_eq_loadRec hinjK hload_rel
  have hloadS : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩) :=
    (Poll.loadRec_scopeKit_eq hinjK hsub hf).symm.trans hloadK.symm
  obtain ⟨s₀, hload₀, hMatch₀⟩ := hd.loadedMatch
  rw [hloadS] at hload₀
  injection hload₀ with h1; injection h1 with h2; injection h2 with hs_eq; injection hs_eq with hs_eq'
  subst hs_eq'
  have hIn : Slots.scopeIn ⟨some s⟩ := hsub _ (scope_of_loadRec_some_d3 hf hloadS)
  obtain ⟨hSeeds, hRC, _⟩ := hIn.1.1 s rfl
  exact ⟨hloadS, rfl, hIn, hMatch₀, hSeeds, hRC,
    Slots.scopeKit_pqrState_lt (Slots.scopeKit_of_scopeIn hIn) s rfl⟩

theorem decPkDef_pathB_panic_pathB (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))} (hd : DecPkOkPathB W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm) (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (hpan : (genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .error .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = none := by
  dsimp only [decPkDef]; rw [hload]; dsimp only [Option.bind_some]; rw [htrust]; dsimp only
  rw [ite_pos_d3 hmatch, ite_neg_d3 (not_not.mpr hrem), tryDecryptFromRecord_preKey_ver_eq_pathB hd hver]
  rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins s.state with ⟨res, st'⟩
  rw [hm] at hpan; dsimp only at hpan; subst hpan; rfl

theorem decPkDef_pathB_err_pathB (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))} {e : SignalProtocolError}
    (hd : DecPkOkPathB W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm) (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (herr : (genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .error e) (hne : e ≠ .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = some none := by
  dsimp only [decPkDef]; rw [hload]; dsimp only [Option.bind_some]; rw [htrust]; dsimp only
  rw [ite_pos_d3 hmatch, ite_neg_d3 (not_not.mpr hrem), tryDecryptFromRecord_preKey_ver_eq_pathB hd hver]
  rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins s.state with ⟨res, st'⟩
  rw [hm] at herr; dsimp only at herr; subst herr; dsimp only
  have hrec_ne := mt (recordError_eq_panic_iff_d3 .preKey e).mp hne
  cases hr : SessionState.recordError .preKey e <;> first | exact absurd hr hrec_ne | rfl

theorem decPkDef_pathB_ok_pathB (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))} {pt : List (BitVec 8)}
    (hf : Slots.FilesOkPeer Scope F peer.val) (hd : DecPkOkPathB W Scope F peer.val me.val pm)
    (hIn : Slots.scopeIn ⟨some s⟩) (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm) (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .ok pt) :
    let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins s.state).2
    let ses' : Session (List (BitVec 8)) :=
      { s with state := st', pendingPreKey := none, pendingKyberPreKey := none }
    let g := StoresGhost.opened
    let g' : StoresGhost := { g with
      identity := g.identity.saveUpd cliIo.rd F peer.val pm.identityKey
      sessions := g.sessions.put (Cli.addressText peer.val) (Record.encodeRecord ⟨some ses'⟩) }
    decPkDef X W Scope F peer.val me.val pm coins = some (some (g', pt)) ∧
      (∀ pw ∈ g'.writes, cliWrOk pw.1) ∧ Slots.scopeKit ⟨some ses'⟩ ∧
      (Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 := by
  intro st' ses' g g'
  have hTry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) s.state = (.ok pt, st') := by
    rw [tryDecryptFromRecord_preKey_ver_eq_pathB hd hver]; dsimp only [st']
    rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins s.state with ⟨res, st1⟩
    rw [hm] at hok; dsimp only at hok; subst hok; rfl
  have hDec : decPkDef X W Scope F peer.val me.val pm coins = some (some (g', pt)) := by
    dsimp only [decPkDef]; rw [hload]; dsimp only [Option.bind_some]; rw [htrust]; dsimp only
    rw [ite_pos_d3 hmatch, ite_neg_d3 (not_not.mpr hrem), hTry]
  have hRecOk := tryDecryptFromRecord_preKey_recOk_of_scopeIn_d3 hIn hTry
  exact ⟨hDec, Poll.storesWrOk_pathB hf, hRecOk.1, hRecOk.2⟩

/-! ## 3. Poll Entry Unpack and Untrusted-Identity Closure Branch -/

section Section2B

open ProofLib.Variant CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Bin CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt CryptoVerification.SignalSession.Cli.RunProofs.Poll

theorem distinctSid_of_decPkOkPathB {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {rem loc : AddrGhost} {pm : PreKeySignalMessage}
    (hd : DecPkOkPathB W Scope F rem.val loc.val pm) :
    DistinctSid uuidTryParse loc.name.bytes rem.name.bytes := by
  obtain ⟨P, hrem, hloc⟩ := hd.party; intro sid h1 h2
  have hsame : SameServiceId rem.val loc.val := ⟨sid, h2, h1⟩
  rw [hrem, hloc] at hsame; exact InitS0.distinctAcct_party P hsame

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem dpCxAt_entails_memRegion32_d3 (cx : BitVec 64) :
    dpCxAt cx ⊢ memRegion cx 32 := by
  unfold dpCxAt
  refine Entails.sepExists_elim fun wk => ?_
  rw [memRegion_split cx 8 24 (by decide),
      memRegion_split (cx + 8#64) 8 16 (by decide),
      memRegion_split (cx + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (Entails.refl _)))

def dpPollEntrySpatial {B : RunBudgets} {S : RunSem} (img : Obj.Image) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 : State) (R : SepProp) : SepProp :=
  memRegion y.out 48 ∗
  dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
  memRegion y.cx 32 ∗
  storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
  protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
  protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
  coinsInstalled img y.g.coinsP y.g.coins ∗
  TokenInit img ∗
  logOff img ∗
  E2E.HooksE.A0.pool ∗
  preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
  stackAt s0.sp stk' ∗ R

structure DpPollEntryPurePathB {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 : State) : Prop where
  inv : ImgCallInv img s0
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg

theorem dpPollPre_unpack_pathB
    {img : Obj.Image} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨ ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).pre y s0 ∗ R) :
    DpPollEntryPurePathB (W := W) (Scope := Scope) img stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatial img stk' y s0 R) := by
  have h1 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgs img y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗
      (memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgs img y.g) ∗ dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
              protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
              protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img ∗ logOff img ∗
              E2E.HooksE.A0.pool ∗ preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗ R))))) := by
    simpa only [Spec.inImage, dpPollSpecState, dpSlotPollKState, slotFrame, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at h1; rcases h1 with ⟨hinv, h2⟩
  rw [satisfies_pure_sepConj] at h2; rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗
          (dpCxAt y.cx ∗ (memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
            storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
            protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
            protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
            coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img ∗ logOff img ∗
            E2E.HooksE.A0.pool ∗ preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
            stackAt s0.sp stk' ∗ R))) := by convert h3 using 1; ac_rfl
  rw [satisfies_pure_sepConj] at h3'; rcases h3' with ⟨⟨hfiles, hfOk, hdOk⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4; rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Arm64.Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32_d3 y.cx)) h5
  refine ⟨⟨hinv, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk⟩, ?_⟩
  dsimp only [dpPollEntrySpatial]; convert h5_cx using 1; ac_rfl

section PlacedSection2B

open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Coins CryptoVerification.SignalSession.Coins.Placed

theorem storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB [LibsignalPlacement] {A : RustAlloc}
    {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : Poll.DpKitStk) (a : BitVec 64)
    (hsub : ∀ r, Scope r → Slots.scopeIn r) (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOkPathB W Scope F peer.val me.val pm) :
    storesAt A a StoresGhost.opened ⊢
      Poll.cliPollStoresKitsAtPlaced A F Slots.scopeKit peer pid sid kid kbk σ a StoresGhost.opened :=
  Poll.storesAt_entails_cliPollStoresKitsAtPlaced (A := A) (F0 := F) (Scope := Slots.scopeKit)
    (peer := peer) (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ a StoresGhost.opened
    (Poll.cliSessInv_opened_scopeKit hsub hf) (cliIdOwnInv_opened_pathB hd)
    (Poll.cliIdInv_opened_peer hf) (cliPkInv_opened_pathB hd pid)
    (cliSpkInv_opened_pathB hd sid) (cliKpkInvFull_opened_pathB hd kid sid kbk)

end PlacedSection2B

end Section2B

end LibsignalBinary.Proofs.SignalSession.Cli.D3
