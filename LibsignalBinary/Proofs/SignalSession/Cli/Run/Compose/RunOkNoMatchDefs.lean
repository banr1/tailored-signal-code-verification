/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOver
public import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCommit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

@[expose] public section

set_option autoImplicit false

/-!
# D2(c) `NoMatch` Observation Definitions, Domain, `CommitOk`, and Matched Agreement

Defines the 2-session `SessionRecord` encoding and CLI `Outcome` for non-matching pre-key messages
(`D2(c)`), discharges `DecPkOkD2c` and `CommitOk` unconditionally on `pqRecvInputs`, and proves
agreement of `decPkDefD2c` with `decPkDef` on empty or matching sessions:
1. `d2cRecordBytes`, `d2cObserve`, `Outcome.AgreeExceptNorm`, `ObservedExceptNorm`, and
   `fsView_raw_agreeExcept_forces_eq`.
2. `reachPq_sessionVersion` and `decPkOkD2c_pqRecv`: every reachable PQXDH session has protocol
   version `4#32`, discharging `DecPkOkD2c` and `RunHsOk` without a `PqSessionMatches` premise.
3. `decPkDefD2c_namedWrites_sub` and `commitOk_pqRecvPrekey_decPkDefD2c`: all accepting writes hit
   the five canonical party-directory file paths.
4. `pqDecryptPrekeyAgrees_decPkDefD2c`: `decPkDefD2c` agrees with `pqRecvPrekeyModel` on empty or
   matching sessions.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- Exact 2-session `SessionRecord` bytes written by libsignal on D2(c) (`NoMatch`):
field 1 holds the newly promoted PQXDH responder session `(x', gs)` and field 2 archives the
displaced current session `(x₀, g₀)` with its pending pre-key fields cleared. -/
def d2cRecordBytes (x' x₀ : RecordExtras) (gs g₀ : GhostState (List (BitVec 8))) :
    List (BitVec 8) :=
  encodeRecordUnderExtras (fun _ => x') gs ++
    E2E.Record.lenField 2 (encStateUnderExtras x₀ { g₀.session with pendingPreKey := false })

/-- Exact CLI `Outcome` of a D2(c) (`NoMatch`) pre-key `recv` run when `r` is the empty-session
responder model answer `pqRecvPrekeyModel X W { st with session := none } m rc`:
* `none`: panic/abort (`.aborted`);
* `some none`: rejection (`.exited 1 [] (filesOf i.files)`);
* `some (some (st', out))`: exit `0` with `out` on stdout and `st'`'s directory overwritten at
  `sessionFile (partyAddress peer)` by the 2-session record `d2cRecordBytes x' x₀ gs g₀`. -/
def d2cObserve (W : PEParams) (i : Inputs) (peer : Party)
    (x₀ : RecordExtras) (g₀ : GhostState (List (BitVec 8)))
    (r : Option (Option (PqParty × List (BitVec 8)))) : Outcome :=
  match r with
  | none => .aborted
  | some none => .exited 1 [] (filesOf i.files)
  | some (some (st', out)) =>
    .exited 0 out
      (filesOf ((i.files ++ encodeDir W st') ++
        match st'.session with
        | some (x', gs) => [(sessionFile (partyAddress peer), d2cRecordBytes x' x₀ gs g₀)]
        | none => []))

abbrev Outcome.AgreeExceptNorm : String → Outcome → Outcome → Prop :=
  Outcome.AgreeExcept

abbrev ObservedExceptNorm : PEParams → Inputs → String →
    Option (Option (PqParty × List (BitVec 8))) → Outcome → Prop :=
  OutcomeMatchesModelExceptPath

/-- `fsView` depends on the path string only through `Arm64.normalizePath`. -/
theorem fsView_congr_norm {fs : Arm64.FsState} {q p : String}
    (hn : Arm64.normalizePath q = Arm64.normalizePath p) :
    fsView fs q = fsView fs p := by
  unfold fsView FsState.files FsState.getEntry
  rw [hn]

/-- Why `Outcome.AgreeExcept` must compare `Arm64.normalizePath`: if `fsView fs1` and `fsView fs2`
agreed at all raw strings `q ≠ sessionFile (partyAddress P)`, evaluating at
`q := "./" ++ sessionFile (partyAddress P)` would force equality at `sessionFile (partyAddress P)`
as well, because `q ≠ p` as strings while `Arm64.normalizePath q = Arm64.normalizePath p`. -/
theorem fsView_raw_agreeExcept_forces_eq (fs1 fs2 : Arm64.FsState) (P : Party)
    (h : ∀ q, q ≠ sessionFile (partyAddress P) → fsView fs1 q = fsView fs2 q) :
    fsView fs1 (sessionFile (partyAddress P)) = fsView fs2 (sessionFile (partyAddress P)) := by
  let p := sessionFile (partyAddress P)
  let q := "./" ++ p
  have hne : q ≠ p := by
    cases P <;> decide
  have hnorm : Arm64.normalizePath q = Arm64.normalizePath p := by
    cases P <;> decide
  rw [← fsView_congr_norm (fs := fs1) hnorm, ← fsView_congr_norm (fs := fs2) hnorm]
  exact h q hne

/-- `filesOf` specialization of `fsView_raw_agreeExcept_forces_eq`. -/
theorem filesOf_raw_agreeExcept_forces_eq (L1 L2 : List (String × List (BitVec 8))) (P : Party)
    (h : ∀ q, q ≠ sessionFile (partyAddress P) → filesOf L1 q = filesOf L2 q) :
    filesOf L1 (sessionFile (partyAddress P)) = filesOf L2 (sessionFile (partyAddress P)) :=
  fsView_raw_agreeExcept_forces_eq _ _ P h

/-- `d2cRecordBytes x' x₀ gs g₀` is strictly longer than (hence distinct from)
`encodeRecordUnderExtras (fun _ => x') gs` because `lenField 2` prepends a non-empty protobuf tag+varint
header. -/
theorem d2cRecordBytes_ne_encodeRecordX (x' x₀ : RecordExtras)
    (gs g₀ : GhostState (List (BitVec 8))) :
    d2cRecordBytes x' x₀ gs g₀ ≠ encodeRecordUnderExtras (fun _ => x') gs := by
  intro heq
  have hlen := congrArg List.length heq
  unfold d2cRecordBytes E2E.Record.lenField at hlen
  have hkey : (encodeKey 2 .lengthDelimited).length = 1 := by decide
  rw [List.length_append, List.length_append, List.length_append, hkey] at hlen
  omega

end CryptoVerification.SignalSession

namespace CryptoVerification.SignalSession.Cli.RunProofs

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

/-! ## 1. `ReachablePqxdhSession` Preserves `sessionVersion = 4#32` and Discharges `DecPkOkD2c` -/

attribute [local simp] E2E.Epochs.exec_pure E2E.Epochs.exec_throw E2E.Epochs.exec_get
  E2E.Epochs.exec_set E2E.Epochs.exec_modify E2E.Epochs.exec_modifyGet E2E.Epochs.exec_liftE
  E2E.Epochs.exec_bind E2E.Epochs.exec_onRatchet

theorem tryDecryptFromRecord_sessionVersion {PQC : Type} (C : Crypto) (S : Spqr E2E.Bytes PQC)
    (expected : Option E2E.Bytes) (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState E2E.Bytes) (pt : E2E.Bytes)
    (h : SessionState.tryDecryptFromRecord C S expected m msgType coins st = (.ok pt, st')) :
    st'.sessionVersion = st.sessionVersion := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C S expected m msgType coins) st with
      ⟨res, updated⟩
    cases res with
    | error _ => simp [hd] at h
    | ok ptext =>
      rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp only [hrem, E2E.Epochs.exec_bind, E2E.Epochs.exec_modifyGet, E2E.Epochs.exec_get] at hd
        simp at hd
      · simp only [hrem, E2E.Epochs.exec_bind, E2E.Epochs.exec_modifyGet, E2E.Epochs.exec_get,
          E2E.Epochs.exec_pure] at hd
        rcases hdec : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨dres, tr'⟩
        cases dres with
        | error _ => simp [hdec] at hd
        | ok _ =>
          rw [hdec] at hd
          simp only [E2E.Epochs.exec_liftE, E2E.Epochs.exec_modify, Prod.mk.injEq,
            Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          rfl

theorem messageEncrypt_sessionVersion {PQC : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (S : Spqr E2E.Bytes PQC) (addresses : Option E2E.Bytes) (ptext : E2E.Bytes) (coins : PQC)
    (st st' : SessionState E2E.Bytes) (msg : SignalMessage)
    (h : SessionState.messageEncrypt C codec S addresses ptext coins st = (.ok msg, st')) :
    st'.sessionVersion = st.sessionVersion := by
  unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp only [E2E.Epochs.exec_bind, E2E.Epochs.exec_get, hsc] at h
    simp at h
  · simp only [hsc, E2E.Epochs.exec_bind, E2E.Epochs.exec_get, E2E.Epochs.exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, E2E.Epochs.exec_pure] at h
        unfold OutgoingTripleRatchet.encrypt at h
        simp only [E2E.Epochs.exec_bind, E2E.Epochs.exec_get] at h
        cases hpan : S.sendPanics st.pqRatchetState coins
        case true => simp [hpan] at h
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
        rcases hs : S.send st.pqRatchetState coins with _ | ⟨pq', key, pm⟩
        · simp [hs] at h
        · simp only [hs] at h
          cases hn : sc.chainKey.nextChainKey C.F with
          | error _ => simp [hn] at h
          | ok next =>
            simp only [hn, E2E.Epochs.exec_bind, E2E.Epochs.exec_liftE, E2E.Epochs.exec_set,
              E2E.Epochs.exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rfl

/-- Every reachable PQXDH session (`ReachablePqxdhSession W me x g`) has protocol version `4#32`. -/
theorem reachPq_sessionVersion {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState E2E.Bytes} (h : ReachablePqxdhSession W me x g) :
    g.session.sessionVersion = 4#32 := by
  induction h with
  | initiate X P me b t x g hi =>
    unfold initiateState at hi
    cases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
    | none => simp [hinit] at hi
    | some dkhdr =>
      rcases dkhdr with ⟨dk, _⟩
      rw [hinit] at hi; dsimp only at hi
      unfold initializeInitiatorSession at hi
      dsimp only [bind, Except.bind, pure, Except.pure] at hi
      cases hrc : rootCreateChain W.C (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (KeyPair.generate W.C (HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
      | error _ => simp [hrc] at hi
      | ok rkck =>
        rcases rkck with ⟨rk', ck'⟩
        rw [hrc] at hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨_, rfl⟩
        rfl
  | recvPrekey X P me k m rc x g pt hr =>
    unfold recvPrekeyState at hr
    cases htf : SignalMessage.tryFrom protoSignalCodec m.inner with
    | error _ => simp [htf] at hr
    | ok inner =>
      rw [htf] at hr; dsimp only at hr
      split_ifs at hr
      · simp at hr
      · cases hak : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
        | none => simp [hak] at hr
        | some dk =>
          rw [hak] at hr; dsimp only at hr
          let st0 : SessionState E2E.Bytes :=
            initializeRecipientSession (pqxdhSpqrSession W) ⟨(keyPairOf W.C me.idPriv).publicKey⟩
              ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          change (match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with
            | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none) = some (some (x, g, pt)) at hr
          rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with ⟨dres, st1⟩
          cases dres with
          | error err => rw [hdec] at hr; cases err <;> simp at hr
          | ok pt' =>
            rw [hdec] at hr
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨_, rfl, _⟩
            have hv := tryDecryptFromRecord_sessionVersion W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 st1 pt' hdec
            dsimp only
            rw [hv]
            rfl
  | @send _ _ g_s m r _ _ ih =>
    rw [E2E.Record.send_eq_afterSend]
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with ⟨eres, s⟩
    cases eres with
    | error _ => exact ih
    | ok msg =>
      dsimp only [GhostState.afterSend]
      rw [messageEncrypt_sessionVersion (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hm]
      exact ih
  | @recv _ _ g_r g'_r c rc res _ _ hrec ih =>
    rcases res with ⟨_, _, _⟩
    rw [E2E.Record.receive_eq_afterRecv] at hrec
    cases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with
    | error _ => simp [htf] at hrec
    | ok msg =>
      rw [htf] at hrec; dsimp only at hrec
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session with ⟨dres, s⟩
      cases dres with
      | error _ => simp [hd] at hrec
      | ok pt' =>
        rw [hd] at hrec
        simp only [Option.some.injEq] at hrec
        have hg' : g'_r = (g_r.afterRecv msg.senderRatchetKey msg.counter s pt').1 :=
          (Prod.mk.inj hrec).1.symm
        subst hg'
        have hv := tryDecryptFromRecord_sessionVersion (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session s pt' hd
        unfold GhostState.afterRecv
        rcases g_r.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) <;>
          exact hv.trans ih

/-- Every loaded current session on `pqRecvInputs W st c rc` under `PqxdhPartyInSpecDomain W st` has
`s.state.version = 4#32`. -/
theorem sessVer4_pqRecv (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st) :
    ∀ r s, Slots.loadRec Scope (runFiles (pqRecvInputs W st c rc))
        (RunRefine.addrValE st.party.other) = .ok (some r) →
      r.currentSession = some s → s.state.version = 4#32 := by
  intro r s hload hcur
  rw [DecPkS0.loadRec_pqRecv_eq hinj hcov st c rc hwf] at hload
  cases hs : st.session with
  | none =>
    rw [hs] at hload; cases hload
  | some xg =>
    rcases xg with ⟨x, g⟩
    rw [hs] at hload
    injection hload with hr
    injection hr with hr
    subst hr
    unfold E2E.Record.toRecord at hcur
    injection hcur with hs_eq
    subst hs_eq
    obtain ⟨⟨g₀, hreach, _, hsess⟩, _⟩ := hwf.1 x g hs
    have hv4 : g.session.sessionVersion = 4#32 := hsess ▸ reachPq_sessionVersion hreach
    unfold SessionState.version
    dsimp only
    rw [hv4]
    decide

/-- `DecPkOkD2c` holds unconditionally on `pqRecvInputs` for every `PqxdhPartyInSpecDomain W st`
and typed `PreKeyMessageFields` (with no `PqSessionMatches` premise). -/
theorem decPkOkD2c_pqRecv (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope) (st : PqParty)
    (m : PreKeyMessageFields) (i : SignalMessage) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i) :
    DecPkOkD2c W Scope (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) (pmOfE m i) :=
  ⟨⟨st.party, rfl, rfl⟩, ⟨m, i, hm, hi, rfl⟩,
    sessVer4_pqRecv W Scope hinj hcov st (wirePrekey :: m.bytes) rc hwf,
    InitS0.distinctAcct_party st.party,
    DecPkS0.keyPairLt_pqRecv W st _ rc hwf,
    DecPkS0.idPairDerived_pqRecv W st _ rc,
    ⟨DecPkS0.signedWf_pqRecv W st _ rc, DecPkS0.oneTimeWf_pqRecv W st _ rc,
      DecPkS0.kyberOneTimeWf_pqRecv W st _ rc, DecPkS0.kyberLastResortWf_pqRecv W st _ rc⟩,
    DecPkS0.baseKeysLt_pqRecv W st _ rc hwf⟩

/-- `DecPkOkD2c` at `Slots.scopeIn` from `Pksm.pksmParse m.bytes = some pm` (no `hmatch`). -/
theorem decPkDomOk_d2c_cli (W : PEParams) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (pm : PreKeySignalMessage) (hst : PqxdhPartyInSpecDomain W st) (hm : m.inner.length + 2048 < 2 ^ 32)
    (hparse : Pksm.pksmParse m.bytes = some pm) :
    DecPkOkD2c W Slots.scopeIn
      (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm := by
  obtain ⟨i, hi, rfl⟩ := pksmParse_bytes_typed hm hparse
  exact decPkOkD2c_pqRecv W Slots.scopeIn encodeInjOn_scopeIn (ratchetScopeCoversPq_scopeIn W)
    st m i rc hst hm hi

/-- `RunHsOk S` holds on `pqRecvInputs W st (wirePrekey :: m.bytes) rc` for all `PqxdhPartyInSpecDomain` states
when `S.decPkOk = DecPkOkD2c W Slots.scopeIn` and `S.pksmParse = Pksm.pksmParse`. -/
theorem runHsOk_pqRecvPrekey_d2c {S : RunSem} {W : PEParams}
    (hdecOk : S.decPkOk = DecPkOkD2c W Slots.scopeIn)
    (hpksm : S.pksmParse = Pksm.pksmParse)
    (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hst : PqxdhPartyInSpecDomain W st) (hm : m.inner.length + 2048 < 2 ^ 32) :
    RunHsOk S (pqRecvInputs W st (wirePrekey :: m.bytes) rc) :=
  MainHops.runHsOk_pqRecvPrekey_of_decPkOk (S := S) W st m rc fun pm hpm =>
    hdecOk ▸ decPkDomOk_d2c_cli W st m rc pm hst hm (hpksm ▸ hpm)

/-! ## 2. Write-Path Classification and Unconditional `CommitOk` for `decPkDefD2c` -/

private theorem kyberMark_writes_d2c {F : FsFiles} {kpkId spkId : BitVec 32} {bk : PublicKey}
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
  | error _ => rw [hot] at hkm; cases hkm
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
      | error _ => rw [hlr] at hkm; cases hkm
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

private theorem oneTimeUpdate_writes_d2c (F : FsFiles) (opk : Option (BitVec 32)) :
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

theorem decPkAcceptWith_namedWrites_sub {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {F : FsFiles} {P : Party} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {mkBytes : RecordExtras → GhostState (List (BitVec 8)) → List (BitVec 8)}
    {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkAcceptWith X W F (RunRefine.addrValE P) pm coins
      ({ StoresGhost.opened.identity with
         peers := StoresGhost.opened.identity.peers.put (RunRefine.addrValE P).name
           pm.identityKey.serialize }) mkBytes = some (some (g', pt))) :
    ∃ kpkId opkId : BitVec 32,
      ∀ pw ∈ namedWrites g'.writes,
        pw.1 = identityFile (partyAddressName P) ∨
        pw.1 = sessionFile (partyAddress P) ∨
        pw.1 = oneTimeKyberPreKeyFile kpkId ∨
        pw.1 = baseKeysFile kpkId ∨
        pw.1 = oneTimePreKeyFile opkId := by
  unfold decPkAcceptWith at h
  dsimp only at h
  cases hpk : pkToE? pm with
  | none => rw [hpk] at h; cases h
  | some m =>
    rw [hpk] at h; dsimp only at h
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
          rw [hreg] at h; dsimp only at h
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
                  obtain ⟨w8, w9, hkot, hklr, hw8, hw9⟩ := kyberMark_writes_d2c hkm
                  obtain ⟨opkId, w7, hot, hw7⟩ := oneTimeUpdate_writes_d2c F pm.preKeyId
                  refine ⟨m.kpkId, opkId, fun pw hpw => ?_⟩
                  have hw := DecPkS0.namedWrites_of_dirs P pm.identityKey.serialize
                    (mkBytes x gs) kyber'.oneTime kyber'.lastResort _ hkot hklr hot
                  have hpw' :
                      pw ∈ [(identityFile (partyAddressName P), pm.identityKey.serialize)] ++
                        w8 ++ w9 ++ w7 ++
                        [(sessionFile (partyAddress P), mkBytes x gs)] := by
                    rw [← hw]; exact hpw
                  simp only [List.mem_append, List.mem_singleton, or_assoc] at hpw'
                  rcases hpw' with rfl | h8 | h9 | h7 | rfl
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr (Or.inl (hw8 pw h8)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl (hw9 pw h9))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (hw7 pw h7))))
                  · exact Or.inr (Or.inl rfl)

/-- Every store write committed on an accepting `decPkDefD2c` call targets one of the five
canonical party-directory file paths. -/
theorem decPkDefD2c_namedWrites_sub {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDefD2c X W Scope F (RunRefine.addrValE P) me pm coins = some (some (g', pt))) :
    ∃ kpkId opkId : BitVec 32,
      ∀ pw ∈ namedWrites g'.writes,
        pw.1 = identityFile (partyAddressName P) ∨
        pw.1 = sessionFile (partyAddress P) ∨
        pw.1 = oneTimeKyberPreKeyFile kpkId ∨
        pw.1 = baseKeysFile kpkId ∨
        pw.1 = oneTimePreKeyFile opkId := by
  cases hload : Slots.loadRec Scope F (RunRefine.addrValE P) with
  | error e =>
    rw [decPkDefD2c_of_load_err X W Scope F _ me pm coins hload] at h; cases h
  | ok opt =>
    cases opt with
    | none =>
      rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F _ me pm coins
        (fun _ hl => by rw [hload] at hl; cases hl)] at h
      exact decPkDef_namedWrites_sub h
    | some r =>
      cases hcur : r.currentSession with
      | none =>
        rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F _ me pm coins
          (fun _ hl => by rw [hload] at hl; injection hl with hr; injection hr with hr; subst hr; exact hcur)] at h
        exact decPkDef_namedWrites_sub h
      | some s =>
        by_cases hm : SessMatchesPm s pm
        · rw [decPkDefD2c_eq_decPkDef_of_match X W Scope F _ me pm coins hload hcur hm] at h
          exact decPkDef_namedWrites_sub h
        · by_cases htr : StoresGhost.opened.identity.trusted cliIo.rd F
              (RunRefine.addrValE P) pm.identityKey = .ok true
          · rw [decPkDefD2c_of_not_match X W Scope F _ me pm coins hload hcur htr hm] at h
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
            rw [hsave] at h
            exact decPkAcceptWith_namedWrites_sub h
          · rw [decPkDefD2c_eq_decPkDef_of_untrusted X W Scope F _ me pm coins htr] at h
            exact decPkDef_namedWrites_sub h

private def dummyKyberKeyD2c : PqKyberKey where
  pub := List.Vector.replicate 1568 0#8
  sec := List.Vector.replicate 3168 0#8
  sig := List.Vector.replicate 64 0#8
  timestamp := 0#64

private def stWithAllRecvTargetsD2c (W : PEParams) (st : PqParty)
    (kpkId opkId : BitVec 32) : PqParty :=
  { st with
    peerId := some (partyIdentityKey .A)
    session := some (E2E.seedRecordExtras .A,
      (pqxdhSessionParams W).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩)
    oneTime := [(opkId, none)]
    kyberOneTime := [(kpkId, none)]
    kyberLastResort := [(kpkId, (dummyKyberKeyD2c, []))] }

private theorem writeOk_pqRecvInputs_allTargets_d2c (W : PEParams) (st : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256) (kpkId opkId : BitVec 32)
    {p : String}
    (hp : p = identityFile (partyAddressName st.party.other) ∨
          p = sessionFile (partyAddress st.party.other) ∨
          p = oneTimeKyberPreKeyFile kpkId ∨
          p = baseKeysFile kpkId ∨
          p = oneTimePreKeyFile opkId) :
    WriteOk (pqRecvInputs W st c rc) p := by
  have hw := writeOk_pqRecvInputs W st (stWithAllRecvTargetsD2c W st kpkId opkId) c rc
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hw (identityFile (partyAddressName st.party.other), (partyIdentityKey .A).serialize)
      (by simp [encodeDir, stWithAllRecvTargetsD2c])
  · exact hw (sessionFile (partyAddress st.party.other),
      encodeRecordUnderExtras (fun _ => E2E.seedRecordExtras .A)
        ((pqxdhSessionParams W).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩))
      (by simp [encodeDir, stWithAllRecvTargetsD2c])
  · exact hw (oneTimeKyberPreKeyFile kpkId, [])
      (by simp [encodeDir, stWithAllRecvTargetsD2c])
  · exact hw (baseKeysFile kpkId, baseKeysBytes [])
      (by simp [encodeDir, stWithAllRecvTargetsD2c])
  · exact hw (oneTimePreKeyFile opkId, [])
      (by simp [encodeDir, stWithAllRecvTargetsD2c])

/-- Unconditional `CommitOk` for `decPkDefD2c` on `pqRecvInputs W st (wirePrekey :: c) rc`
for all `st` and `c` (including D2(c) `NoMatch` runs). -/
theorem commitOk_pqRecvPrekey_decPkDefD2c {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hdec : S.decryptPrekey = decPkDefD2c X W Scope)
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
    cases ha : decPkDefD2c X W Scope (runFiles (pqRecvInputs W st (wirePrekey :: c) rc))
        (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm
        (HMAC.keyToBytes32 rc) with
    | none =>
      trivial
    | some o =>
      cases o with
      | none => intro _ h; cases h
      | some gp =>
        rcases gp with ⟨g', pt⟩
        obtain ⟨kpkId, opkId, hsub⟩ := decPkDefD2c_namedWrites_sub ha
        intro pw hpw
        exact writeOk_pqRecvInputs_allTargets_d2c W st (wirePrekey :: c) rc kpkId opkId
          (hsub pw hpw)

/-- `decPkCommitOk` bundle obligation for `decPkDefD2c` at `Slots.scopeIn`. -/
theorem decPkCommitOk_d2c_cli {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (S : RunSem) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hdec : S.decryptPrekey = decPkDefD2c X W Slots.scopeIn)
    (_hpksm : S.pksmParse = Pksm.pksmParse)
    (_hwf : PqxdhPartyInSpecDomain W st)
    (_hm : m.inner.length + 2048 < 2 ^ 32)
    (_hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    CommitOk (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
      (MainResult.ofAnswer (runAns S (pqRecvInputs W st (wirePrekey :: m.bytes) rc))) :=
  commitOk_pqRecvPrekey_decPkDefD2c hdec st m.bytes rc

/-! ## 3. Agreement of `decPkDefD2c` on Empty / Matching Sessions (`PqDecryptPrekeyAgrees`) -/

/-- On empty or matching sessions (`∀ x g, st.session = some (x, g) → PqSessionMatches x g m`),
`decPkDefD2c` agrees identically with `pqRecvPrekeyModel` (`RunRefine.PqDecryptPrekeyAgrees`). -/
theorem pqDecryptPrekeyAgrees_decPkDefD2c (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS : S.decryptPrekey = decPkDefD2c X W Scope) (hpksm : PksmTyped S)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope) :
    RunRefine.PqDecryptPrekeyAgrees S X W := by
  intro st m rc pm hwf hm hmatch hparse
  let S0 : RunSem := { S with decryptPrekey := decPkDef X W Scope }
  have hpksm0 : PksmTyped S0 := hpksm
  have hag0 := DecPkS0.pqDecryptPrekeyAgrees_decPkDef S0 X W Scope rfl hpksm0 hinj hcov
    st m rc pm hwf hm hmatch hparse
  obtain ⟨inner, _, rfl⟩ := hpksm m pm hm hparse
  have hload := DecPkS0.loadRec_pqRecv_eq hinj hcov st (wirePrekey :: m.bytes) rc hwf
  have heq_dec :
      decPkDefD2c X W Scope (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
        (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) (pmOfE m inner)
        (HMAC.keyToBytes32 rc) =
      decPkDef X W Scope (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
        (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) (pmOfE m inner)
        (HMAC.keyToBytes32 rc) := by
    cases hs : st.session with
    | none =>
      exact decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope _ _ _ _ _ fun _ hl => by
        rw [hload, hs] at hl; cases hl
    | some xg =>
      rcases xg with ⟨x, g⟩
      rw [hs] at hload
      have hm_pm : SessMatchesPm (E2E.RecordX.sessionOfX (fun _ => x) g) (pmOfE m inner) :=
        DecPkS0.sessMatchesPm_toRecord x g m inner (hmatch x g hs)
      exact decPkDefD2c_eq_decPkDef_of_match X W Scope _ _ _ _ _ hload rfl hm_pm
  rw [hS, heq_dec]
  exact hag0

end CryptoVerification.SignalSession.Cli.RunProofs

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 4. Parameterized `Ext` `RunSem`, Stack Reserve, and Callee Slot Bundles -/

/-- `RunOkNoMatch` store reads use `cliIo.rd`, which is definitionally `CliExt.readFileResult`. -/
theorem cliIo_rd_eq_readRule : Cli.MainHops.cliIo.rd = CliExt.readFileResult := rfl

/-- `PEParams`-parameterized counterpart of `MainHops.cliRunSem`, dropping the unused `CliHooks`
hook fields (`bcmp`, `utf8Err`). -/
noncomputable def cliRunSemP (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) : RunSem where
  encrypt := encDef P Slots.scopeIn
  decryptSignal := decSigDef P Slots.scopeIn
  initiate := initDef X P
  decryptPrekey := decPk
  pksmParse := pksmParse
  filesOk := Slots.filesOk₀ Slots.scopeIn (fun _ => True)
  encOk := Slots.encOk₀ Slots.scopeIn
  initOk := InitOk₀ P
  decPkOk := decPkOk

/-- Concrete D2(c)-extended `RunSem` at `P : PEParams` (`rfl`-equal to `cliRunSemD2cExt X P`). -/
noncomputable abbrev cliRunSemD2cP (X : UnreachedPqxdhPrimitives) (P : PEParams) : RunSem :=
  cliRunSemP X P (decPkDefD2c X P Slots.scopeIn) (DecPkOkD2c P Slots.scopeIn) Pksm.pksmParse

/-- `MainHops.cliRunSem X W` is definitionally `cliRunSemP X ⟨W.C, W.Q⟩`. -/
theorem cliRunSem_eq_cliRunSemP (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) :
    cliRunSem X W decPk decPkOk pksmParse = cliRunSemP X ⟨W.C, W.Q⟩ decPk decPkOk pksmParse :=
  rfl

/-- The D2(c) `RunSem` in `hrun_cli_d2c` / `hrun_cli_d2c_tight` is definitionally
`cliRunSemD2cP X ⟨W.C, W.Q⟩`. -/
theorem cliRunSem_d2c_eq_cliRunSemD2cP (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    cliRunSem X W (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
      (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn) Pksm.pksmParse =
    cliRunSemD2cP X ⟨W.C, W.Q⟩ :=
  rfl

/-- Pointwise `(P, A, ext)` counterpart of `WrapperOver.DecPkD2cSlotOk img` for an arbitrary
allocator `A : RustAlloc` and extern table `ext`. -/
def DecPkD2cSlotAt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (S : RunSem) (needs : RunNeeds),
    S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X P Slots.scopeIn →
    S.decPkOk = DecPkOkD2c P Slots.scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    (slotsOf A img S needs).decryptPrekey.Ok img ext wrapDecryptPrekeyName

/-- Fixed-table `DecPkD2cSlotOk img` specializes immediately to `DecPkD2cSlotAt` at
`P := ⟨W.C, W.Q⟩`, `A := E2E.HooksE.A0`, `ext := cliExterns W`. -/
theorem decPkD2cSlotAt_of_fixed {img : Obj.Image} (W : CliHooks) (hslot : DecPkD2cSlotOk img) :
    DecPkD2cSlotAt img ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliExterns W) :=
  fun X S needs hf hd hdo hn => hslot X W S needs hf hd hdo hn

/-- Bundle of the 5 non-`decryptPrekey` `RunCallees` fields (`readFile`, `encrypt`,
`decryptSignal`, `initiate`, `kemDeserialize`) at `(img, A, ext, S, decPkNeed)`. -/
structure RunBaseCalleesAt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (S : RunSem) (decPkNeed : Nat) : Prop where
  readFile : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
    (readFileSpec cliIo.rd cliWrOk A img cliRunBudgets.readFile)
  encrypt : (slotsOf A img S (cliRunNeeds decPkNeed)).encrypt.Ok img ext wrapEncryptName
  decryptSignal :
    (slotsOf A img S (cliRunNeeds decPkNeed)).decryptSignal.Ok img ext wrapDecryptSignalName
  initiate : (slotsOf A img S (cliRunNeeds decPkNeed)).initiate.Ok img ext wrapInitiateName
  kemDeserialize :
    (slotsOf A img S (cliRunNeeds decPkNeed)).kemDeserialize.Ok img ext kemDeserializeName

/-- Combine `RunBaseCalleesAt` with `DecPkD2cSlotAt` to build the full `RunCallees` at
`cliRunSemD2cP X P`. -/
theorem runCallees_d2c_of_slotAt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (hbase : RunBaseCalleesAt img A ext (cliRunSemD2cP X P)
      (cliDecryptPrekeyNeed cliRunBudgets))
    (hslot : DecPkD2cSlotAt img P A ext) :
    RunCallees img A ext cliRunBudgets
      (slotsOf A img (cliRunSemD2cP X P) (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))) where
  readFile := hbase.readFile
  encrypt := hbase.encrypt
  decryptSignal := hbase.decryptSignal
  initiate := hbase.initiate
  decryptPrekey := hslot X (cliRunSemD2cP X P)
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) rfl rfl rfl rfl
  kemDeserialize := hbase.kemDeserialize

end CryptoVerification.SignalSession.Cli.RunCompose
