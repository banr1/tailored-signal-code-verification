/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj

@[expose] public section

set_option autoImplicit false

/-!
# `TopStateTight` Lift from `CliPqxdhInputs`

Lifts the counter-free tight SPQR V1 serialized-state invariant `TopStateTight F K`
(`SpqrTrialDomainLiftAux`) across `ReachablePqxdhSession`, `SessionRecord`, `PeerSpqrStateTight640`,
`cliSessionStoreSpec.ScopeAt`, `w1SessKit.ScopeAt`, and `CliPqxdhInputs`.
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession
  (GhostState KeyPair SessionState ShaCompress SignalMessage
   initializeInitiatorSession initializeRecipientSession maxReceiverChains rootCreateChain)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E
  (LocalIdentity PEParams ReachablePqxdhSession RecordExtras
   acceptInput initiateInput keyPairOf modelPrims ofU8 pqxdhSessionParams responderRecordExtras
   wirePrekey wireWhisper)
open CryptoVerification.E2E.Record (receive_eq_afterRecv send_eq_afterSend toRecord)
open CryptoVerification.E2E.RecordX (extrasOf sessionOfX toRecord_extrasOf_eq)
open CryptoVerification.E2E.V1 (messageEncrypt_ok_props_gen tryDecryptFromRecord_ok_props_gen)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (Bytes MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs PqParty PqxdhPartyInSpecDomain bundleDir partyAddress pqInitInputs
   pqRecvInputs pqSendInputs)
open CryptoVerification.SignalSession.Cli (StoresGhost pathOf)
open CryptoVerification.SignalSession.Cli.KitInst (cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo encodeInjOn_scopeIn parseArgs ratchetScopeCoversPq_scopeIn)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (loadRec_scopeKit_eq w1SessKit)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_init parseArgs_recv parseArgs_send)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (callPeer_of_cmd encodeInjOn_deserializeScopeP_Q filesOkPeer_pqRecv filesOkPeer_pqSend loadRec
   loadRec_pqRecv loadRec_pqSend loadRec_unique partyAddr pqSessBytes_le_fileCapBytes scopeIn
   scopeKit)
open CryptoVerification.SignalSession.Cli.Slots.PqValid
  (initiateStateV1 paramsPV1 reachPq_inv recvPrekeyStateV1)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (PeerSpqrValid)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec (CliRunSpqrAndInitCaps CliRunTightSpqrCaps)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValid640 RecordSpqrTightValid peerSpqrValid_of_peerSpqrTightValidAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (SpqrStateTight640 TopStateTight TopStateTightW spqrStateTight640_length_le
   spqrStateTight640_to_tightValid640 topStateTightW_length_le topStateTightW_links_le_three
   topStateTight_decode_props topStateTight_length_le topStateTight_spqrV1Init
   topStateTight_spqrV1_recv topStateTight_spqrV1_send topStateTight_to_tightValid640)
export LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (SpqrStateTight640 TopStateTight TopStateTightW topStateTight_decode_props)

/-! ## 1. `ReachablePqxdhSession` Lift -/

/-- Every `ReachablePqxdhSession W me x g` maintains `TopStateTight W.C.F W.Q.K` on `g.session.pqRatchetState`.
-/
theorem topStateTight_of_reachPq {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    TopStateTight W.C.F W.Q.K g.session.pqRatchetState := by
  induction h with
  | initiate X P me b t x g hi =>
    change initiateStateV1 X W W.Q.K P me b t = some (x, g) at hi
    unfold initiateStateV1 at hi
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
      _ | ⟨dk, hdr⟩
    · simp [hinit] at hi
    · rw [hinit] at hi; dsimp only at hi
      unfold initializeInitiatorSession at hi
      dsimp only [bind, Except.bind, pure, Except.pure] at hi
      rcases hrc : rootCreateChain W.C (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (KeyPair.generate W.C
            (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨_, _⟩
      · simp [hrc] at hi
      · rw [hrc] at hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩
        exact topStateTight_spqrV1Init W.C.F W.Q.K .a2b _
  | recvPrekey X P me k m rc x g pt hr =>
    change recvPrekeyStateV1 X W W.Q.K P me k m rc = some (some (x, g, pt)) at hr
    unfold recvPrekeyStateV1 at hr
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htf] at hr
    · rw [htf] at hr; dsimp only at hr
      split_ifs at hr with hids
      · simp at hr
      · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
          _ | dk
        · simp [hacc] at hr
        · rw [hacc] at hr; dsimp only at hr
          let st0 : SessionState Bytes :=
            initializeRecipientSession (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv)
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          have hseeds0 : SeedsLen32 st0 := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
              SeedsLen32]
          have hlen0 : st0.receiverChains.length ≤ maxReceiverChains := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
          have hval0 : TopStateTight W.C.F W.Q.K st0.pqRatchetState :=
            topStateTight_spqrV1Init W.C.F W.Q.K .b2a
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          change (match SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 with
            | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none) = some (some (x, g, pt)) at hr
          rcases hdec : SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
              ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
          · rw [hdec] at hr; cases e <;> simp at hr
          · rw [hdec] at hr
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨rfl, rfl, rfl⟩
            obtain ⟨-, -, -, -, _key, hrecv⟩ :=
              tryDecryptFromRecord_ok_props_gen W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
                ((paramsPV1 W.C W.Q.K).expectedAddrs P) inner .preKey rc st0 st pt'
                hseeds0 hlen0 hdec
            exact topStateTight_spqrV1_recv hval0 hrecv
  | @send _ _ g_s m r hr _ ih =>
    rw [send_eq_afterSend]
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with
      ⟨_ | msg, s⟩
    · exact ih
    · obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
      obtain ⟨-, -, -, -, _key, _pm, hsend, -⟩ :=
        messageEncrypt_ok_props_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg
          hseeds hlen' hm
      exact topStateTight_spqrV1_send ih hsend
  | @recv _ _ g_r _ c rc res hr _ hrec ih =>
    rcases res with ⟨_, _, pt⟩
    rw [receive_eq_afterRecv] at hrec
    rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party)
          msg .whisper rc g_r.session with ⟨_ | pt', s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec
        simp only [Option.some.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
        obtain ⟨-, -, -, -, _key, hrecv⟩ :=
          tryDecryptFromRecord_ok_props_gen (pqxdhSessionParams W).C
            (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party)
            msg .whisper rc g_r.session s pt hseeds hlen' hd
        exact topStateTight_spqrV1_recv ih hrecv

theorem spqrStateTight640_of_reachPq {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    SpqrStateTight640 W.C.F W.Q.K g.session.pqRatchetState :=
  (topStateTight_of_reachPq h).toSpqrStateTight640

/-! ## 2. Record and Peer Store Predicates -/

/-- Tight SPQR V1 serialized-state invariant (`TopStateTight F K`) on every active session of a
`SessionRecord`. -/
def RecordSpqrStateTight640 (F : ShaCompress) (K : MlKem)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ sess, r.currentSession = some sess → TopStateTight F K sess.state.pqRatchetState

/-- Tight SPQR V1 serialized-state invariant on the record stored for `rem` on `files` under
`scopeKit`. -/
def PeerSpqrStateTight640 (F : ShaCompress) (K : MlKem) (files : FsFiles) (rem : AddrVal) : Prop :=
  match loadRec scopeKit files rem with
  | .ok (some r) => RecordSpqrStateTight640 F K r
  | _ => True

theorem recordSpqrTightValid640_of_recordSpqrStateTight640 {F : ShaCompress} {K : MlKem}
    {r : SessionRecord (List (BitVec 8))} (h : RecordSpqrStateTight640 F K r) :
    RecordSpqrTightValid 640 r :=
  fun sess hsess => topStateTight_to_tightValid640 (h sess hsess)

theorem peerSpqrTightValid640_of_peerSpqrStateTight640 {F : ShaCompress} {K : MlKem}
    {files : FsFiles} {rem : AddrVal} (h : PeerSpqrStateTight640 F K files rem) :
    PeerSpqrTightValid640 files rem := by
  revert h
  unfold PeerSpqrStateTight640 PeerSpqrTightValid640 SpqrTightCaps.PeerSpqrTightValidAt
  cases loadRec scopeKit files rem with
  | error _ => intro _; trivial
  | ok opt =>
    cases opt with
    | none => intro _; trivial
    | some r => exact recordSpqrTightValid640_of_recordSpqrStateTight640

theorem peerSpqrValid_of_peerSpqrStateTight640 {F : ShaCompress} {K : MlKem}
    {files : FsFiles} {rem : AddrVal} (h : PeerSpqrStateTight640 F K files rem) :
    PeerSpqrValid files rem :=
  peerSpqrValid_of_peerSpqrTightValidAt (by decide)
    (peerSpqrTightValid640_of_peerSpqrStateTight640 h)

/-- Extracts `RecordSpqrStateTight640 F K r` from `PeerSpqrStateTight640 F K files rem` at any `cliSessionStoreSpec.ScopeAt` record.
-/
theorem recordSpqrStateTight640_of_cliSessionStoreSpec {A : RustAlloc} {b : BitVec 64}
    {F : ShaCompress} {K : MlKem} {files : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))}
    (hScAt : (cliSessionStoreSpec A b cliIo.rd files pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hState : PeerSpqrStateTight640 F K files rem) :
    RecordSpqrStateTight640 F K r := by
  obtain ⟨bs, hbs, hla⟩ := hScAt.2
  have hlr : loadRec scopeKit files rem = .ok (some r) :=
    (loadRec_unique encodeInjOn_deserializeScopeP_Q (hbs ▸ hla)).symm
  unfold PeerSpqrStateTight640 at hState
  rw [hlr] at hState
  exact hState

theorem peerSpqrStateTight640_of_cliSessionStoreSpec {A : RustAlloc} {b : BitVec 64}
    {F : ShaCompress} {K : MlKem} {files : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otrPqr : List (BitVec 8)}
    (hScAt : (cliSessionStoreSpec A b cliIo.rd files pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hpqr : otrPqr = sess.state.pqRatchetState)
    (hState : PeerSpqrStateTight640 F K files rem) :
    TopStateTight F K otrPqr := by
  have hrec := recordSpqrStateTight640_of_cliSessionStoreSpec hScAt hState sess hcur
  simpa [hpqr] using hrec

theorem peerSpqrStateTight640_of_w1ScopeAt {B : RunBudgets} {img : Arm64.Obj.Image}
    {F : ShaCompress} {K : MlKem} {files : FsFiles} {peer : AddrGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otrPqr : List (BitVec 8)}
    (hScAt : (w1SessKit B img files peer).ScopeAt scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hpqr : otrPqr = sess.state.pqRatchetState)
    (hState : PeerSpqrStateTight640 F K files rem) :
    TopStateTight F K otrPqr :=
  peerSpqrStateTight640_of_cliSessionStoreSpec hScAt hcur hpqr hState

/-! ## 3. `CliPqxdhInputs` and `RunCall` Domain-Cap Bridges -/

private theorem recordSpqrStateTight640_of_wfSession {W : PEParams} {st : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) {x : RecordExtras} {g : GhostState Bytes}
    (hs : st.session = some (x, g)) :
    RecordSpqrStateTight640 W.C.F W.Q.K (toRecord (extrasOf fun _ => x) g) := by
  intro sess hsess
  simp only [toRecord_extrasOf_eq, Option.some.injEq] at hsess
  subst hsess
  dsimp only [sessionOfX]
  have hwf_sess := hwf.1 x g hs
  rcases hwf_sess.1 with ⟨g₀, hr, _, hsess₀⟩
  have htop := topStateTight_of_reachPq hr
  rw [hsess₀] at htop
  exact htop

theorem peerSpqrStateTight640_of_cliPqInputs_send {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) :
    PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) (addrValOf peer) := by
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
    have hcap := pqSessBytes_le_fileCapBytes hwf
    have hok := filesOkPeer_pqSend W st m r hcov hcap
    have hlrK := loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hok
    have hlrIn := loadRec_pqSend encodeInjOn_scopeIn W st m r hcov hcap
    rw [hpeer]
    unfold PeerSpqrStateTight640
    rw [hlrK, hlrIn]
    rcases hs : st.session with _ | ⟨x, g⟩
    · trivial
    · exact recordSpqrStateTight640_of_wfSession hwf hs
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

theorem peerSpqrStateTight640_of_cliPqInputs_recv {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) (addrValOf peer) := by
  obtain ⟨st, hwf, hcases⟩ := hi
  have hrecvCase : ∀ (ct : List (BitVec 8)) (rc : BitVec 256),
      parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
        some (.recv peer) →
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles (pqRecvInputs W st ct rc)) (addrValOf peer) := by
    intro ct rc hp
    have ha : (pqRecvInputs W st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
    have hpeer : addrValOf peer = partyAddr st.party.other :=
      callPeer_of_cmd (.recv (partyAddress st.party.other)) rfl (ha ▸ hp) rfl
    have hcov := fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs
    have hcap := pqSessBytes_le_fileCapBytes hwf
    have hok := filesOkPeer_pqRecv W st ct rc hcov hcap
    have hlrK := loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hok
    have hlrIn := loadRec_pqRecv encodeInjOn_scopeIn W st ct rc hcov hcap
    rw [hpeer]
    unfold PeerSpqrStateTight640
    rw [hlrK, hlrIn]
    rcases hs : st.session with _ | ⟨x, g⟩
    · trivial
    · exact recordSpqrStateTight640_of_wfSession hwf hs
  rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ | ⟨m, rc, _, rfl⟩ |
    ⟨c, rc, _, _, _, rfl⟩
  · have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
    rw [ha, parseArgs_init] at hparse
    cases hparse
  · have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_send] at hparse
    cases hparse
  · exact hrecvCase (wireWhisper :: c) rc hparse
  · exact hrecvCase (wirePrekey :: m.bytes) rc hparse
  · exact hrecvCase c rc hparse

/-- `RunCall` domain-cap bundle carrying `PeerSpqrStateTight640 F K` on `.send` and `.recv` peers.
-/
structure CliRunSpqrStateTightCaps (F : ShaCompress) (K : MlKem)
    (maxInitDir bundleCap : Nat) (g : RunCall) : Prop where
  init_caps : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
    (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)
  send_spqr_state_tight : ∀ peer, g.c = .send peer →
    PeerSpqrStateTight640 F K (runFiles g.i) (addrValOf peer)
  recv_spqr_state_tight : ∀ peer, g.c = .recv peer →
    PeerSpqrStateTight640 F K (runFiles g.i) (addrValOf peer)

/-- Canonical 1 MiB (`maxInitDir = 26`, `bundleCap = 1,637` B) `CliRunSpqrStateTightCaps` bundle. -/
abbrev CliRunTightSpqrStateCaps (F : ShaCompress) (K : MlKem) (g : RunCall) : Prop :=
  CliRunSpqrStateTightCaps F K 26 1637 g

theorem CliRunSpqrStateTightCaps.toSpqrAndInitCaps {F : ShaCompress} {K : MlKem}
    {maxInitDir bundleCap : Nat} {g : RunCall}
    (h : CliRunSpqrStateTightCaps F K maxInitDir bundleCap g) :
    CliRunSpqrAndInitCaps maxInitDir bundleCap g where
  init_caps := h.init_caps
  send_spqr_tight peer hc :=
    peerSpqrTightValid640_of_peerSpqrStateTight640 (h.send_spqr_state_tight peer hc)
  recv_spqr_tight peer hc :=
    peerSpqrTightValid640_of_peerSpqrStateTight640 (h.recv_spqr_state_tight peer hc)

theorem CliRunTightSpqrStateCaps.toTightSpqrCaps {F : ShaCompress} {K : MlKem} {g : RunCall}
    (h : CliRunTightSpqrStateCaps F K g) : CliRunTightSpqrCaps g :=
  h.toSpqrAndInitCaps

theorem cliRunSpqrStateTightCaps_of_cliPqInputs {W : PEParams} {maxInitDir bundleCap : Nat}
    {g : RunCall} (hi : CliPqxdhInputs W g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hinit : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    CliRunSpqrStateTightCaps W.C.F W.Q.K maxInitDir bundleCap g where
  init_caps := hinit
  send_spqr_state_tight _peer hc :=
    peerSpqrStateTight640_of_cliPqInputs_send hi (hc ▸ hparse)
  recv_spqr_state_tight _peer hc :=
    peerSpqrStateTight640_of_cliPqInputs_recv hi (hc ▸ hparse)

theorem cliRunTightSpqrStateCaps_of_cliPqInputs {W : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs W g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hinit : ∀ peer dir, g.c = .init peer dir → dir.length ≤ 26 ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ 1637)) :
    CliRunTightSpqrStateCaps W.C.F W.Q.K g :=
  cliRunSpqrStateTightCaps_of_cliPqInputs hi hparse hinit

end LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
