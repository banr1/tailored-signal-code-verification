/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridgePlaced
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# SPQR Send and `CliPqOrD3RecvInputs` Domain-Tie Lemmas

**Checked by Lean.**

Projects `o.pqrState = s.pqRatchetState` across `OutgoingTripleRatchet::from_session_state`, wraps
placed `cliSessionStoreSpecPlaced.ScopeAt` session-store domain lifts for `RecordSpqrStateTight640`
and `TopStateTight`, and lifts `PeerSpqrStateTight640` / `CliRunTightSpqrStateCaps` across
`CliPqOrD3RecvInputs`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (Mut OutgoingTripleRatchet SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (
  Api Session SessionRecord execOk execOk_fromSessionState liftProtocol storeCall
)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliPqxdhInputs Cmd Inputs PqParty partyAddress pqRecvInputs
)
open CryptoVerification.SignalSession.Cli (StoresGhost pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (
  AddrV RunCall cliIo parseArgs
)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_recv)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (
  CliRunSpqrStateTightCaps CliRunTightSpqrStateCaps PeerSpqrStateTight640 RecordSpqrStateTight640
  peerSpqrStateTight640_of_cliPqInputs_recv peerSpqrStateTight640_of_cliPqInputs_send
  peerSpqrStateTight640_of_cliSessionStoreSpec recordSpqrStateTight640_of_cliSessionStoreSpec
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf (peerSpqrStateTight640_of_pqRecv_wf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (CliPqOrD3RecvInputs)

/-! ## `OutgoingTripleRatchet::from_session_state` `pqrState` Projection -/

local macro "api_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp [Api.run, storeCall, liftProtocol, modify, modifyGet,
      MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure,
      StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, Id.run, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, $xs,*] $(loc)?)

/-- `OutgoingTripleRatchet::from_session_state` copies `s.pqRatchetState` into `o.pqrState`. -/
theorem execOk_fromSessionState_pqrState {PQ : Type} [Inhabited PQ]
    {s t : SessionState PQ} {o : OutgoingTripleRatchet PQ}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (o, t)) :
    o.pqrState = s.pqRatchetState := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    api_simp [hs, hr] at h
  all_goals split_ifs at h <;> api_simp [] at h
  exact h.1 ▸ rfl

theorem execOk_fromSessionState_pqrState_and_taken {PQ : Type} [Inhabited PQ]
    {s t : SessionState PQ} {o : OutgoingTripleRatchet PQ}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (o, t)) :
    o.pqrState = s.pqRatchetState ∧ t = { s with pqRatchetState := default } :=
  ⟨execOk_fromSessionState_pqrState h, (execOk_fromSessionState h).1⟩

/-! ## Placed `cliSessionStoreSpecPlaced` Wrappers -/

theorem recordSpqrStateTight640_of_cliSessionStoreSpecPlaced [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {files : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    (hScAt : (CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.cliSessionStoreSpecPlaced
      A cliIo.rd files pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hState : PeerSpqrStateTight640 F K files rem) :
    RecordSpqrStateTight640 F K r :=
  recordSpqrStateTight640_of_cliSessionStoreSpec
    (A := A) (b := 0#64) (pathOk := pathOk) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) hScAt hState

theorem recordSpqrStateTight640_of_kitInstSessionStoreSpecPlaced [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {files : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    (hScAt : (CryptoVerification.SignalSession.Cli.KitInst.cliSessionStoreSpecPlaced
      A cliIo.rd files pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hState : PeerSpqrStateTight640 F K files rem) :
    RecordSpqrStateTight640 F K r :=
  recordSpqrStateTight640_of_cliSessionStoreSpec
    (A := A) (b := 0#64) (pathOk := pathOk) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) hScAt hState

theorem peerSpqrStateTight640_of_cliSessionStoreSpecPlaced [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {files : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otrPqr : List (BitVec 8)}
    (hScAt : (CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.cliSessionStoreSpecPlaced
      A cliIo.rd files pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hpqr : otrPqr = sess.state.pqRatchetState)
    (hState : PeerSpqrStateTight640 F K files rem) :
    TopStateTight F K otrPqr :=
  peerSpqrStateTight640_of_cliSessionStoreSpec
    (A := A) (b := 0#64) (pathOk := pathOk) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) hScAt hcur hpqr hState

/-- Derives `TopStateTight F K otr.pqrState` from `cliSessionStoreSpecPlaced.ScopeAt`, `r.currentSession = some sess`, and `OutgoingTripleRatchet.fromSessionState`.
-/
theorem topStateTight_of_cliSessionStoreSpecPlaced_fromSessionState [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {files : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    (hScAt : (CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.cliSessionStoreSpecPlaced
      A cliIo.rd files pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hState : PeerSpqrStateTight640 F K files rem) :
    TopStateTight F K otr.pqrState :=
  peerSpqrStateTight640_of_cliSessionStoreSpecPlaced hScAt hcur
    (execOk_fromSessionState_pqrState hfrom) hState

/-! ## `CliPqOrD3RecvInputs` Domain-Cap Bridges -/

/-- `pqRecvInputs W st ct rc` has `.recv` argv and never parses as `.send peer`. -/
theorem pqRecvInputs_parseArgs_ne_send {W : PEParams} {st : PqParty}
    {ct : List (BitVec 8)} {rc : BitVec 256} {peer : AddrV} :
    parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) ≠
      some (.send peer) := by
  intro hparse
  have ha : (pqRecvInputs W st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  rw [ha, parseArgs_recv] at hparse
  cases hparse

/-- Under `CliPqOrD3RecvInputs W i`, parsing `.send peer` yields `CliPqxdhInputs W i`. -/
theorem cliPqInputs_of_cliPqOrD3RecvInputs_send {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) :
    CliPqxdhInputs W i := by
  rcases hi with hPq | ⟨_, _, _, _, rfl⟩
  · exact hPq
  · exact absurd hparse pqRecvInputs_parseArgs_ne_send

theorem peerSpqrStateTight640_of_cliPqOrD3RecvInputs_send {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) :
    PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) (addrValOf peer) :=
  peerSpqrStateTight640_of_cliPqInputs_send
    (cliPqInputs_of_cliPqOrD3RecvInputs_send hi hparse) hparse

theorem peerSpqrStateTight640_of_cliPqOrD3RecvInputs_recv {W : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) (addrValOf peer) := by
  rcases hi with hPq | ⟨_, _, _, hwf, rfl⟩
  · exact peerSpqrStateTight640_of_cliPqInputs_recv hPq hparse
  · exact peerSpqrStateTight640_of_pqRecv_wf hwf hparse

theorem cliRunSpqrStateTightCaps_of_cliPqOrD3RecvInputs {W : PEParams} {maxInitDir bundleCap : Nat}
    {g : RunCall} (hi : CliPqOrD3RecvInputs W g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hinit : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    CliRunSpqrStateTightCaps W.C.F W.Q.K maxInitDir bundleCap g where
  init_caps := hinit
  send_spqr_state_tight _peer hc :=
    peerSpqrStateTight640_of_cliPqOrD3RecvInputs_send hi (hc ▸ hparse)
  recv_spqr_state_tight _peer hc :=
    peerSpqrStateTight640_of_cliPqOrD3RecvInputs_recv hi (hc ▸ hparse)

/-- Derives `CliRunTightSpqrStateCaps` (`maxInitDir = 26`, `bundleCap = 1,637`) from `CliPqOrD3RecvInputs W g.i`.
-/
theorem cliRunTightSpqrStateCaps_of_cliPqOrD3RecvInputs {W : PEParams} {g : RunCall}
    (hi : CliPqOrD3RecvInputs W g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hinit : ∀ peer dir, g.c = .init peer dir → dir.length ≤ 26 ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ 1637)) :
    CliRunTightSpqrStateCaps W.C.F W.Q.K g :=
  cliRunSpqrStateTightCaps_of_cliPqOrD3RecvInputs hi hparse hinit

end LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
