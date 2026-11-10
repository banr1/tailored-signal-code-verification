/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj

@[expose] public section

set_option autoImplicit false

/-!
# `PeerSpqrStateTight640` Lift from `PqxdhPartyInSpecDomain`

Lifts `PeerSpqrStateTight640 W.C.F W.Q.K` directly from `PqxdhPartyInSpecDomain W st` onto
`pqRecvInputs` and `pqSendInputs` for arbitrary wire inputs (`ct`, `rc`, `m`, `r`).
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E (PEParams RecordExtras)
open CryptoVerification.E2E.Record (toRecord)
open CryptoVerification.E2E.RecordX (extrasOf sessionOfX toRecord_extrasOf_eq)
open CryptoVerification.LibsignalSpqrV1 (Bytes)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (
  Cmd PqParty PqxdhPartyInSpecDomain partyAddress pqRecvInputs pqSendInputs
)
open CryptoVerification.SignalSession.Cli.MainHops (
  AddrV encodeInjOn_scopeIn parseArgs ratchetScopeCoversPq_scopeIn
)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (loadRec_scopeKit_eq)
open CryptoVerification.SignalSession.Cli.Slots (
  callPeer_of_cmd encodeInjOn_deserializeScopeP_Q filesOkPeer_pqRecv filesOkPeer_pqSend
  loadRec_pqRecv loadRec_pqSend partyAddr pqSessBytes_le_fileCapBytes
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (
  PeerSpqrStateTight640 RecordSpqrStateTight640 topStateTight_of_reachPq
)

theorem recordSpqrStateTight640_of_wfSession' {W : PEParams} {st : PqParty}
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

/-- `pqRecvInputs W st ct rc` satisfies `PeerSpqrStateTight640 W.C.F W.Q.K` on the parsed `.recv peer` address for any `PqxdhPartyInSpecDomain W st`.
-/
theorem peerSpqrStateTight640_of_pqRecv_wf {W : PEParams} {st : PqParty}
    {ct : List (BitVec 8)} {rc : BitVec 256} {peer : AddrV}
    (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
      some (.recv peer)) :
    PeerSpqrStateTight640 W.C.F W.Q.K (runFiles (pqRecvInputs W st ct rc)) (addrValOf peer) := by
  have ha : (pqRecvInputs W st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  have hpeer : addrValOf peer = partyAddr st.party.other :=
    callPeer_of_cmd (.recv (partyAddress st.party.other)) rfl (ha ▸ hparse) rfl
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
  · exact recordSpqrStateTight640_of_wfSession' hwf hs

theorem peerSpqrStateTight640_of_pqSend_wf {W : PEParams} {st : PqParty}
    {m : List (BitVec 8)} {r : List.Vector (BitVec 8) 64} {peer : AddrV}
    (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : parseArgs uuidTryParse ((pqSendInputs W st m r).argv.map bytesOfString) =
      some (.send peer)) :
    PeerSpqrStateTight640 W.C.F W.Q.K (runFiles (pqSendInputs W st m r)) (addrValOf peer) := by
  have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
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
  · exact recordSpqrStateTight640_of_wfSession' hwf hs

end LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf
