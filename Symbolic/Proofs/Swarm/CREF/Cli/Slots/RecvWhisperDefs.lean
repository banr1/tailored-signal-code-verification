/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.OpkRelC
public import Symbolic.Proofs.Swarm.CREF.RecvWire.BinPendPure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.RngG.R3Canon
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPure

/-!
# Whisper Receive Preconditions and Record Canonicality

Defines the entry bundle `WhisperSlotPre`, `CoinSplit` helpers over CLI call events, pre-state
`TRRecordCanonPend` extraction, and post-decrypt `slots_DeserializeScopeP_Q` preservation for CLI
`recv` on whisper wire messages.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

cref_open
open Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Rust (RecordRec)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
  (CliCall CoinSplit ExternContractsHoldCli cliEntryEvents cliExitEvents)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession
open Proofs.libsignal.SR (AesW)
open Symbolic.Swarm.CREF.TR.Pure (PureRecordRepr slots_SessionScopeP slots_RecordCanonical_Q slots_NonEmptyV1Q slots_DeserializeScopeP_Q slots_RecordScopeP slots_RecordInScopeP)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.Cli

/-! ## CLI Call Events, `CoinSplit` Helpers, and `WhisperSlotPre` -/

/-- Events appended to the CLI trace by outcome `o` of call `c`. -/
def cliOutcomeEvents (c : CliCall) : Option Outcome → List MachineEvent
  | some (.exited code out _) => cliEntryEvents c ++ cliExitEvents c code out
  | _ => cliEntryEvents c

def cliRecvWhisperCall (p : Participant) (st : PqParty) (body : HwBytes) (rc : BitVec 256) :
    CliCall where
  party  := p
  cmd    := .recv (partyAddress st.party.other)
  bundle := []
  stdin  := wireWhisper :: body
  coins  := HMAC.keyToBytes32 rc

theorem cliEntryEvents_recvWhisper {c : CliCall} {peer : Address} {body : HwBytes}
    (hcmd : c.cmd = .recv peer) (hstdin : c.stdin = wireWhisperTag :: body) :
    cliEntryEvents c = [.recv (wireWhisperTag :: body), .rng c.coins] := by
  simp [cliEntryEvents, hcmd, hstdin]

theorem cliExitEvents_recvWhisper_zero {c : CliCall} {peer : Address}
    (hcmd : c.cmd = .recv peer) (pt : HwBytes) :
    cliExitEvents c 0 pt = [.accept pt] := by
  simp [cliExitEvents, hcmd]

theorem cliExitEvents_recvWhisper_nonzero {c : CliCall} {peer : Address} {code : Nat}
    (hcmd : c.cmd = .recv peer) (hne : code ≠ 0) (out : HwBytes) :
    cliExitEvents c code out = [] := by
  cases code with
  | zero => exact absurd rfl hne
  | succ _ => simp [cliExitEvents, hcmd]

theorem coinSplit_recv_drop_rng (msg coins : HwBytes) :
    CoinSplit [.recv msg, .rng coins] [.recv msg] := by
  refine .keep (fun _ h => by cases h) ?_
  exact .split (pieces := []) (by simp) List.nil_prefix .nil

theorem coinSplit_recv_full_rng_accept (msg coins pt : HwBytes) (hne : coins ≠ []) :
    CoinSplit [.recv msg, .rng coins, .accept pt]
      [.recv msg, .rng coins, .accept pt] := by
  refine .keep (fun _ h => by cases h) ?_
  refine .split (pieces := [coins])
    (fun q hq => by simp at hq; subst hq; exact hne)
    (by simp) ?_
  exact .keep (fun _ h => by cases h) .nil

theorem coinSplit_recv_drop_rng_accept (msg coins pt : HwBytes) :
    CoinSplit [.recv msg, .rng coins, .accept pt]
      [.recv msg, .accept pt] := by
  refine .keep (fun _ h => by cases h) ?_
  refine .split (pieces := []) (by simp) List.nil_prefix ?_
  exact .keep (fun _ h => by cases h) .nil

/-- Precondition bundle for a whisper `recv` (`wireWhisper :: body`) turn on party `p`. -/
structure WhisperSlotPre (interp : ExternInterpretation) (W : PEParams)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (j : Nat) (p : Participant) (st : PqParty)
    (records : Participant → Option HwBytes)
    (sent accepted : List HwBytes) (opkUsed : Bool)
    (acc_hw : List MachineEvent)
    (body : HwBytes) : Prop where
  extCli    : ExternContractsHoldCli interp
  bridge    : ModelHookBridge interp W
  wfR       : ProtocolSetupWF r
  semEq     : S = compSemOf interp r
  partyMem  : p = r.alice ∨ p = r.bob
  partyTag  : st.party = (if p = r.alice then Party.A else Party.B)
  wfSt      : PqxdhPartyInSpecDomain W st
  recSync   : records p = st.session.map (fun xg => encodeRecordUnderExtras (fun _ => xg.1) xg.2)
  bodyLen   : body.length < 2 ^ 32
  pqHonest  : st.session ≠ none → PqFromHonest sent body
  callIdx   : (callStarts acc_hw).length = j
  whoAt     : who[j]? = some p
  cleanPre  : ∃ g ms, Clean interp r S who ok g ms acc_hw
  relPre    : PureCRel interp r S who ok records sent accepted acc_hw
  opkPre    : COpkRelC interp r S who ok opkUsed acc_hw

/-! ## Record Canonicality and Post-Decrypt Scope -/

/-- `TRRecordCanon` without the `pendingPreKey = none` requirement, covering both steady-state and
Alice's pending-prekey sessions. -/
abbrev TRRecordCanonPend : HwBytes → Prop :=
  Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.TRRecordCanonPend

theorem ooo_of_trRecordCanonPend {recBytes : HwBytes} {gs : Session HwBytes}
    (hcanonP : TRRecordCanonPend recBytes) (hrc : slots_RecordCanonical_Q slots_NonEmptyV1Q recBytes gs) :
    SpqrOooBounded gs.state.pqRatchetState ∧ gs.state.pqRatchetState.length < 2 ^ 32 :=
  Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.ooo_of_trRecordCanonPend hcanonP hrc

/-- Extracts `TRRecordCanonPend`, `SingleSession`, and `slots_RecordCanonical_Q` from
`WhisperSlotPre` when `st.session = some (x, g_sess)`. -/
theorem trRecordCanonPend_of_slotPre
    {interp : ExternInterpretation} {W : PEParams}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant} {st : PqParty}
    {records : Participant → Option HwBytes}
    {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc_hw : List MachineEvent} {body : HwBytes}
    {x : RecordExtras} {g_sess : GhostState HwBytes}
    (hpre : WhisperSlotPre interp W r S who ok j p st records sent accepted opkUsed acc_hw body)
    (hsess : st.session = some (x, g_sess)) :
    let recBytes := encodeRecordUnderExtras (fun _ => x) g_sess
    let sx := pqSession x g_sess
    records p = some recBytes ∧
    recBytes ≠ [] ∧
    SingleSession recBytes ∧
    TRRecordCanonPend recBytes ∧
    (∃ rr : RecordRec, recBytes = recordBytes rr ∧ rr.current.sessionVersion = 4#32) ∧
    slots_RecordCanonical_Q slots_NonEmptyV1Q recBytes sx ∧
    recBytes.length < 2 ^ 31 ∧
    g_sess.party = st.party := by
  intro recBytes sx
  have hrec_p : records p = some recBytes := by
    rw [hpre.recSync, hsess]; rfl
  obtain ⟨_, hg_party, hlen31⟩ := reachPqInvPure_of_wfPq hpre.wfSt hsess
  have hrcq_sx : slots_RecordCanonical_Q slots_NonEmptyV1Q recBytes sx :=
    recordCanonical_Q_of_wfPq hpre.wfSt hsess
  have hss : SingleSession recBytes :=
    ⟨Symbolic.Swarm.CREF.Cli.sessionToRecordRecPending sx,
      encodeRecordX_eq_recordBytesPending_of_wfPq hpre.wfSt hsess, rfl⟩
  have ⟨hcanonP, hrec4⟩ :=
    Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_canonPend_of_pureCRel interp hpre.cleanPre hpre.relPre
      hrec_p hss (by dsimp [recBytes]; omega)
  have hrec_ne : recBytes ≠ [] := by
    obtain ⟨rr, hrr, _⟩ := hrec4
    rw [hrr]
    exact Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_recordBytes_ne_nil₂ rr
  exact ⟨hrec_p, hrec_ne, hss, hcanonP, hrec4, hrcq_sx, hlen31, hg_party⟩

theorem deserializeScopeP_Q_storedSession_of_decryptW {PQC : Type}
    {C : Crypto} {W_aes : AesW} {spqr : Spqr HwBytes PQC}
    {expected : Option HwBytes} {msg : SignalMessage} {coins : BitVec 256}
    {sess : Session HwBytes} {pt : HwBytes} {st' : SessionState HwBytes}
    (hdeser : slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some sess⟩)
    (hok : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C W_aes spqr expected
      msg .whisper coins sess.state = (.ok pt, st'))
    (hpq' : slots_NonEmptyV1Q st'.pqRatchetState) :
    let sess' : Session HwBytes :=
      { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
    slots_RecordInScopeP ⟨some sess'⟩ ∧
    slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some sess'⟩ := by
  intro sess'
  obtain ⟨_hLocEq, _hRemEq, hPpkFalse, hSeeds, hLt32, hLeMax, hSessRepr, _⟩ :=
    Proofs.libsignal.RngG.R3.tryDecryptFromRecordW_ok_state_props hok
  obtain ⟨⟨hScope0, _hPq0, hRepr0⟩, s0, hs0, hRcLe0, _hPpk0, _hKyb0, hAlice0⟩ := hdeser
  injection hs0 with hs0'; subst hs0'
  obtain ⟨hSeeds0, hLt32_0, _⟩ := hScope0 sess rfl
  obtain ⟨hMk0, hClamp0, _hWf0, hAliceLt0⟩ := hRepr0 sess rfl
  have hRep' := hSessRepr ⟨hMk0, hClamp0⟩
  have hScope' : slots_RecordInScopeP ⟨some sess'⟩ := by
    intro s hs; injection hs with hs'; subst hs'
    exact ⟨hSeeds hSeeds0, hLt32 hLt32_0, fun k hk => by simp [sess'] at hk⟩
  have hPq' : slots_RecordScopeP slots_NonEmptyV1Q ⟨some sess'⟩ := by
    intro s hs; injection hs with hs'; subst hs'
    exact hpq'
  have hRepr' : PureRecordRepr ⟨some sess'⟩ := by
    intro s hs; injection hs with hs'; subst hs'
    refine ⟨hRep'.1, hRep'.2, ?_, hAliceLt0⟩
    dsimp [Session.Wf, sess']
    exact hPpkFalse
  have hSessScope' : slots_SessionScopeP sess' :=
    ⟨hLeMax hRcLe0, fun p hp => by simp [sess'] at hp, fun k hk => by simp [sess'] at hk, hAlice0⟩
  exact ⟨hScope', ⟨hScope', hPq', hRepr'⟩, sess', rfl, hSessScope'⟩

end Symbolic.Swarm.CREF.Cli.Slots
