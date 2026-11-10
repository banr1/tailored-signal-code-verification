/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromModel
public import Symbolic.Proofs.Swarm.CREF.Cli.World.TopPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromReject
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Promote Pre-Key Receive Reject Step and Directory Invariant Extraction

Proves the `CliCallStepSpec` postcondition for rejected `.recv` calls (`rpkProm_reject_step`) and
extracts `BobPromDirInv` from `PqPartyInv` and `FilesBounded` (`bobPromDirInv_of_pqPartyInv`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession (Inputs Outcome PqParty PqSessionMatches PqxdhPartyInSpecDomain filesOf
  stdioPaths oneTimePreKeyFile pqxdhExpectedOutcome pqRecvPrekeyModel encodeDir)
open DY.Libsignal.Composed.Refinement.Cli (DirectorySnapshot CliCall CliTurn ValidCall FilesBounded InputsFor
  CoinSplit cliEntryEvents cliExitEvents sessionPathOf peerIdSecret ModelAgree)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

/-- Proves the `CliCallStepSpec` postcondition for a rejected `.recv` call leaving `c.party`'s
session file and Bob's OPK file unchanged. -/
theorem rpkProm_reject_step {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {DirInv : CliTurn → List HwBytes → Prop}
    {t : CliTurn} {c : CliCall} {peer : CryptoVerification.SignalSession.Address}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {acc_hw : List MachineEvent}
    (hcmd : c.cmd = .recv peer) (hne : code ≠ 0)
    (hDir' : DirInv (t.after r c code out files) accepted)
    (hsess : files (sessionPathOf r c.party) = t.dirs c.party (sessionPathOf r c.party))
    (hopk : c.party = r.bob →
      files (oneTimePreKeyFile r.opkId) = t.dirs r.bob (oneTimePreKeyFile r.opkId)) :
    ∃ (blk_hw : List MachineEvent) (accepted' : List HwBytes),
      DirInv (t.after r c code out files) accepted' ∧
      CoinSplit (cliEntryEvents c ++ cliExitEvents c code out) blk_hw ∧
      ∀ (who : List Participant) (ok : Nat → Bool),
        who[(callStarts acc_hw).length]? = some c.party →
        CliLiveAt interp r S who ok t accepted acc_hw →
        ((∃ g ms, MatchedPrefix interp r S who g ms (acc_hw ++ blk_hw)) ∨
          CollisionAt interp r S who ok (acc_hw ++ blk_hw)) ∧
        (¬ CollisionAt interp r S who ok (acc_hw ++ blk_hw) →
          ok (callStarts acc_hw).length = decide (code = 0) →
          CliLiveAt interp r S who ok (t.after r c code out files) accepted'
            (acc_hw ++ blk_hw)) := by
  have ⟨_, hleak_eq, hsent_eq, hopk_eq⟩ :=
    after_unchanged_of_recv_reject hcmd hne out files hsess hopk
  refine ⟨[.recv c.stdin], accepted, hDir', coinSplit_rpkProm_reject hcmd hne out,
    fun who ok _ hlive => ?_⟩
  have hrej := rpkProm_reject_live c.stdin hlive
  refine ⟨Or.inl hrej.1, fun _ hok => ?_⟩
  have hok_f : ok (callStarts acc_hw).length = false := by
    simpa [hne] using hok
  obtain ⟨hclean', hrel', hopk'⟩ := hrej.2 hok_f
  rw [CliLiveAt, hleak_eq, hsent_eq, hopk_eq]
  exact ⟨hclean', hrel', hopk'⟩

/-- Extracts `BobPromDirInv` from `PqPartyInv` and `FilesBounded` at `r.bob`. -/
theorem bobPromDirInv_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {accepted : List HwBytes} {t : CliTurn} {stB : PqParty} {rec_ : HwBytes}
    (hwf : ProtocolSetupWF r) (hagree : ModelAgree interp P)
    (hinvB : PqPartyInv interp P r accepted r.bob stB (t.dirs r.bob))
    (hfb : FilesBounded (t.dirs r.bob))
    (hrec_bob : t.records r r.bob = some rec_) :
    BobPromDirInv interp P r stB rec_ := by
  have hparty : stB.party = .B := hinvB.party_eq.trans (partyOf_bob hwf.1)
  have hpeer_sec : peerIdSecret r r.bob = secretBytes r 0 := by
    unfold peerIdSecret; split_ifs with ha
    · exact absurd ha.symm hwf.1
    · rfl
  have hpub_len : (pubBytes interp (secretBytes r 0)).length = 32 :=
    pubBytes_length_of_modelAgree hagree (secretBytes_0_length hwf)
  have hpeer : ∃ kA : IdentityKey, stB.peerId = some kA ∧
      kA.serialize = ecKey (pubBytes interp (secretBytes r 0)) := by
    refine ⟨⟨⟨bytesToVec 32 (pubBytes interp (secretBytes r 0))⟩⟩, ?_, ?_⟩
    · simpa only [hpeer_sec] using hinvB.peerId_eq
    · change djbKey (bytesToVec 32 (pubBytes interp (secretBytes r 0))) =
        ecKey (pubBytes interp (secretBytes r 0))
      change ecKey (bytesToVec 32 (pubBytes interp (secretBytes r 0))).toList =
        ecKey (pubBytes interp (secretBytes r 0))
      rw [bytesToVec_toList_of_len hpub_len]
  have hwfSt : PqxdhPartyInSpecDomain P stB := wfPq_of_pqPartyInv hinvB hfb
  have hrec_map := (records_of_pqPartyInv hinvB).symm.trans hrec_bob
  have hsess : ∃ x g, stB.session = some (x, g) ∧ rec_ = encodeRecordUnderExtras (fun _ => x) g := by
    cases hs : stB.session with
    | none => simp [hs] at hrec_map
    | some xg =>
      rcases xg with ⟨x, g⟩
      simp only [hs, Option.map_some, Option.some.injEq] at hrec_map
      exact ⟨x, g, rfl, hrec_map.symm⟩
  exact ⟨hparty, hpeer, hwfSt, hsess⟩

end Symbolic.Swarm.CREF.Cli
