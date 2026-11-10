/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs
import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridgeAux
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDirAux
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure

/-!
# Alice Directory Invariant and `CliTurn` Transitions for `init`

Relates `CliTurn` directory snapshots to Alice's `PqParty` state across
`initDirs`, `clearSession`, `InputsFor`, and exit-0 or exit-1 `CliTurn.after`
transitions.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF.Cli (encodeRecordX_eq_encodeRecord_pqSession)

/-- Alice's directory invariant at a CLI directory `d`:
`st` is a well-formed `AlicePqParty` (`PqxdhPartyInSpecDomain P st`) whose encoded directory `filesOf`
agrees with `d` at every path. -/
structure AliceDirState (interp : ExternInterpretation) (P : PEParams)
    (r : ProtocolSetup) (d : DirectorySnapshot) (st : PqParty) : Prop where
  alice  : AlicePqParty interp r st
  wf     : PqxdhPartyInSpecDomain P st
  dir_eq : d = filesOf (encodeDir P st)

theorem encodeRecordX_ne_nil (x : RecordExtras) (g : GhostState HwBytes) :
    encodeRecordUnderExtras (fun _ => x) g ≠ [] := by
  rw [encodeRecordX_eq_encodeRecord_pqSession]
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  dsimp only [Option.map_some]
  have hkey : CryptoVerification.LibsignalProtoCodec.encodeKey 1 .lengthDelimited = [10#8] := by
    decide
  rw [hkey]
  simp

private theorem filesOf_commonFiles_sessionPath_eq_none
    (interp : ExternInterpretation) (r : ProtocolSetup) :
    filesOf (commonFiles interp r r.alice) (sessionPathOf r r.alice) = none := by
  rw [filesOf_eq_optFold (alicePathList_commonFiles interp r), sessionPathOf_alice_eq]
  refine foldl_false_eq_none _ _ fun f hf => ?_
  unfold commonFiles at hf
  simp only [peerNameOf, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem AliceDirState.records_eq {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t : CliTurn} {st : PqParty}
    (hd : AliceDirState interp P r (t.dirs r.alice) st) :
    t.records r r.alice = st.session.map fun (x, g) => encodeRecordUnderExtras (fun _ => x) g := by
  unfold CliTurn.records
  rw [hd.dir_eq, encodeDir_of_alicePqParty hagree hEq hwf hd.alice]
  cases hs : st.session with
  | none =>
    simp [filesOf_commonFiles_sessionPath_eq_none]
  | some xg =>
    rcases xg with ⟨x, g⟩
    have hsess_al : AlicePathList [(sessionPathOf r r.alice, encodeRecordUnderExtras (fun _ => x) g)] := by
      intro f hf; rw [List.mem_singleton] at hf; subst hf
      simp [sessionPathOf_alice_eq, aliceAllPaths, aliceKeepPaths]
    rw [filesOf_append_of_alicePaths (alicePathList_commonFiles interp r) hsess_al,
        filesOf_eq_optFold hsess_al]
    simp [encodeRecordX_ne_nil x g]

theorem AliceDirState.scrub_exit1 {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t : CliTurn} {st : PqParty}
    (hd : AliceDirState interp P r (t.dirs r.alice) st)
    (bE : PreKeyBundleFields) (tVec : List.Vector (BitVec 8) initiateTapeLen) :
    scrub (filesOf (pqInitInputs P st bE tVec).files) = t.dirs r.alice := by
  have hal_dir := alicePathList_encodeDir hagree hEq hwf hd.alice
  have hal_ext := alicePathList_bundle_coins (publicBundleOf bE) tVec.toList
  rw [pqInitInputs_files_eq]
  have hfun : filesOf (encodeDir P st ++
      ((publicBundleOf bE).files bundleDir ++ [(coinsFile, tVec.toList)])) =
      fun p => (filesOf ((publicBundleOf bE).files bundleDir ++ [(coinsFile, tVec.toList)]) p).or
        (filesOf (encodeDir P st) p) :=
    funext (filesOf_append_of_alicePaths hal_dir hal_ext)
  rw [hfun, scrub_or, scrub_filesOf_scrub (aliceScrub_bundle_coins _ _),
      scrub_filesOf_keep (aliceKeep_encodeDir hagree hEq hwf hd.alice), hd.dir_eq]
  funext p; simp

theorem AliceDirState.scrub_exit0 {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t : CliTurn} {st : PqParty}
    (hd : AliceDirState interp P r (t.dirs r.alice) st)
    (hsess_none : st.session = none)
    (bE : PreKeyBundleFields) (tVec : List.Vector (BitVec 8) initiateTapeLen)
    {st' : PqParty} (hal' : AlicePqParty interp r st')
    (x : RecordExtras) (g : GhostState HwBytes) (hsess' : st'.session = some (x, g)) :
    scrub (filesOf ((pqInitInputs P st bE tVec).files ++ encodeDir P st')) =
      filesOf (encodeDir P st') := by
  have hal_pq : AlicePathList (pqInitInputs P st bE tVec).files := by
    rw [pqInitInputs_files_eq]
    exact (alicePathList_encodeDir hagree hEq hwf hd.alice).append
      (alicePathList_bundle_coins _ _)
  have hal_st' := alicePathList_encodeDir hagree hEq hwf hal'
  have hfun : filesOf ((pqInitInputs P st bE tVec).files ++ encodeDir P st') =
      fun p => (filesOf (encodeDir P st') p).or
        (filesOf (pqInitInputs P st bE tVec).files p) :=
    funext (filesOf_append_of_alicePaths hal_pq hal_st')
  rw [hfun, scrub_or, hd.scrub_exit1 hagree hEq hwf bE tVec,
      scrub_filesOf_keep (aliceKeep_encodeDir hagree hEq hwf hal'), hd.dir_eq]
  have henc_st : encodeDir P st = commonFiles interp r r.alice := by
    simpa [hsess_none] using encodeDir_of_alicePqParty hagree hEq hwf hd.alice
  have henc_st' : encodeDir P st' =
      commonFiles interp r r.alice ++ [(sessionPathOf r r.alice, encodeRecordUnderExtras (fun _ => x) g)] := by
    simpa [hsess'] using encodeDir_of_alicePqParty hagree hEq hwf hal'
  have hsess_al : AlicePathList [(sessionPathOf r r.alice, encodeRecordUnderExtras (fun _ => x) g)] := by
    intro f hf; rw [List.mem_singleton] at hf; subst hf
    simp [sessionPathOf_alice_eq, aliceAllPaths, aliceKeepPaths]
  funext p
  rw [henc_st, henc_st', filesOf_append_of_alicePaths (alicePathList_commonFiles interp r) hsess_al]
  cases filesOf [(sessionPathOf r r.alice, encodeRecordUnderExtras (fun _ => x) g)] p <;>
    cases filesOf (commonFiles interp r r.alice) p <;> rfl

theorem AliceDirState.after_exit0 {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t : CliTurn} {st : PqParty}
    (hd : AliceDirState interp P r (t.dirs r.alice) st)
    (hsess_none : st.session = none)
    {c : CliCall} {peer : Address} {dir : String}
    (hparty : c.party = r.alice) (hcmd : c.cmd = .init peer dir)
    (bE : PreKeyBundleFields) (tVec : List.Vector (BitVec 8) initiateTapeLen)
    {st' : PqParty} (hal' : AlicePqParty interp r st') (hwf' : PqxdhPartyInSpecDomain P st')
    (x : RecordExtras) (g : GhostState HwBytes) (hsess' : st'.session = some (x, g)) :
    let t' := t.after r c 0 []
      (filesOf ((pqInitInputs P st bE tVec).files ++ encodeDir P st'))
    AliceDirState interp P r (t'.dirs r.alice) st' ∧
    (∀ q, q ≠ r.alice → t'.dirs q = t.dirs q) ∧
    t'.sent = t.sent ∧
    t'.bobOff = t.bobOff ∧
    t'.opkUsed r = t.opkUsed r ∧
    t'.leakRecords r = fun q =>
      if q = r.alice then some (encodeRecordUnderExtras (fun _ => x) g) else t.leakRecords r q := by
  intro t'
  have hnot_pknm : ¬ PreKeyNoMatch r t c := by
    rintro ⟨hp_bob, _⟩
    exact hwf.1 (hparty.symm.trans hp_bob)
  have hscr := hd.scrub_exit0 hagree hEq hwf hsess_none bE tVec hal' x g hsess'
  have hdirs_alice : t'.dirs r.alice = filesOf (encodeDir P st') := by
    simp [t', CliTurn.after, hparty, hscr]
  have hdirs_other : ∀ q, q ≠ r.alice → t'.dirs q = t.dirs q := by
    intro q hq
    simp [t', CliTurn.after, hparty, hq]
  have hsent : t'.sent = t.sent := by
    simp [t', CliTurn.after, hcmd]
  have hbobOff : t'.bobOff = t.bobOff := by
    simp [t', CliTurn.after, hnot_pknm]
  have hopk : t'.opkUsed r = t.opkUsed r := by
    unfold CliTurn.opkUsed
    rw [hdirs_other r.bob hwf.1.symm]
  have hd' : AliceDirState interp P r (t'.dirs r.alice) st' := ⟨hal', hwf', hdirs_alice⟩
  refine ⟨hd', hdirs_other, hsent, hbobOff, hopk, ?_⟩
  funext q
  by_cases hqa : q = r.alice
  · subst hqa
    have hab : r.alice ≠ r.bob := hwf.1
    simp only [↓reduceIte, CliTurn.leakRecords, hab, and_false,
      hd'.records_eq hagree hEq hwf, hsess', Option.map_some]
  · simp only [hqa, ↓reduceIte, CliTurn.leakRecords, hbobOff, CliTurn.records, hdirs_other q hqa]

end Symbolic.Swarm.CREF.Cli.Slots
