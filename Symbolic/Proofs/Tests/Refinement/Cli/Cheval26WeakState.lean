/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.Cheval26.Session
public import Symbolic.Proofs.Tests.Refinement.Cli.Cheval26.Payloads
import all Init.Data.Repr
import all Init.Data.String.Defs
import Symbolic.Proofs.Tests.Refinement.Cli.StdinGuard

/-!
# Non-Vacuity Witness: 7-Call `cheval26-weak-state` Trace

Proves that the CLI protocol environment (`initDirs`, `ValidCall`, `CliTracesMoves`, `CoinSplit`,
and `CallsMatchSchedules`) admits the 7-call recorded trace
`Symbolic.BugInjection.Witnesses.Cheval26WeakState.trace` under `ExternContractsHoldCli chevalInterp`
and `ProtocolSetupWF chevalRecords`, with `PreKeyNoMatch` established on the 7th call `c6`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.Cheval26

open DY
open Arm64 (normalizePath)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (Inputs Outcome CliRun Cmd filesOf stdioPaths
  partyDirs bundleDir coinsFile)
open Symbolic.BugInjection
open Symbolic.Proofs.Tests.Refinement.Cli
open Symbolic.Proofs.Tests.Refinement.Cli.StdinGuard

/-! ## Party Directories, `scrub` / `clearSession` Lemmas, and `chevalRun` -/

def aliceBaseList : List (String × HwBytes) := commonFiles chevalInterp chevalRecords "alice"
def bobBaseList : List (String × HwBytes) :=
  commonFiles chevalInterp chevalRecords "bob" ++ bobPreKeyFiles chevalInterp chevalRecords

def aliceSessPath : String := sessionPathOf chevalRecords "alice"
def bobSessPath : String := sessionPathOf chevalRecords "bob"

def aliceSessList : List (String × HwBytes) :=
  aliceBaseList ++ [(aliceSessPath, chevalSessionBytes)]
def bobSessList : List (String × HwBytes) :=
  bobBaseList ++ [(bobSessPath, chevalSessionBytes)]

def aliceInitDir : DirectorySnapshot := filesOf aliceBaseList
def bobInitDir : DirectorySnapshot := filesOf bobBaseList
def aliceSessDir : DirectorySnapshot := filesOf aliceSessList
def bobSessDir : DirectorySnapshot := filesOf bobSessList

private theorem aliceBaseList_fp : ∀ x ∈ aliceBaseList, CliFilePath x.1 :=
  commonFiles_alice_cliFilePath chevalInterp chevalRecords

private theorem bobBaseList_fp : ∀ x ∈ bobBaseList, CliFilePath x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact commonFiles_bob_cliFilePath chevalRecords_wf.1 x h1
  · exact bobPreKeyFiles_cliFilePath rfl rfl rfl x h2

private theorem aliceSessPath_eq :
    aliceSessPath = CryptoVerification.SignalSession.sessionFile ⟨bobUuid, 1⟩ := rfl

private theorem bobSessPath_eq :
    bobSessPath = CryptoVerification.SignalSession.sessionFile ⟨aliceUuid, 1⟩ := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  simp [bobSessPath, sessionPathOf, peerOf, peerNameOf,
    show chevalRecords.alice = "alice" from rfl, hba]

private theorem aliceSessPath_fp : CliFilePath aliceSessPath := by
  rw [aliceSessPath_eq]; decide

private theorem bobSessPath_fp : CliFilePath bobSessPath := by
  rw [bobSessPath_eq]; decide

private theorem aliceSessList_fp : ∀ x ∈ aliceSessList, CliFilePath x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact aliceBaseList_fp x h1
  · simp only [List.mem_singleton] at h2; subst h2; exact aliceSessPath_fp

private theorem bobSessList_fp : ∀ x ∈ bobSessList, CliFilePath x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact bobBaseList_fp x h1
  · simp only [List.mem_singleton] at h2; subst h2; exact bobSessPath_fp

private theorem aliceBaseList_no_coins_bundle :
    ∀ x ∈ aliceBaseList,
      normalizePath x.1 ≠ [coinsFile] ∧ (normalizePath x.1).head? ≠ some bundleDir := by
  have hpeer : peerNameOf chevalRecords "alice" = bobUuid := rfl
  intro x hx
  simp only [aliceBaseList, commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; decide)

private theorem bobBaseList_no_coins_bundle :
    ∀ x ∈ bobBaseList,
      normalizePath x.1 ≠ [coinsFile] ∧ (normalizePath x.1).head? ≠ some bundleDir := by
  have hpeer : peerNameOf chevalRecords "bob" = aliceUuid := rfl
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · simp only [commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  · simp only [bobPreKeyFiles, show chevalRecords.withOpk = false from rfl, Bool.false_eq_true,
      ↓reduceIte, List.append_nil, show chevalRecords.spkId = 7 from rfl,
      show chevalRecords.kpkId = 9 from rfl, List.mem_cons, List.not_mem_nil, or_false] at h2
    rcases h2 with rfl | rfl | rfl <;> (dsimp only; decide)

private theorem scrub_aliceSessDir : scrub aliceSessDir = aliceSessDir := by
  have h := scrub_filesOf_eq (base := aliceSessList) (extra := [])
    aliceSessList_fp (fun _ hm => nomatch hm)
    (fun x hx => by
      rcases List.mem_append.mp hx with h1 | h2
      · exact aliceBaseList_no_coins_bundle x h1
      · simp only [List.mem_singleton] at h2; subst h2; rw [aliceSessPath_eq]; decide)
    (fun _ hm => nomatch hm)
  simpa [aliceSessDir] using h

private theorem scrub_bobSessDir : scrub bobSessDir = bobSessDir := by
  have h := scrub_filesOf_eq (base := bobSessList) (extra := [])
    bobSessList_fp (fun _ hm => nomatch hm)
    (fun x hx => by
      rcases List.mem_append.mp hx with h1 | h2
      · exact bobBaseList_no_coins_bundle x h1
      · simp only [List.mem_singleton] at h2; subst h2; rw [bobSessPath_eq]; decide)
    (fun _ hm => nomatch hm)
  simpa [bobSessDir] using h

private theorem aliceInitDir_bounded : FilesBounded aliceInitDir :=
  filesBounded_of_cliFilePaths aliceBaseList_fp
    (commonFiles_alice_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf)

private theorem bobInitDir_bounded : FilesBounded bobInitDir := by
  apply filesBounded_of_cliFilePaths bobBaseList_fp
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact commonFiles_bob_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf x h1
  · exact bobPreKeyFiles_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf rfl x h2

set_option maxRecDepth 8192 in
private theorem aliceSessList_bounded : ∀ x ∈ aliceSessList, x.2.length < 2 ^ 31 := by
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact commonFiles_alice_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf x h1
  · simp only [List.mem_singleton] at h2; subst h2; exact chevalSessionBytes_lt

private theorem aliceSessDir_bounded : FilesBounded aliceSessDir :=
  filesBounded_of_cliFilePaths aliceSessList_fp aliceSessList_bounded

set_option maxRecDepth 8192 in
private theorem bobSessList_bounded : ∀ x ∈ bobSessList, x.2.length < 2 ^ 31 := by
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · rcases List.mem_append.mp h1 with h1a | h1b
    · exact commonFiles_bob_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf x h1a
    · exact bobPreKeyFiles_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf rfl x h1b
  · simp only [List.mem_singleton] at h2; subst h2; exact chevalSessionBytes_lt

private theorem bobSessDir_bounded : FilesBounded bobSessDir :=
  filesBounded_of_cliFilePaths bobSessList_fp bobSessList_bounded

def mkTurn (aDir bDir : DirectorySnapshot) (sent : List HwBytes) (bobOff : Bool) : CliTurn where
  dirs := fun q => if q = "alice" then aDir else if q = "bob" then bDir else fun _ => none
  sent := sent
  bobOff := bobOff

private theorem cliTurn_mk_eq {d1 d2 : Participant → DirectorySnapshot} {s1 s2 : List HwBytes} {b1 b2 : Bool}
    (hd : d1 = d2) (hs : s1 = s2) (hb : b1 = b2) :
    CliTurn.mk d1 s1 b1 = CliTurn.mk d2 s2 b2 := by
  subst hd hs hb; rfl

private theorem initTurn_eq_mkTurn :
    CliTurn.init (initDirs chevalInterp chevalRecords) =
      mkTurn aliceInitDir bobInitDir [] false := by
  unfold CliTurn.init mkTurn
  refine cliTurn_mk_eq (funext fun p => ?_) rfl rfl
  simp only [initDirs, show chevalRecords.alice = "alice" from rfl,
    show chevalRecords.bob = "bob" from rfl, aliceInitDir, aliceBaseList,
    bobInitDir, bobBaseList]
  by_cases hpa : p = "alice"
  · subst hpa; simp
  · by_cases hpb : p = "bob"
    · subst hpb; simp [show ("bob" : String) ≠ "alice" from by decide]
    · simp [hpa, hpb]

private theorem aliceBaseList_no_sess :
    ∀ x ∈ aliceBaseList, normalizePath x.1 ≠ normalizePath aliceSessPath := by
  have hpeer : peerNameOf chevalRecords "alice" = bobUuid := rfl
  rw [aliceSessPath_eq]
  intro x hx
  simp only [aliceBaseList, commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; decide)

private theorem bobBaseList_no_sess :
    ∀ x ∈ bobBaseList, normalizePath x.1 ≠ normalizePath bobSessPath := by
  have hpeer : peerNameOf chevalRecords "bob" = aliceUuid := rfl
  rw [bobSessPath_eq]
  intro x hx
  rcases List.mem_append.mp hx with h1 | h2
  · simp only [commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  · simp only [bobPreKeyFiles, show chevalRecords.withOpk = false from rfl, Bool.false_eq_true,
      ↓reduceIte, List.append_nil, show chevalRecords.spkId = 7 from rfl,
      show chevalRecords.kpkId = 9 from rfl, List.mem_cons, List.not_mem_nil, or_false] at h2
    rcases h2 with rfl | rfl | rfl <;> (dsimp only; decide)

private theorem records_alice_init (bDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    (mkTurn aliceInitDir bDir sent off).records chevalRecords "alice" = none := by
  have hnone : aliceInitDir aliceSessPath = none := by
    rw [aliceInitDir, cliFilesOf_eq_evalAt aliceBaseList_fp]
    split
    · rfl
    · split
      · rfl
      · exact cliEvalAt_idle aliceBaseList_no_sess none
  simp [CliTurn.records, mkTurn, show sessionPathOf chevalRecords "alice" = aliceSessPath from rfl,
    hnone]

private theorem records_bob_init (aDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    (mkTurn aDir bobInitDir sent off).records chevalRecords "bob" = none := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hnone : bobInitDir bobSessPath = none := by
    rw [bobInitDir, cliFilesOf_eq_evalAt bobBaseList_fp]
    split
    · rfl
    · split
      · rfl
      · exact cliEvalAt_idle bobBaseList_no_sess none
  simp [CliTurn.records, mkTurn, hba,
    show sessionPathOf chevalRecords "bob" = bobSessPath from rfl, hnone]

private theorem records_alice_sess (bDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    (mkTurn aliceSessDir bDir sent off).records chevalRecords "alice" = some chevalSessionBytes := by
  have hnst : normalizePath aliceSessPath ∉ stdioPaths.map normalizePath := by
    rw [aliceSessPath_eq]; decide
  have hsome : aliceSessDir aliceSessPath = some chevalSessionBytes :=
    filesOf_last_session aliceBaseList_fp aliceSessPath_fp hnst
  simp [CliTurn.records, mkTurn, show sessionPathOf chevalRecords "alice" = aliceSessPath from rfl,
    hsome, chevalSessionBytes_ne_nil]

private theorem records_bob_sess (aDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    (mkTurn aDir bobSessDir sent off).records chevalRecords "bob" = some chevalSessionBytes := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hnst : normalizePath bobSessPath ∉ stdioPaths.map normalizePath := by
    rw [bobSessPath_eq]; decide
  have hsome : bobSessDir bobSessPath = some chevalSessionBytes :=
    filesOf_last_session bobBaseList_fp bobSessPath_fp hnst
  simp [CliTurn.records, mkTurn, hba,
    show sessionPathOf chevalRecords "bob" = bobSessPath from rfl, hsome, chevalSessionBytes_ne_nil]

private theorem clearSession_alice_mkTurn (bDir : DirectorySnapshot) (sent : List HwBytes) :
    (mkTurn aliceSessDir bDir sent false).clearSession chevalRecords "alice" =
      mkTurn aliceInitDir bDir sent false := by
  have hsp : SamePath aliceSessPath (sessionPathOf chevalRecords "alice") = true := by
    rw [show sessionPathOf chevalRecords "alice" = aliceSessPath from rfl, aliceSessPath_eq]
    decide
  have hdir := clearSession_filesOf_eq (r := chevalRecords) (p := "alice")
    (base := aliceBaseList) (sPath := aliceSessPath) (recBytes := chevalSessionBytes)
    aliceBaseList_fp aliceSessPath_fp aliceBaseList_no_sess hsp
    (fun q => if q = "bob" then bDir else fun _ => none) sent false
  unfold CliTurn.clearSession mkTurn; simp only [Bool.false_and]
  refine cliTurn_mk_eq (funext fun q => ?_) rfl rfl
  by_cases hqa : q = "alice"
  · subst hqa; simpa [CliTurn.clearSession, aliceInitDir, aliceSessDir, aliceSessList] using hdir
  · simp [hqa]

open Classical in
private theorem after_alice_mkTurn {aDir bDir : DirectorySnapshot} {sent : List HwBytes}
    {c : CliCall} {out : HwBytes} (hp : c.party = "alice") :
    (mkTurn aDir bDir sent false).after chevalRecords c 0 out aliceSessDir =
      mkTurn aliceSessDir bDir
        (sent ++ (match c.cmd with | .send _ => (sentBody out).toList | _ => [])) false := by
  have hnm : ¬ (0 = 0 ∧ PreKeyNoMatch chevalRecords (mkTurn aDir bDir sent false) c) := by
    rintro ⟨_, hbob, _⟩; exact absurd (hp.symm.trans hbob) (by decide)
  have hbob : ((mkTurn aDir bDir sent false).bobOff ||
      decide (0 = 0 ∧ PreKeyNoMatch chevalRecords (mkTurn aDir bDir sent false) c)) = false := by
    rw [show (mkTurn aDir bDir sent false).bobOff = false from rfl, Bool.false_or]
    exact decide_eq_false hnm
  unfold CliTurn.after; rw [hbob]; simp only [hp, scrub_aliceSessDir]; unfold mkTurn
  refine cliTurn_mk_eq (funext fun q => ?_) (by cases c.cmd <;> rfl) rfl
  by_cases hqa : q = "alice" <;> simp [hqa]

/-- Deterministic `CliRun` witnessing the 7 CLI runs of `cheval26-weak-state`. -/
def chevalRun : CliRun := fun i =>
  if i.argv = (Cmd.init ⟨bobUuid, 1⟩ bundleDir).argv then
    some (.exited 0 [] aliceSessDir)
  else if i.argv = (Cmd.send ⟨bobUuid, 1⟩).argv then
    if i.stdin = pt1 then some (.exited 0 c1Out aliceSessDir)
    else if i.stdin = pt3 then some (.exited 0 c3Out aliceSessDir)
    else if i.stdin = pt5 then some (.exited 0 c5Out aliceSessDir)
    else none
  else if i.argv = (Cmd.recv ⟨aliceUuid, 1⟩).argv then
    if i.stdin = c1Out then some (.exited 0 pt1 bobSessDir)
    else if i.stdin = c6In then some (.exited 0 pt6Out bobSessDir)
    else none
  else none

/-! ## Calls, Intermediate Turns, and Step Proofs -/

private theorem publicBundle_mk_eq
    {r1 r2 s1 s2 k1 k2 : BitVec 32} {ik1 ik2 sk1 sk2 ss1 ss2 kk1 kk2 ks1 ks2 : HwBytes}
    (h1 : r1 = r2) (h2 : ik1 = ik2) (h3 : s1 = s2) (h4 : sk1 = sk2) (h5 : ss1 = ss2)
    (h6 : k1 = k2) (h7 : kk1 = kk2) (h8 : ks1 = ks2) :
    CryptoVerification.SignalSession.PublicBundle.mk ik1 r1 s1 sk1 ss1 k1 kk1 ks1 none =
    CryptoVerification.SignalSession.PublicBundle.mk ik2 r2 s2 sk2 ss2 k2 kk2 ks2 none := by
  subst h1 h2 h3 h4 h5 h6 h7 h8; rfl

private theorem hpub2_eq : pubBytes chevalInterp (secretBytes chevalRecords 2) = pkSpk := by
  rw [chevalRecords_secrets.2, pubBytes, chevalInterp_publicKey, Option.getD_some, chevalPubKey,
    ite_eq_left (rfl : clamp cwSetup.spk = clamp cwSetup.spk)]

private theorem hpub1_eq : pubBytes chevalInterp (secretBytes chevalRecords 1) = pkBob := by
  rw [chevalRecords_secrets.1, pubBytes, chevalInterp_publicKey, Option.getD_some, chevalPubKey,
    ite_eq_right clamp_bobId_ne_spk, ite_eq_left (rfl : clamp cwSetup.bobId = clamp cwSetup.bobId)]

theorem honestPublicBundle_eq_cwBundle :
    honestPublicBundle chevalInterp chevalRecords = cwBundle :=
  publicBundle_mk_eq rfl (congrArg ecKey hpub1_eq) rfl (congrArg ecKey hpub2_eq)
    chevalRecords_opaque.1 rfl (congrArg kyberKey chevalRecords_opaque.2.1) chevalRecords_opaque.2.2

theorem cwBundle_honestBundleDir : HonestBundleDir chevalInterp chevalRecords cwBundle := by
  rw [← honestPublicBundle_eq_cwBundle]
  exact honestBundleDir_honestPublicBundle chevalInterp_cryptoEquationsHold chevalRecords_wf

def call0 : CliCall :=
  { party := "alice", cmd := .init ⟨bobUuid, 1⟩ bundleDir, bundle := cwBundle.files bundleDir,
    stdin := [], coins := coins0 }
def call1 : CliCall :=
  { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt1, coins := coins1 }
def call2 : CliCall :=
  { party := "bob", cmd := .recv ⟨aliceUuid, 1⟩, bundle := [], stdin := c1Out, coins := coins2 }
def call3 : CliCall :=
  { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt3, coins := coins3 }
def call4 : CliCall :=
  { party := "alice", cmd := .init ⟨bobUuid, 1⟩ bundleDir, bundle := cwBundle.files bundleDir,
    stdin := [], coins := coins4 }
def call5 : CliCall :=
  { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt5, coins := coins5 }
def call6 : CliCall :=
  { party := "bob", cmd := .recv ⟨aliceUuid, 1⟩, bundle := [], stdin := c6In, coins := coins6 }

def mkInp (c : CliCall) (base : List (String × HwBytes)) : Inputs where
  argv := c.cmd.argv
  dirs := partyDirs ++ (match c.cmd with | .init _ dir => [dir] | _ => [])
  files := base ++ c.extra
  stdin := c.stdin

def turn0 : CliTurn := mkTurn aliceInitDir bobInitDir [] false
def turn1 : CliTurn := mkTurn aliceSessDir bobInitDir [] false
def turn2 : CliTurn := mkTurn aliceSessDir bobInitDir [s1] false
def turn3 : CliTurn := mkTurn aliceSessDir bobSessDir [s1] false
def turn4Pre : CliTurn := mkTurn aliceSessDir bobSessDir [s1, s3] false
def turn4 : CliTurn := mkTurn aliceInitDir bobSessDir [s1, s3] false
def turn5 : CliTurn := mkTurn aliceSessDir bobSessDir [s1, s3] false
def turn6 : CliTurn := mkTurn aliceSessDir bobSessDir [s1, s3, s5] false
def turn7 : CliTurn := mkTurn aliceSessDir bobSessDir [s1, s3, s5] true

private theorem next_call0 : ValidCall chevalInterp chevalRecords turn0 call0 := by
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, call0, turn0]
  refine ⟨coins0_length, trivial, by simpa [mkTurn] using aliceInitDir_bounded,
    (fun h => nomatch h), rfl, rfl, rfl, rfl, records_alice_init _ _ _,
    honestBundleDir_to_flat_and_honest cwBundle_honestBundleDir⟩

private theorem next_call1 : ValidCall chevalInterp chevalRecords turn1 call1 := by
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, call1, turn1]
  refine ⟨coins1_length, by rw [pt1_length]; omega, by simpa [mkTurn] using aliceSessDir_bounded,
    (fun h => nomatch h), Or.inl rfl, rfl, rfl, by decide, ?_⟩
  rw [records_alice_sess]; simp

private theorem next_call2 : ValidCall chevalInterp chevalRecords turn2 call2 := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, call2, turn2]
  refine ⟨coins2_length, ⟨?_, fun _ => by rw [c1Out_length]; omega, ?_, ?_⟩, by simpa [mkTurn, hba] using bobInitDir_bounded,
    (fun h => nomatch h), Or.inr rfl, rfl, rfl, Or.inr ⟨rfl, Or.inl (canonicalPreKey_head_ne_whisper canonicalPreKey_c1Out), ?_⟩⟩
  · intro body h
    have hlen := c1Out_length
    rw [h] at hlen; simp at hlen; omega
  · intro q hq
    have hm := parse_c1Out_msg; rw [hq] at hm
    have hqm : q.message = s1 := Option.some.inj hm
    rw [hqm, s1_length]; omega
  · intro preKeyId spkId kpkId regId ik ek ct msg _ _ _ hst
    have hle := msg_length_le_preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg
    have hlen := c1Out_length
    rw [← hst] at hle; omega
  · intro q hq
    have hm := parse_c1Out_msg; rw [hq] at hm
    have hqm : q.message = s1 := Option.some.inj hm
    rw [hqm]; exact pqFromHonest_of_mem (by simp [mkTurn])

private theorem next_call3 : ValidCall chevalInterp chevalRecords turn3 call3 := by
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, call3, turn3]
  refine ⟨List.length_replicate, by rw [pt3_length]; omega,
    by simpa [mkTurn] using aliceSessDir_bounded,
    (fun h => nomatch h), Or.inl rfl, rfl, rfl, by decide, ?_⟩
  rw [records_alice_sess]; simp

private theorem next_call4 : ValidCall chevalInterp chevalRecords turn4 call4 := by
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, call4, turn4]
  refine ⟨coins4_length, trivial, by simpa [mkTurn] using aliceInitDir_bounded,
    (fun h => nomatch h), rfl, rfl, rfl, rfl, records_alice_init _ _ _,
    honestBundleDir_to_flat_and_honest cwBundle_honestBundleDir⟩

private theorem next_call5 : ValidCall chevalInterp chevalRecords turn5 call5 := by
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, call5, turn5]
  refine ⟨coins5_length, by rw [pt5_length]; omega, by simpa [mkTurn] using aliceSessDir_bounded,
    (fun h => nomatch h), Or.inl rfl, rfl, rfl, by decide, ?_⟩
  rw [records_alice_sess]; simp

private theorem next_call6 : ValidCall chevalInterp chevalRecords turn6 call6 := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, call6, turn6]
  refine ⟨coins6_length, ⟨?_, fun _ => by rw [c6In_length]; omega, ?_, ?_⟩, by simpa [mkTurn, hba] using bobSessDir_bounded,
    (fun h => nomatch h), Or.inr rfl, rfl, rfl, Or.inr ⟨rfl, Or.inl (canonicalPreKey_head_ne_whisper canonicalPreKey_c6In), ?_⟩⟩
  · intro body h
    have hlen := c6In_length
    rw [h] at hlen; simp at hlen; omega
  · intro q hq
    have hf := parse_c6In_fields; rw [hq] at hf
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
    rw [hf.1, s3_length]; omega
  · intro preKeyId spkId kpkId regId ik ek ct msg _ _ _ hst
    have hle := msg_length_le_preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg
    have hlen := c6In_length
    rw [← hst] at hle; omega
  · intro q hq
    have hf := parse_c6In_fields; rw [hq] at hf
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
    rw [hf.1]; exact pqFromHonest_of_mem (by simp [mkTurn])

theorem not_promoteMatch_chevalSession_c6In : ¬ EligibleForSessionPromotion chevalSessionBytes c6In := by
  rintro ⟨rr, p, hrec, hprev, hp, hbk⟩
  have hf := parse_c6In_fields
  rw [hp] at hf
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
  have hbk_eq : rr.current.aliceBaseKey = c6BaseKey := hbk.trans hf.2
  have h1 := chevalSessionBytes_recordBytes_aliceBaseKey_take2 hrec hprev
  rw [hbk_eq, c6BaseKey_take2] at h1
  cases h1

theorem preKeyNoMatch_call6 : PreKeyNoMatch chevalRecords turn6 call6 := by
  dsimp only [PreKeyNoMatch, call6]
  refine ⟨rfl, ⟨_, rfl⟩, canonicalPreKey_head_ne_whisper canonicalPreKey_c6In, chevalSessionBytes, ?_,
    not_promoteMatch_chevalSession_c6In⟩
  rw [turn6, show chevalRecords.bob = "bob" from rfl]
  exact records_bob_sess aliceSessDir [s1, s3, s5] false

open Classical in
private theorem after_call2 :
    turn2.after chevalRecords call2 0 pt1 bobSessDir = turn3 := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hnm : ¬ (0 = 0 ∧ PreKeyNoMatch chevalRecords turn2 call2) := by
    rintro ⟨_, _, _, _, rec_, hrec, _⟩
    rw [turn2, show chevalRecords.bob = "bob" from rfl, records_bob_init] at hrec; cases hrec
  have hbob : (turn2.bobOff || decide (0 = 0 ∧ PreKeyNoMatch chevalRecords turn2 call2)) = false := by
    rw [show turn2.bobOff = false from rfl, Bool.false_or]; exact decide_eq_false hnm
  unfold CliTurn.after; rw [hbob]
  simp only [show call2.party = "bob" from rfl, show call2.cmd = .recv ⟨aliceUuid, 1⟩ from rfl,
    scrub_bobSessDir, List.append_nil]
  unfold turn2 turn3 mkTurn; refine cliTurn_mk_eq (funext fun q => ?_) rfl rfl
  by_cases hqa : q = "alice"
  · subst hqa; simp [hba.symm]
  · by_cases hqb : q = "bob" <;> simp [hqa, hqb]

open Classical in
private theorem after_call6 :
    turn6.after chevalRecords call6 0 pt6Out bobSessDir = turn7 := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hbob : (turn6.bobOff || decide (0 = 0 ∧ PreKeyNoMatch chevalRecords turn6 call6)) = true := by
    rw [show turn6.bobOff = false from rfl, Bool.false_or]
    exact decide_eq_true ⟨rfl, preKeyNoMatch_call6⟩
  unfold CliTurn.after; rw [hbob]
  simp only [show call6.party = "bob" from rfl, show call6.cmd = .recv ⟨aliceUuid, 1⟩ from rfl,
    scrub_bobSessDir, List.append_nil]
  unfold turn6 turn7 mkTurn; refine cliTurn_mk_eq (funext fun q => ?_) rfl rfl
  by_cases hqa : q = "alice"
  · subst hqa; simp [hba.symm]
  · by_cases hqb : q = "bob" <;> simp [hqa, hqb]

private theorem run_call0 :
    runFnToRelation chevalRun (mkInp call0 aliceBaseList) (some (.exited 0 [] aliceSessDir)) := by
  simp [runFnToRelation, chevalRun, mkInp, call0]
private theorem run_call1 :
    runFnToRelation chevalRun (mkInp call1 aliceSessList) (some (.exited 0 c1Out aliceSessDir)) := by
  have ha : (Cmd.send ⟨bobUuid, 1⟩).argv ≠ (Cmd.init ⟨bobUuid, 1⟩ bundleDir).argv := by decide
  simp [runFnToRelation, chevalRun, mkInp, call1, ha]
private theorem run_call2 :
    runFnToRelation chevalRun (mkInp call2 bobBaseList) (some (.exited 0 pt1 bobSessDir)) := by
  have ha1 : (Cmd.recv ⟨aliceUuid, 1⟩).argv ≠ (Cmd.init ⟨bobUuid, 1⟩ bundleDir).argv := by decide
  have ha2 : (Cmd.recv ⟨aliceUuid, 1⟩).argv ≠ (Cmd.send ⟨bobUuid, 1⟩).argv := by decide
  simp [runFnToRelation, chevalRun, mkInp, call2, ha1, ha2]
private theorem run_call3 :
    runFnToRelation chevalRun (mkInp call3 aliceSessList) (some (.exited 0 c3Out aliceSessDir)) := by
  have ha : (Cmd.send ⟨bobUuid, 1⟩).argv ≠ (Cmd.init ⟨bobUuid, 1⟩ bundleDir).argv := by decide
  simp [runFnToRelation, chevalRun, mkInp, call3, ha, pt3_ne_pt1]
private theorem run_call4 :
    runFnToRelation chevalRun (mkInp call4 aliceBaseList) (some (.exited 0 [] aliceSessDir)) := by
  simp [runFnToRelation, chevalRun, mkInp, call4]
private theorem run_call5 :
    runFnToRelation chevalRun (mkInp call5 aliceSessList) (some (.exited 0 c5Out aliceSessDir)) := by
  have ha : (Cmd.send ⟨bobUuid, 1⟩).argv ≠ (Cmd.init ⟨bobUuid, 1⟩ bundleDir).argv := by decide
  simp [runFnToRelation, chevalRun, mkInp, call5, ha, pt5_ne_pt1, pt5_ne_pt3]
private theorem run_call6 :
    runFnToRelation chevalRun (mkInp call6 bobSessList) (some (.exited 0 pt6Out bobSessDir)) := by
  have ha1 : (Cmd.recv ⟨aliceUuid, 1⟩).argv ≠ (Cmd.init ⟨bobUuid, 1⟩ bundleDir).argv := by decide
  have ha2 : (Cmd.recv ⟨aliceUuid, 1⟩).argv ≠ (Cmd.send ⟨bobUuid, 1⟩).argv := by decide
  simp [runFnToRelation, chevalRun, mkInp, call6, ha1, ha2, c6In_ne_c1Out]

private theorem cliEntryEvents_mk_init (p : Participant)
    (peer : CryptoVerification.SignalSession.Address) (dir : String)
    (b : List (String × HwBytes)) (s cs : HwBytes) (pb : CryptoVerification.SignalSession.PublicBundle)
    (h : parseBundleFiles (filesOf b) = some pb) :
    cliEntryEvents { party := p, cmd := .init peer dir, bundle := b, stdin := s, coins := cs } =
      [.recv (bundleBlob pb), .rng cs] := by
  simp [cliEntryEvents, h]

private theorem cliEntryEvents_mk_send (p : Participant)
    (peer : CryptoVerification.SignalSession.Address)
    (b : List (String × HwBytes)) (s cs : HwBytes) :
    cliEntryEvents { party := p, cmd := .send peer, bundle := b, stdin := s, coins := cs } =
      [.pt s, .rng cs] := rfl

private theorem cliEntryEvents_mk_recv (p : Participant)
    (peer : CryptoVerification.SignalSession.Address)
    (b : List (String × HwBytes)) (s cs : HwBytes) :
    cliEntryEvents { party := p, cmd := .recv peer, bundle := b, stdin := s, coins := cs } =
      [.recv s, .rng cs] := rfl

private theorem cliExitEvents_mk_init (p : Participant)
    (peer : CryptoVerification.SignalSession.Address) (dir : String)
    (b : List (String × HwBytes)) (s cs out : HwBytes) :
    cliExitEvents { party := p, cmd := .init peer dir, bundle := b, stdin := s, coins := cs } 0 out =
      [] := rfl

private theorem cliExitEvents_mk_send (p : Participant)
    (peer : CryptoVerification.SignalSession.Address)
    (b : List (String × HwBytes)) (s cs out : HwBytes) :
    cliExitEvents { party := p, cmd := .send peer, bundle := b, stdin := s, coins := cs } 0 out =
      [.send out] := rfl

private theorem cliExitEvents_mk_recv (p : Participant)
    (peer : CryptoVerification.SignalSession.Address)
    (b : List (String × HwBytes)) (s cs out : HwBytes) :
    cliExitEvents { party := p, cmd := .recv peer, bundle := b, stdin := s, coins := cs } 0 out =
      [.accept out] := rfl

private theorem chevalCliTrace_eq :
    ([] : List MachineEvent) ++ cliEntryEvents call0 ++ cliExitEvents call0 0 [] ++
    (([] : List MachineEvent) ++ cliEntryEvents call1 ++ cliExitEvents call1 0 c1Out ++
    (([] : List MachineEvent) ++ cliEntryEvents call2 ++ cliExitEvents call2 0 pt1 ++
    (([] : List MachineEvent) ++ cliEntryEvents call3 ++ cliExitEvents call3 0 c3Out ++
    (([] : List MachineEvent) ++ cliEntryEvents call4 ++ cliExitEvents call4 0 [] ++
    (([] : List MachineEvent) ++ cliEntryEvents call5 ++ cliExitEvents call5 0 c5Out ++
    (([] : List MachineEvent) ++ cliEntryEvents call6 ++ cliExitEvents call6 0 pt6Out ++
    [])))))) = chevalCliTrace := by
  have hparse : parseBundleFiles (filesOf (cwBundle.files bundleDir)) = some cwBundle :=
    parseBundleFiles_of_honestBundleDir cwBundle_honestBundleDir
  unfold call0 call1 call2 call3 call4 call5 call6
  rw [cliEntryEvents_mk_init _ _ _ _ _ _ _ hparse,
      cliEntryEvents_mk_init _ _ _ _ _ _ _ hparse,
      cliEntryEvents_mk_send, cliEntryEvents_mk_recv, cliEntryEvents_mk_send,
      cliEntryEvents_mk_send, cliEntryEvents_mk_recv,
      cliExitEvents_mk_init, cliExitEvents_mk_send, cliExitEvents_mk_recv,
      cliExitEvents_mk_send, cliExitEvents_mk_init, cliExitEvents_mk_send,
      cliExitEvents_mk_recv, bundleBlob_cwBundle]
  simp only [chevalCliTrace, List.nil_append, List.cons_append, List.append_nil]

theorem chevalCliTraces_admitted :
    CliTracesMoves (runFnToRelation chevalRun) chevalInterp chevalRecords
      (CliTurn.init (initDirs chevalInterp chevalRecords)) chevalCliTrace chevalCalls := by
  rw [initTurn_eq_mkTurn]
  have hba : ("bob" : String) ≠ "alice" := by decide
  have ht01 : turn0.after chevalRecords call0 0 [] aliceSessDir = turn1 := by
    simpa [turn0, turn1, show call0.cmd = .init ⟨bobUuid, 1⟩ bundleDir from rfl] using
      after_alice_mkTurn (aDir := aliceInitDir) (bDir := bobInitDir) (sent := []) (c := call0) (out := []) rfl
  have ht12 : turn1.after chevalRecords call1 0 c1Out aliceSessDir = turn2 := by
    simpa [turn1, turn2, show call1.cmd = .send ⟨bobUuid, 1⟩ from rfl, sentBody_c1Out] using
      after_alice_mkTurn (aDir := aliceSessDir) (bDir := bobInitDir) (sent := []) (c := call1) (out := c1Out) rfl
  have ht34 : turn3.after chevalRecords call3 0 c3Out aliceSessDir = turn4Pre := by
    simpa [turn3, turn4Pre, show call3.cmd = .send ⟨bobUuid, 1⟩ from rfl, sentBody_c3Out] using
      after_alice_mkTurn (aDir := aliceSessDir) (bDir := bobSessDir) (sent := [s1]) (c := call3) (out := c3Out) rfl
  have hclr : turn4Pre.clearSession chevalRecords "alice" = turn4 :=
    clearSession_alice_mkTurn bobSessDir [s1, s3]
  have ht45 : turn4.after chevalRecords call4 0 [] aliceSessDir = turn5 := by
    simpa [turn4, turn5, show call4.cmd = .init ⟨bobUuid, 1⟩ bundleDir from rfl] using
      after_alice_mkTurn (aDir := aliceInitDir) (bDir := bobSessDir) (sent := [s1, s3]) (c := call4) (out := []) rfl
  have ht56 : turn5.after chevalRecords call5 0 c5Out aliceSessDir = turn6 := by
    simpa [turn5, turn6, show call5.cmd = .send ⟨bobUuid, 1⟩ from rfl, sentBody_c5Out] using
      after_alice_mkTurn (aDir := aliceSessDir) (bDir := bobSessDir) (sent := [s1, s3]) (c := call5) (out := c5Out) rfl
  have haliceBase_len : ∀ x ∈ aliceBaseList, x.2.length < 2 ^ 31 :=
    commonFiles_alice_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf
  have hbobBase_len : ∀ x ∈ bobBaseList, x.2.length < 2 ^ 31 := fun x hx =>
    (List.mem_append.mp hx).elim
      (commonFiles_bob_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf x)
      (bobPreKeyFiles_bounded chevalInterp_cryptoEquationsHold chevalRecords_wf rfl x)
  have haliceSess_len : ∀ x ∈ aliceSessList, x.2.length < 2 ^ 31 := aliceSessList_bounded
  have hbobSess_len : ∀ x ∈ bobSessList, x.2.length < 2 ^ 31 := bobSessList_bounded
  have hcwBundle_len : ∀ x ∈ cwBundle.files bundleDir, x.2.length < 2 ^ 31 := fun x hx =>
    ((honestBundleDir_to_flat_and_honest cwBundle_honestBundleDir).1 x hx).2
  have hs7 : CliTracesMoves (runFnToRelation chevalRun) chevalInterp chevalRecords turn7 [] [] :=
    CliTracesMoves.done turn7
  have hs6 := CliTracesMoves.step (leaks := []) (i := mkInp call6 bobSessList)
    (fun _ h => nomatch h) next_call6
    (by simp only [turn6, mkTurn, show call6.party = "bob" from rfl, hba, ↓reduceIte, bobSessDir, mkInp]
        exact inputsFor_of_cliFilePaths call6 bobSessList bobSessList_fp (fun _ h => nomatch h)
          hbobSess_len (fun _ h => nomatch h) (by rw [(next_call6).1]; decide))
    run_call6 (after_call6.symm ▸ hs7)
  have hs5 := CliTracesMoves.step (leaks := []) (i := mkInp call5 aliceSessList)
    (fun _ h => nomatch h) next_call5
    (by simp only [turn5, mkTurn, show call5.party = "alice" from rfl, ↓reduceIte, aliceSessDir, mkInp]
        exact inputsFor_of_cliFilePaths call5 aliceSessList aliceSessList_fp (fun _ h => nomatch h)
          haliceSess_len (fun _ h => nomatch h) (by rw [(next_call5).1]; decide))
    run_call5 (ht56.symm ▸ hs6)
  have hs4 := CliTracesMoves.step (leaks := []) (i := mkInp call4 aliceBaseList)
    (fun _ h => nomatch h) next_call4
    (by simp only [turn4, mkTurn, show call4.party = "alice" from rfl, ↓reduceIte, aliceInitDir, mkInp]
        exact inputsFor_of_cliFilePaths call4 aliceBaseList aliceBaseList_fp
          (bundleFiles_cliFilePath cwBundle) haliceBase_len hcwBundle_len
          (by rw [(next_call4).1]; decide))
    run_call4 (ht45.symm ▸ hs5)
  have hs4Pre : CliTracesMoves (runFnToRelation chevalRun) chevalInterp chevalRecords turn4Pre _ _ :=
    CliTracesMoves.clear "alice" (hclr.symm ▸ hs4)
  have hs3 := CliTracesMoves.step (leaks := []) (i := mkInp call3 aliceSessList)
    (fun _ h => nomatch h) next_call3
    (by simp only [turn3, mkTurn, show call3.party = "alice" from rfl, ↓reduceIte, aliceSessDir, mkInp]
        exact inputsFor_of_cliFilePaths call3 aliceSessList aliceSessList_fp (fun _ h => nomatch h)
          haliceSess_len (fun _ h => nomatch h) (by rw [(next_call3).1]; decide))
    run_call3 (ht34.symm ▸ hs4Pre)
  have hs2 := CliTracesMoves.step (leaks := []) (i := mkInp call2 bobBaseList)
    (fun _ h => nomatch h) next_call2
    (by simp only [turn2, mkTurn, show call2.party = "bob" from rfl, hba, ↓reduceIte, bobInitDir, mkInp]
        exact inputsFor_of_cliFilePaths call2 bobBaseList bobBaseList_fp (fun _ h => nomatch h)
          hbobBase_len (fun _ h => nomatch h) (by rw [(next_call2).1]; decide))
    run_call2 (after_call2.symm ▸ hs3)
  have hs1 := CliTracesMoves.step (leaks := []) (i := mkInp call1 aliceSessList)
    (fun _ h => nomatch h) next_call1
    (by simp only [turn1, mkTurn, show call1.party = "alice" from rfl, ↓reduceIte, aliceSessDir, mkInp]
        exact inputsFor_of_cliFilePaths call1 aliceSessList aliceSessList_fp (fun _ h => nomatch h)
          haliceSess_len (fun _ h => nomatch h) (by rw [(next_call1).1]; decide))
    run_call1 (ht12.symm ▸ hs2)
  have hs0 := CliTracesMoves.step (leaks := []) (i := mkInp call0 aliceBaseList)
    (fun _ h => nomatch h) next_call0
    (by simp only [turn0, mkTurn, show call0.party = "alice" from rfl, ↓reduceIte, aliceInitDir, mkInp]
        exact inputsFor_of_cliFilePaths call0 aliceBaseList aliceBaseList_fp
          (bundleFiles_cliFilePath cwBundle) haliceBase_len hcwBundle_len
          (by rw [(next_call0).1]; decide))
    run_call0 (ht01.symm ▸ hs1)
  rw [← chevalCliTrace_eq]
  exact hs0

/-! ## Main Non-Vacuity Theorems -/

/-- Non-vacuity witness showing that the CLI guards (`initDirs`, `ValidCall`, `CliTracesMoves`,
`CoinSplit`, `CallsMatchSchedules`) admit the 7-call `cheval26-weak-state` trace. -/
theorem cheval26_weak_state_admitted :
    ExternContractsHoldCli chevalInterp ∧
    ProtocolSetupWF chevalRecords ∧
    ∃ (run : CliRun) (τ_cli : List MachineEvent) (calls : List (DY.Participant × Bool)),
      calls.length = 7 ∧
      CliTracesMoves (runFnToRelation run) chevalInterp chevalRecords
        (CliTurn.init (initDirs chevalInterp chevalRecords)) τ_cli calls ∧
      CoinSplit τ_cli Symbolic.Proofs.Tests.Refinement.Cli.Cheval26.Fixture.trace ∧
      CallsMatchSchedules calls Symbolic.Proofs.Tests.Refinement.Cli.Cheval26.Fixture.who
        Symbolic.Proofs.Tests.Refinement.Cli.Cheval26.Fixture.ok :=
  ⟨chevalInterp_contractsHold, chevalRecords_wf, chevalRun, chevalCliTrace, chevalCalls,
    rfl, chevalCliTraces_admitted, chevalCliTrace_coinSplit, chevalCalls_fit⟩

/-- Companion witness showing that the 7th call (`call6`, Bob's pre-key `recv`) is admitted at
`turn6`, satisfies `PreKeyNoMatch` (`¬ EligibleForSessionPromotion`), and sets `bobOff = true`. -/
theorem cheval26_weak_state_last_call_preKeyNoMatch :
    ValidCall chevalInterp chevalRecords turn6 call6 ∧
    PreKeyNoMatch chevalRecords turn6 call6 ∧
    (turn6.after chevalRecords call6 0 pt6Out bobSessDir).bobOff = true :=
  ⟨next_call6, preKeyNoMatch_call6, by rw [after_call6]; rfl⟩

#print axioms cheval26_weak_state_admitted
#print axioms cheval26_weak_state_last_call_preKeyNoMatch

end Symbolic.Proofs.Tests.Refinement.Cli.Cheval26
