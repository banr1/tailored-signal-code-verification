/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.ExternWitness
public import LibsignalBinary.Proofs.SignalSession.NonVacuityPq
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingFixed
import all Init.Data.Repr
import all Init.Data.String.Defs
import DY.Actions.Network
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Tests.Refinement.Cli.StdinGuard
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Non-Vacuity, Boundary, and Falsifiability Checks for `Composed/Cli/`

Verifies canonical-path and turn-state properties, inhabited `ValidCall` and `CliTracesMoves`
clauses with negative guard boundaries, `CoinSplit`, `CallsMatchSchedules`, `FilesVisible`, and
`HooksMatchInterpretation` checks, and falsifiability of `CompRefinesCliMoves` and
`CompAsmSecurityCliMoves`.
-/

@[expose] public section

set_option autoImplicit false
namespace Symbolic.Proofs.Tests.Refinement.Cli.StmtAuditSym

open DY DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Tests.Refinement.Cli
open Symbolic.Swarm.COMPOSED
open Arm64 (normalizePath)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.SignalSession (Inputs Outcome partyDirs filesOf bundleDir coinsFile sessionFile emptyParty)
open CryptoVerification.E2E (initiateState encodeRecordUnderExtras)
open CryptoVerification.SignalSession.NonVacuityPq (W0 b0 t0 X0)

/-! ## Path Canonicalization and Turn-State Properties -/
private theorem sessionPathOf_cases (r : ProtocolSetup) (p : Participant) :
    sessionPathOf r p = sessionFile ⟨bobUuid, 1⟩ ∨ sessionPathOf r p = sessionFile ⟨aliceUuid, 1⟩ := by
  by_cases hp : p = r.alice <;> simp [sessionPathOf, peerOf, peerNameOf, hp]
theorem samePath_dot_aliases (r : ProtocolSetup) (p : Participant) :
    SamePath "./coins" "coins" = true ∧ SamePath "./bundle/id_pub" "bundle/id_pub" = true ∧
    SamePath ("./" ++ sessionPathOf r p) (sessionPathOf r p) = true := by
  rcases sessionPathOf_cases r p with hs | hs <;> (rw [hs]; exact ⟨rfl, rfl, by decide⟩)
theorem scrub_deletes_coins_and_bundle (d : DirectorySnapshot) :
    scrub d "coins" = none ∧ scrub d "./coins" = none ∧
    scrub d "bundle/id_pub" = none ∧ scrub d "./bundle/id_pub" = none := ⟨rfl, rfl, rfl, rfl⟩
theorem scrub_preserves_party_files (d : DirectorySnapshot) (r : ProtocolSetup) (p : Participant) :
    scrub d "address" = d "address" ∧ scrub d "identity_key" = d "identity_key" ∧
    scrub d "identity-key-pair" = d "identity-key-pair" ∧ scrub d (sessionPathOf r p) = d (sessionPathOf r p) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rcases sessionPathOf_cases r p with hs | hs
  · have hc : (SamePath (sessionFile ⟨bobUuid, 1⟩) coinsFile ||
        (normalizePath (sessionFile ⟨bobUuid, 1⟩)).head? == some bundleDir) = false := by decide
    rw [hs]; simp [scrub, hc]
  · have hc : (SamePath (sessionFile ⟨aliceUuid, 1⟩) coinsFile ||
        (normalizePath (sessionFile ⟨aliceUuid, 1⟩)).head? == some bundleDir) = false := by decide
    rw [hs]; simp [scrub, hc]
theorem clearSession_deletes_session_and_alias (t : CliTurn) (r : ProtocolSetup) (p : Participant) :
    (t.clearSession r p).dirs p (sessionPathOf r p) = none ∧
    (t.clearSession r p).dirs p ("./" ++ sessionPathOf r p) = none := by
  have hself : SamePath (sessionPathOf r p) (sessionPathOf r p) = true := by simp [SamePath]
  simp [CliTurn.clearSession, hself, (samePath_dot_aliases r p).2.2]
theorem clearSession_preserves_non_session (t : CliTurn) (r : ProtocolSetup) (p : Participant) :
    (t.clearSession r p).dirs p "address" = t.dirs p "address" ∧
    (t.clearSession r p).dirs p "identity_key" = t.dirs p "identity_key" ∧
    (t.clearSession r p).dirs p "identity-key-pair" = t.dirs p "identity-key-pair" := by
  rcases sessionPathOf_cases r p with hs | hs <;>
    (have h1 : SamePath "address" (sessionPathOf r p) = false := by rw [hs]; decide
     have h2 : SamePath "identity_key" (sessionPathOf r p) = false := by rw [hs]; decide
     have h3 : SamePath "identity-key-pair" (sessionPathOf r p) = false := by rw [hs]; decide
     simp [CliTurn.clearSession, h1, h2, h3])
theorem clearSession_bobOff_behavior (t : CliTurn) (r : ProtocolSetup) (hne : r.alice ≠ r.bob) :
    (t.clearSession r r.bob).bobOff = false ∧ (t.clearSession r r.alice).bobOff = t.bobOff := by
  simp [CliTurn.clearSession, hne]
theorem leakRecords_bobOff (t : CliTurn) (r : ProtocolSetup) (hoff : t.bobOff = true) (hne : r.alice ≠ r.bob) :
    t.leakRecords r r.bob = none ∧ t.leakRecords r r.alice = t.records r r.alice := by
  simp [CliTurn.leakRecords, hoff, hne]
theorem not_cliNextCall_of_bobOff {interp : ExternInterpretation} {r : ProtocolSetup} {t : CliTurn}
    {c : CliCall} (hoff : t.bobOff = true) (hp : c.party = r.bob) : ¬ ValidCall interp r t c := fun h => h.2.2.2.1 hoff hp
theorem not_filesVisible_dot_or_stdio : ¬ FilesVisible [(".", [])] ∧ ¬ FilesVisible [("<stdin>", [])] :=
  ⟨fun h => (h _ (.head _)).1 rfl, fun h => (h _ (.head _)).2.1 (by decide)⟩

/-! ## Inhabited Clauses and Negative Guard Boundaries -/

def auditSessionBytes : HwBytes :=
  match initiateState X0 W0 .A emptyParty.me b0 t0 with
  | some (x, g) => encodeRecordUnderExtras (fun _ => x) g | none => []
set_option maxHeartbeats 800000 in
theorem auditSessionBytes_wf : auditSessionBytes ≠ [] ∧ auditSessionBytes.length < 2 ^ 31 := by
  unfold auditSessionBytes; exact ⟨by decide +kernel, by decide +kernel⟩

def aliceSessPath : String := sessionPathOf testRecords testRecords.alice
def aliceSessFiles : List (String × HwBytes) :=
  commonFiles cliWitnessInterp testRecords testRecords.alice ++ [(aliceSessPath, auditSessionBytes)]
def bobInitFiles : List (String × HwBytes) :=
  commonFiles cliWitnessInterp testRecords testRecords.bob ++ bobPreKeyFiles cliWitnessInterp testRecords

private theorem aliceSessPath_fp : CliFilePath aliceSessPath := by
  dsimp only [aliceSessPath, sessionPathOf, peerOf, peerNameOf, testRecords]; decide
private theorem aliceSessFiles_fp : ∀ x ∈ aliceSessFiles, CliFilePath x.1 := fun x hx =>
  (List.mem_append.mp hx).elim (commonFiles_alice_cliFilePath cliWitnessInterp testRecords x)
    fun h => by simp only [List.mem_singleton] at h; subst h; exact aliceSessPath_fp
private theorem bobInitFiles_fp : ∀ x ∈ bobInitFiles, CliFilePath x.1 := fun x hx =>
  (List.mem_append.mp hx).elim (commonFiles_bob_cliFilePath testRecords_wf.1 x)
    (bobPreKeyFiles_cliFilePath rfl rfl rfl x)
set_option maxRecDepth 8192 in
private theorem aliceSessFiles_bounded : ∀ x ∈ aliceSessFiles, x.2.length < 2 ^ 31 := fun x hx =>
  (List.mem_append.mp hx).elim (commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf x)
    fun h => by simp only [List.mem_singleton] at h; subst h; exact auditSessionBytes_wf.2
private theorem bobInitFiles_bounded : ∀ x ∈ bobInitFiles, x.2.length < 2 ^ 31 := fun x hx =>
  (List.mem_append.mp hx).elim (commonFiles_bob_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf x)
    (bobPreKeyFiles_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf rfl x)

def aliceSessionTurn : CliTurn :=
  ⟨fun q => if q = testRecords.alice then filesOf aliceSessFiles else initDirs cliWitnessInterp testRecords q, [], false⟩
private theorem aliceSessionTurn_records_alice :
    aliceSessionTurn.records testRecords testRecords.alice = some auditSessionBytes := by
  have hn : normalizePath aliceSessPath ∉ CryptoVerification.SignalSession.stdioPaths.map normalizePath := by
    dsimp only [aliceSessPath, sessionPathOf, peerOf, peerNameOf, testRecords]; decide
  have hf : filesOf aliceSessFiles (sessionPathOf testRecords testRecords.alice) = some auditSessionBytes :=
    filesOf_last_session (recBytes := auditSessionBytes)
      (commonFiles_alice_cliFilePath cliWitnessInterp testRecords) aliceSessPath_fp hn
  unfold CliTurn.records aliceSessionTurn; simp only [↓reduceIte, hf, auditSessionBytes_wf.1]

def testSendCall : CliCall := ⟨testRecords.alice, .send (peerOf testRecords testRecords.alice), [], [], List.replicate 64 0#8⟩
theorem cliNextCall_send_satisfiable :
    ∃ c : CliCall, (∃ peer, c.cmd = .send peer) ∧ ValidCall cliWitnessInterp testRecords aliceSessionTurn c := by
  refine ⟨testSendCall, ⟨_, rfl⟩, ?_⟩
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, testSendCall]
  refine ⟨List.length_replicate, (by decide), ?_, (fun h => by dsimp only [aliceSessionTurn] at h; cases h),
    Or.inl rfl, rfl, rfl, (by dsimp only [aliceSessionTurn]; decide), (by rw [aliceSessionTurn_records_alice]; simp)⟩
  simpa [aliceSessionTurn] using filesBounded_of_cliFilePaths aliceSessFiles_fp aliceSessFiles_bounded

def testRecvWhisperCall : CliCall :=
  ⟨testRecords.alice, .recv (peerOf testRecords testRecords.alice), [], [wireWhisperTag], List.replicate 32 0#8⟩
theorem cliNextCall_recv_whisper_satisfiable :
    ∃ (c : CliCall) (body : HwBytes), (∃ peer, c.cmd = .recv peer) ∧ c.stdin = wireWhisperTag :: body ∧
      ValidCall cliWitnessInterp testRecords aliceSessionTurn c := by
  have htry : CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec [] = .error (.ciphertextMessageTooShort 0) := rfl
  refine ⟨testRecvWhisperCall, [], ⟨_, rfl⟩, rfl, ?_⟩
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, testRecvWhisperCall]
  refine ⟨List.length_replicate, ⟨fun body h => ?_, fun hnw => absurd rfl hnw, fun q hq => ?_, fun _ _ _ _ _ _ _ _ _ _ _ h => ?_⟩, ?_,
    (fun h => by dsimp only [aliceSessionTurn] at h; cases h),
    Or.inl rfl, rfl, rfl, Or.inl ⟨(by rw [aliceSessionTurn_records_alice]; simp), [], rfl, fun _ hm => by rw [htry] at hm; cases hm⟩⟩
  · injection h with _ hb; subst hb; decide
  · simp [parsePreKeyWire, wireWhisperTag, wirePrekeyTag] at hq
  · have hh := congrArg List.head? h; simp [preKeyWire, wireWhisperTag, wirePrekeyTag] at hh
  · simpa [aliceSessionTurn] using filesBounded_of_cliFilePaths aliceSessFiles_fp aliceSessFiles_bounded

def auditPreKeyBytes : HwBytes :=
  preKeyWire none 0 0 0 (ecKey (List.replicate 32 0#8)) (List.replicate 32 0#8) (List.replicate 1568 0#8) []
theorem canonicalPreKey_auditPreKeyBytes : CanonicalPreKey auditPreKeyBytes :=
  ⟨none, 0, 0, 0, List.replicate 32 0#8, List.replicate 32 0#8, List.replicate 1568 0#8, [],
    List.length_replicate, List.length_replicate, List.length_replicate, rfl⟩
theorem parsePreKeyWire_auditPreKeyBytes : parsePreKeyWire auditPreKeyBytes = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

def testRecvPreKeyCall : CliCall :=
  ⟨testRecords.bob, .recv (peerOf testRecords testRecords.bob), [], auditPreKeyBytes, List.replicate 32 0#8⟩
theorem cliNextCall_testRecvPreKeyCall :
    ValidCall cliWitnessInterp testRecords (CliTurn.init (initDirs cliWitnessInterp testRecords)) testRecvPreKeyCall := by
  have hba : testRecords.bob ≠ testRecords.alice := testRecords_wf.1.symm
  have hdirs : (CliTurn.init (initDirs cliWitnessInterp testRecords)).dirs testRecords.bob = filesOf bobInitFiles := by
    simp [CliTurn.init, initDirs, hba, bobInitFiles]
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, testRecvPreKeyCall]
  refine ⟨List.length_replicate, ⟨fun _ h => ?_, fun _ => by decide +kernel, fun q hq => ?_, fun pkId sId kId rId ik ek ct msg _ _ _ h => ?_⟩, ?_,
    (fun h => by dsimp only [CliTurn.init] at h; cases h),
    Or.inr rfl, rfl, rfl, Or.inr ⟨rfl, Or.inl (canonicalPreKey_head_ne_whisper canonicalPreKey_auditPreKeyBytes), fun q hq => ?_⟩⟩
  · have hh := congrArg List.head? h; change some wirePrekeyTag = some wireWhisperTag at hh; cases hh
  · rw [parsePreKeyWire_auditPreKeyBytes] at hq; cases hq
  · have hlen := StdinGuard.msg_length_le_preKeyWire pkId sId kId rId (ecKey ik) ek ct msg
    rw [← h] at hlen; have ha : auditPreKeyBytes.length < 2048 := by decide +kernel
    omega
  · simpa [hdirs] using filesBounded_of_cliFilePaths bobInitFiles_fp bobInitFiles_bounded
  · rw [parsePreKeyWire_auditPreKeyBytes] at hq; cases hq

theorem cliNextCall_recv_prekey_satisfiable :
    ∃ c : CliCall, (∃ peer, c.cmd = .recv peer) ∧ CanonicalPreKey c.stdin ∧
      ValidCall cliWitnessInterp testRecords (CliTurn.init (initDirs cliWitnessInterp testRecords)) c :=
  ⟨testRecvPreKeyCall, ⟨_, rfl⟩, canonicalPreKey_auditPreKeyBytes, cliNextCall_testRecvPreKeyCall⟩

private theorem cliNextCall_init_of_alice_dirs {t : CliTurn} (hbob : t.bobOff = false)
    (hd : t.dirs testRecords.alice = filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice)) :
    ValidCall cliWitnessInterp testRecords t testInitCall := by
  have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
  have hbd := commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf
  have hrec : t.records testRecords testRecords.alice = none := by
    simpa [CliTurn.records, CliTurn.init, initDirs, hd] using initDirs_alice_no_session cliWitnessInterp testRecords
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, testInitCall]
  refine ⟨List.length_replicate, trivial, ?_, (by simp [hbob]), rfl, rfl, rfl, rfl, hrec,
    honestBundleDir_to_flat_and_honest
      (honestBundleDir_honestPublicBundle cliWitnessInterp_cryptoEquationsHold testRecords_wf)⟩
  rw [hd]; exact filesBounded_of_cliFilePaths hbase hbd

theorem cliTraces_clear_satisfiable :
    ¬ ValidCall cliWitnessInterp testRecords aliceSessionTurn testInitCall ∧
    ∃ τ calls, calls ≠ [] ∧ CliTracesMoves (fun _ _ => True) cliWitnessInterp testRecords aliceSessionTurn τ calls := by
  refine ⟨fun hc => by have hm := hc.2.2.2.2; simp [testInitCall, aliceSessionTurn_records_alice] at hm, ?_⟩
  have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
  let t1 := aliceSessionTurn.clearSession testRecords testRecords.alice
  have hd1 : t1.dirs testRecords.alice = filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice) := by
    have hpeer : peerNameOf testRecords testRecords.alice = bobUuid := rfl
    exact clearSession_filesOf_eq hbase aliceSessPath_fp
      (fun x hx => by
        simp only [commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only [aliceSessPath, sessionPathOf, peerOf, hpeer]; decide))
      (by simp [SamePath, aliceSessPath]) (initDirs cliWitnessInterp testRecords) [] false
  let inp1 : Inputs :=
    { argv := testInitCall.cmd.argv, dirs := partyDirs ++ [bundleDir]
      files := commonFiles cliWitnessInterp testRecords testRecords.alice ++ testInitCall.extra, stdin := [] }
  have hinp1 : InputsFor testInitCall (t1.dirs testInitCall.party) inp1 := by
    change InputsFor testInitCall (t1.dirs testRecords.alice) inp1; rw [hd1]
    exact inputsFor_of_cliFilePaths testInitCall _ hbase (bundleFiles_cliFilePath _)
      (commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf)
      (fun x hx => ((honestBundleDir_to_flat_and_honest
        (honestBundleDir_honestPublicBundle cliWitnessInterp_cryptoEquationsHold testRecords_wf)).1 x hx).2)
      (by dsimp only [testInitCall]; rw [List.length_replicate]; decide)
  exact ⟨_, _, by simp, CliTracesMoves.clear testRecords.alice
    (CliTracesMoves.step (leaks := []) (code := 0) (out := []) (files := t1.dirs testInitCall.party) (fun _ h => nomatch h)
      (cliNextCall_init_of_alice_dirs (by simp [CliTurn.clearSession, aliceSessionTurn]) hd1) hinp1 trivial (CliTracesMoves.done _))⟩

theorem cliTraces_stop_aborted_and_none_satisfiable :
    (∃ τ calls, CliTracesMoves (fun _ o => o = some .aborted) cliWitnessInterp testRecords
      (CliTurn.init (initDirs cliWitnessInterp testRecords)) τ calls) ∧
    (∃ τ calls, CliTracesMoves (fun _ o => o = none) cliWitnessInterp testRecords
      (CliTurn.init (initDirs cliWitnessInterp testRecords)) τ calls) := by
  have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
  let t0 := CliTurn.init (initDirs cliWitnessInterp testRecords)
  have hd0 : t0.dirs testRecords.alice = filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice) := by
    simp [t0, CliTurn.init, initDirs]
  let inp0 : Inputs :=
    { argv := testInitCall.cmd.argv, dirs := partyDirs ++ [bundleDir]
      files := commonFiles cliWitnessInterp testRecords testRecords.alice ++ testInitCall.extra, stdin := [] }
  have hinp0 : InputsFor testInitCall (t0.dirs testInitCall.party) inp0 := by
    change InputsFor testInitCall (t0.dirs testRecords.alice) inp0; rw [hd0]
    exact inputsFor_of_cliFilePaths testInitCall _ hbase (bundleFiles_cliFilePath _)
      (commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf)
      (fun x hx => ((honestBundleDir_to_flat_and_honest
        (honestBundleDir_honestPublicBundle cliWitnessInterp_cryptoEquationsHold testRecords_wf)).1 x hx).2)
      (by dsimp only [testInitCall]; rw [List.length_replicate]; decide)
  have hnc := cliNextCall_init_of_alice_dirs (t := t0) rfl hd0
  exact ⟨⟨_, _, CliTracesMoves.stop (leaks := []) (fun _ h => nomatch h) hnc hinp0 rfl (Or.inl rfl)⟩,
    ⟨_, _, CliTracesMoves.stop (leaks := []) (fun _ h => nomatch h) hnc hinp0 rfl (Or.inr rfl)⟩⟩

/-- Live `CliTraces.stop` (`Statement.lean`) admits `some .aborted` and rejects `none` runs. -/
theorem live_cliTraces_stop_aborted_only :
    (∃ evs, evs ≠ [] ∧
      DY.Libsignal.Composed.Refinement.Cli.CliTraces (fun _ o => o = some .aborted)
        cliWitnessInterp testRecords
        (CliTurn.init (initDirs cliWitnessInterp testRecords)) evs) ∧
    (∀ t evs,
      DY.Libsignal.Composed.Refinement.Cli.CliTraces (fun _ o => o = none)
        cliWitnessInterp testRecords t evs →
      ∀ ev, DY.Libsignal.HwEvents.CliEvent.run ev ∉ evs) := by
  refine ⟨?_, ?_⟩
  · have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
    let t0 := CliTurn.init (initDirs cliWitnessInterp testRecords)
    have hd0 : t0.dirs testRecords.alice =
        filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice) := by
      simp [t0, CliTurn.init, initDirs]
    let inp0 : Inputs :=
      { argv := testInitCall.cmd.argv, dirs := partyDirs ++ [bundleDir]
        files := commonFiles cliWitnessInterp testRecords testRecords.alice ++ testInitCall.extra,
        stdin := [] }
    have hinp0 : InputsFor testInitCall (t0.dirs testInitCall.party) inp0 := by
      change InputsFor testInitCall (t0.dirs testRecords.alice) inp0; rw [hd0]
      exact inputsFor_of_cliFilePaths testInitCall _ hbase (bundleFiles_cliFilePath _)
        (commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf)
        (fun x hx => ((honestBundleDir_to_flat_and_honest
          (honestBundleDir_honestPublicBundle cliWitnessInterp_cryptoEquationsHold testRecords_wf)).1 x hx).2)
        (by dsimp only [testInitCall]; rw [List.length_replicate]; decide)
    have hnc := cliNextCall_init_of_alice_dirs (t := t0) rfl hd0
    exact ⟨_, by simp, DY.Libsignal.Composed.Refinement.Cli.CliTraces.stop
      (leaks := []) (fun _ h => nomatch h) hnc hinp0 rfl rfl⟩
  · intro t evs htr
    induction htr with
    | done _ => intro _ h; cases h
    | clear _ _ ih => exact ih
    | breakInvert _ _ ih =>
      intro ev hmem
      rcases List.mem_cons.mp hmem with h | h
      · cases h
      · exact ih ev h
    | step _ _ _ hRel _ _ => cases hRel
    | stop _ _ _ hRel habort => cases hRel.symm.trans habort

/-- `FilesVisible` rejects leading-`/` and `..` paths (`ElfImage.loadState` rejection). -/
theorem not_filesVisible_slash_or_dotdot :
    ¬ FilesVisible [("/coins", [0#8])] ∧ ¬ FilesVisible [("../coins", [0#8])] := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hsl := (h ("/coins", [0#8]) (List.mem_singleton.mpr rfl)).2.2.1
    exact absurd hsl (by decide)
  · have hdd := (h ("../coins", [0#8]) (List.mem_singleton.mpr rfl)).2.2.2.1
    exact absurd hdd (by decide)

/-- Exercises `CliReachable` beyond `.init` across `.step` and `.clear`, reaching distinct turns
where `testSendCall` becomes valid (`t1 ≠ t0`) and session deletion restores `init` (`t2 ≠ t1`). -/
theorem cliReachable_step_and_clear_satisfiable :
    let t0 := CliTurn.init (initDirs cliWitnessInterp testRecords)
    let Rel : Inputs → Option Outcome → Prop :=
      fun _ o => o = some (.exited 0 [] (filesOf aliceSessFiles))
    ∃ t1 t2 : CliTurn,
      t1 ≠ t0 ∧ t2 ≠ t1 ∧
      CliReachable Rel cliWitnessInterp testRecords t0 t1 ∧
      ValidCall cliWitnessInterp testRecords t1 testSendCall ∧
      CliReachable Rel cliWitnessInterp testRecords t0 t2 ∧
      t2.records testRecords testRecords.alice = none := by
  intro t0 Rel
  have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
  have hd0 : t0.dirs testRecords.alice =
      filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice) := by
    simp [t0, CliTurn.init, initDirs]
  let inp0 : Inputs :=
    { argv := testInitCall.cmd.argv, dirs := partyDirs ++ [bundleDir]
      files := commonFiles cliWitnessInterp testRecords testRecords.alice ++ testInitCall.extra,
      stdin := [] }
  have hinp0 : InputsFor testInitCall (t0.dirs testInitCall.party) inp0 := by
    change InputsFor testInitCall (t0.dirs testRecords.alice) inp0; rw [hd0]
    exact inputsFor_of_cliFilePaths testInitCall _ hbase (bundleFiles_cliFilePath _)
      (commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf)
      (fun x hx => ((honestBundleDir_to_flat_and_honest
        (honestBundleDir_honestPublicBundle cliWitnessInterp_cryptoEquationsHold testRecords_wf)).1 x hx).2)
      (by dsimp only [testInitCall]; rw [List.length_replicate]; decide)
  have hnc0 := cliNextCall_init_of_alice_dirs (t := t0) rfl hd0
  let t1 := t0.after testRecords testInitCall 0 [] (filesOf aliceSessFiles)
  have hr1 : CliReachable Rel cliWitnessInterp testRecords t0 t1 :=
    CliReachable.step CliReachable.init hnc0 hinp0 rfl
  have hrec1 : t1.records testRecords testRecords.alice = some auditSessionBytes := by
    have hsp := (scrub_preserves_party_files (filesOf aliceSessFiles) testRecords testRecords.alice).2.2.2
    have hrec_a := aliceSessionTurn_records_alice
    unfold CliTurn.records aliceSessionTurn at hrec_a
    simp only [↓reduceIte] at hrec_a
    unfold CliTurn.records t1 CliTurn.after
    have hp : testInitCall.party = testRecords.alice := rfl
    simp only [hp, ↓reduceIte, hsp]
    exact hrec_a
  have hrec0 : t0.records testRecords testRecords.alice = none :=
    initDirs_alice_no_session cliWitnessInterp testRecords
  have hne10 : t1 ≠ t0 := fun heq => by
    rw [heq, hrec0] at hrec1; cases hrec1
  have hfb_sess : FilesBounded (filesOf aliceSessFiles) :=
    filesBounded_of_cliFilePaths aliceSessFiles_fp aliceSessFiles_bounded
  have hfb1 : FilesBounded (t1.dirs testRecords.alice) := by
    intro p content hsc
    have hp : testInitCall.party = testRecords.alice := rfl
    simp only [t1, CliTurn.after, hp, ↓reduceIte, scrub] at hsc
    split at hsc
    · cases hsc
    · exact hfb_sess p content hsc
  have hbob1 : t1.bobOff = false := by
    have hne : testInitCall.party ≠ testRecords.bob := testRecords_wf.1
    simp [t1, CliTurn.after, t0, CliTurn.init, PreKeyNoMatch, hne]
  have hsend1 : ValidCall cliWitnessInterp testRecords t1 testSendCall := by
    have hsent1 : t1.sent.length < 2 ^ 32 - 1 := by
      simp [t1, CliTurn.after, t0, CliTurn.init, testInitCall]
    dsimp only [ValidCall, StdinBounded, BobCallAllowed, testSendCall]
    exact ⟨List.length_replicate, (by decide), hfb1, (by simp [hbob1]),
      Or.inl rfl, rfl, rfl, hsent1, (by rw [hrec1]; simp)⟩
  let t2 := t1.clearSession testRecords testRecords.alice
  have hr2 : CliReachable Rel cliWitnessInterp testRecords t0 t2 :=
    CliReachable.clear testRecords.alice hr1
  have hrec2 : t2.records testRecords testRecords.alice = none := by
    have hdel := (clearSession_deletes_session_and_alias t1 testRecords testRecords.alice).1
    simp [CliTurn.records, t2, hdel]
  have hne21 : t2 ≠ t1 := fun heq => by
    rw [heq, hrec1] at hrec2; cases hrec2
  exact ⟨t1, t2, hne10, hne21, hr1, hsend1, hr2, hrec2⟩

/-- Minimal well-formed 1-page `udf #0` (`0#32`) ELF image at `Obj.pageSize`. -/
def udfElf : Arm64.Process.ElfImage :=
  { entry := BitVec.ofNat 64 Arm64.Obj.pageSize
    phdrVaddr := BitVec.ofNat 64 Arm64.Obj.pageSize
    phent := 56
    phnum := 1
    segments := [{ start := BitVec.ofNat 64 Arm64.Obj.pageSize
                   perm := .rx
                   bytes := List.replicate Arm64.Obj.pageSize 0#8 }]
    brkStart := BitVec.ofNat 64 (2 * Arm64.Obj.pageSize)
    symbols := [] }

/-- `udfElf` passes `ElfImage.WellFormed` and loads cleanly, yet fails `CliElfProgress` because
instruction 0 (`udf #0`) halts instead of exiting or aborting. -/
theorem not_cliElfProgress_udfElf :
    udfElf.WellFormed = true ∧
    (∃ s0, udfElf.loadState (CryptoVerification.SignalSession.cliProcessInputs
      { argv := testRecvPreKeyCall.cmd.argv, dirs := partyDirs,
        files := bobInitFiles ++ testRecvPreKeyCall.extra, stdin := auditPreKeyBytes }) = .ok s0) ∧
    ¬ CliElfProgress udfElf := by
  have hwf : udfElf.WellFormed = true := by
    unfold udfElf Arm64.Process.ElfImage.WellFormed Arm64.Process.regionsDisjointAndAligned
      Arm64.Process.regionAlignedValid Arm64.Process.entryInExecRegion
    simp only [List.length_replicate]
    decide +kernel
  let inp : Inputs :=
    { argv := testRecvPreKeyCall.cmd.argv, dirs := partyDirs,
      files := bobInitFiles ++ testRecvPreKeyCall.extra, stdin := auditPreKeyBytes }
  let t0 := CliTurn.init (initDirs cliWitnessInterp testRecords)
  have hba : testRecords.bob ≠ testRecords.alice := testRecords_wf.1.symm
  have hd : t0.dirs testRecvPreKeyCall.party = filesOf bobInitFiles := by
    simp [t0, CliTurn.init, initDirs, testRecvPreKeyCall, hba, bobInitFiles]
  have hinp : InputsFor testRecvPreKeyCall (t0.dirs testRecvPreKeyCall.party) inp := by
    rw [hd]
    exact inputsFor_of_cliFilePaths testRecvPreKeyCall _ bobInitFiles_fp (fun _ h => nomatch h)
      bobInitFiles_bounded (fun _ h => nomatch h) (by dsimp only [testRecvPreKeyCall]; decide)
  have hdirs_ok :
      ((CryptoVerification.SignalSession.cliProcessInputs inp).dirs.any
        (fun d => Arm64.hasLeadingSlash d || Arm64.hasDotDot d)) = false := by decide +kernel
  have hfiles_ok :
      ((CryptoVerification.SignalSession.cliProcessInputs inp).files.any
        (fun (p, bs) => Arm64.hasLeadingSlash p || Arm64.hasDotDot p ||
          !decide (bs.length ≤ Arm64.MAX_LFS_FILESIZE))) = false := by
    rw [List.any_eq_false]
    intro ⟨p, bs⟩ hmem
    obtain ⟨_, _, hsl, hdd, hle⟩ := hinp.2.2.2.2 (p, bs) hmem
    simp [hsl, hdd, hle]
  have hstk : ∃ sp stackRegion,
      Arm64.Process.buildInitialStack udfElf
        (CryptoVerification.SignalSession.cliProcessInputs inp) = .ok (sp, stackRegion) := by
    cases h : Arm64.Process.buildInitialStack udfElf
        (CryptoVerification.SignalSession.cliProcessInputs inp) with
    | ok p => exact ⟨p.1, p.2, rfl⟩
    | error _ =>
      have hok : (match Arm64.Process.buildInitialStack udfElf
          (CryptoVerification.SignalSession.cliProcessInputs inp) with
        | .ok _ => true | .error _ => false) = true := by decide +kernel
      rw [h] at hok; cases hok
  obtain ⟨sp, stackRegion, hstk_eq⟩ := hstk
  let baseMem : Arm64.Memory := ⟨Arm64.Snapshot.loadCellAt (udfElf.segments ++ [stackRegion])⟩
  let stackBase := BitVec.ofNat 64
    ((CryptoVerification.SignalSession.cliProcessInputs inp).init.stackTop.toNat -
      (CryptoVerification.SignalSession.cliProcessInputs inp).init.stackSize)
  have hload : ∃ s0, udfElf.loadState (CryptoVerification.SignalSession.cliProcessInputs inp) = .ok s0 ∧
      s0.pc = udfElf.entry ∧ s0.status = .Running ∧
      s0.mem = baseMem.mapZero stackBase
        (CryptoVerification.SignalSession.cliProcessInputs inp).init.stackSize := by
    unfold Arm64.Process.ElfImage.loadState
    simp only [hwf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hdirs_ok, hfiles_ok,
      Bind.bind, Except.bind, hstk_eq, pure, Except.pure]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  obtain ⟨s0, hload_eq, hpc, hrun, hmem⟩ := hload
  refine ⟨hwf, ⟨s0, hload_eq⟩, fun hprog => ?_⟩
  have hne := hprog cliWitnessInterp cliWitnessInterp_contracts cliWitnessHooks cliWitnessHooks_agree
    testRecords testRecords_wf t0 CliReachable.init testRecvPreKeyCall inp
    cliNextCall_testRecvPreKeyCall hinp
  apply hne
  unfold CryptoVerification.SignalSession.cliRunAbortOnPanic
  split
  · next hex =>
    obtain ⟨o, s0', hload', hruns⟩ := hex
    cases Option.some.inj ( Except.ok.inj (hload_eq.symm.trans hload') ▸ rfl : some s0 = some s0' )
    let prog := CryptoVerification.SignalSession.cliProgAbortOnPanic cliWitnessHooks
    let st0 := CryptoVerification.SignalSession.cliTokenPatch s0
    have hpc_st0 : st0.pc = udfElf.entry := by simp [st0, CryptoVerification.SignalSession.cliTokenPatch, hpc]
    have hrun_st0 : st0.status = .Running := by simp [st0, CryptoVerification.SignalSession.cliTokenPatch, hrun]
    have hext_none : prog.externAt? st0.pc = none := by
      rw [hpc_st0]
      exact Option.isNone_iff_eq_none.mp (by decide +kernel)
    have hfetch_none : prog.fetchMem st0.mem st0.pc = none := by
      unfold Arm64.Program.fetchMem
      rw [hext_none]
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · have hr32 : st0.mem.read32 st0.pc = 0#32 := by
              have hw8 : ∀ (m : Arm64.Memory) (addr a : BitVec 64),
                  m.read8 a = 0#8 → (m.write8 addr 0#8).read8 a = 0#8 := by
                intro m addr a hm
                unfold Arm64.Memory.read8 at hm ⊢
                unfold Arm64.Memory.write8
                dsimp only
                by_cases ha : a = addr
                · subst ha; simp only [↓reduceIte]
                · simp only [ha, ↓reduceIte]; exact hm
              have hmz : ∀ (m : Arm64.Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64),
                  m.read8 a = 0#8 → (m.mapZero base len).read8 a = 0#8 := by
                intro m base len a hm
                unfold Arm64.Memory.read8 at hm ⊢
                unfold Arm64.Memory.mapZero
                dsimp only
                cases hc : ((a - base).toNat < len && !(m.perm a).mapped)
                · simp only [Bool.false_eq_true, ↓reduceIte]; exact hm
                · simp only [↓reduceIte]
              have hb : ∀ (sr : Arm64.Snapshot.Region) (off : BitVec 64),
                  (off = 0#64 ∨ off = 1#64 ∨ off = 2#64 ∨ off = 3#64) →
                  (⟨Arm64.Snapshot.loadCellAt (udfElf.segments ++ [sr])⟩ :
                    Arm64.Memory).read8 (udfElf.entry + off) = 0#8 := by
                intro sr off hoff
                have hlt : (BitVec.ofNat 64 Arm64.Obj.pageSize + off -
                    BitVec.ofNat 64 Arm64.Obj.pageSize).toNat <
                    (List.replicate Arm64.Obj.pageSize (0#8 : BitVec 8)).length := by
                  rw [List.length_replicate]
                  rcases hoff with rfl | rfl | rfl | rfl <;> decide +kernel
                unfold Arm64.Memory.read8 Arm64.Snapshot.loadCellAt udfElf
                dsimp only [List.cons_append, List.findSome?]
                simp only [hlt, ↓reduceDIte, List.getElem_replicate]
              obtain ⟨a1, a2, hst0_mem⟩ : ∃ a1 a2,
                  st0.mem = (s0.mem.writeBytes a1 [0#8]).writeBytes a2 [0#8, 0#8, 0#8, 0#8] :=
                ⟨_, _, rfl⟩
              have hm8 : ∀ (off : BitVec 64),
                  (off = 0#64 ∨ off = 1#64 ∨ off = 2#64 ∨ off = 3#64) →
                  st0.mem.read8 (udfElf.entry + off) = 0#8 := by
                intro off hoff
                rw [hst0_mem, hmem]
                dsimp only [Arm64.Memory.writeBytes]
                exact hw8 _ _ _ (hw8 _ _ _ (hw8 _ _ _ (hw8 _ _ _ (hw8 _ _ _
                  (hmz _ _ _ _ (hb stackRegion off hoff))))))
              rw [hpc_st0]
              unfold Arm64.Memory.read32
              rw [hm8 0#64 (Or.inl rfl), hm8 1#64 (Or.inr (Or.inl rfl)),
                  hm8 2#64 (Or.inr (Or.inr (Or.inl rfl))), hm8 3#64 (Or.inr (Or.inr (Or.inr rfl)))]
              rfl
            rw [hr32]
            decide +kernel
    have hstep : Arm64.Step prog st0 { st0 with status := .Halted } :=
      Arm64.Step.halt_unmapped hrun_st0 hfetch_none hext_none
    have hsteps : Arm64.Steps prog st0 { st0 with status := .Halted } :=
      Arm64.Steps.step hstep (Arm64.Steps.refl _)
    have hpart := hruns.2 { st0 with status := .Halted } hsteps
    rcases hpart with ⟨_, hterm, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩
    · rcases hterm with ⟨_, hc, _⟩ | ⟨_, hc, _⟩ <;> cases hc
    · cases hc
    · cases hc
  · rfl

theorem not_cliNextCall_wrong_coinsLen {interp : ExternInterpretation} {r : ProtocolSetup} {t : CliTurn}
    {c : CliCall} (h : c.coins.length ≠ coinsLen c.cmd) : ¬ ValidCall interp r t c := fun hc => h hc.1
theorem not_canonicalPreKey_nil : ¬ CanonicalPreKey [] := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩; simp [preKeyWire] at h
theorem not_cliNextCall_init_when_session_exists {interp : ExternInterpretation} {r : ProtocolSetup}
    {t : CliTurn} {c : CliCall} {peer : CryptoVerification.SignalSession.Address} {dir : String}
    (hcmd : c.cmd = .init peer dir) (hsess : t.records r r.alice ≠ none) : ¬ ValidCall interp r t c := by
  intro hc; have hm := hc.2.2.2.2; rw [hcmd] at hm; exact hsess hm.2.2.2.2.1
theorem not_cliNextCall_send_when_no_session {interp : ExternInterpretation} {r : ProtocolSetup}
    {t : CliTurn} {c : CliCall} {peer : CryptoVerification.SignalSession.Address}
    (hcmd : c.cmd = .send peer) (hsess : t.records r c.party = none) : ¬ ValidCall interp r t c := by
  intro hc; have hm := hc.2.2.2.2; rw [hcmd] at hm; exact hm.2.2.2.2 hsess

/-! ## `CoinSplit` and `CallsMatchSchedules` Checks -/
theorem coinSplit_multi_piece_and_tail_drop :
    CoinSplit [.rng [1#8, 2#8, 3#8, 4#8]] [.rng [1#8, 2#8], .rng [3#8]] := by
  simpa using CoinSplit.split (pieces := [[1#8, 2#8], [3#8]])
    (fun p hp => by simp at hp; rcases hp with rfl | rfl <;> decide) ⟨[4#8], rfl⟩ CoinSplit.nil
theorem coinSplit_preserves_non_rng :
    CoinSplit [.pt [9#8], .rng [1#8, 2#8], .send [7#8]] [.pt [9#8], .rng [1#8], .send [7#8]] := by
  refine CoinSplit.keep (fun _ h => nomatch h) ?_
  exact CoinSplit.split (pieces := [[1#8]]) (fun p hp => by simp at hp; subst hp; decide)
    ⟨[2#8], rfl⟩ (CoinSplit.keep (fun _ h => nomatch h) CoinSplit.nil)
theorem not_coinSplit_mismatched_send : ¬ CoinSplit [.send [1#8]] [.send [2#8]] := by
  have key : ∀ l1 l2, CoinSplit l1 l2 → l1 = [.send [1#8]] → l2 = [.send [2#8]] → False := by
    rintro _ _ (_ | ⟨_, _⟩ | _) hl hr
    · cases hl
    · injection hl with h1; injection hr with h2; rw [h1] at h2; simp at h2
    · cases hl
  exact fun h => key _ _ h rfl rfl
theorem not_coinSplit_non_prefix_rng : ¬ CoinSplit [.rng [0#8]] [.rng [1#8]] := by
  intro h; generalize hl : ([MachineEvent.rng [0#8]] : List MachineEvent) = l1 at h
  generalize hr : ([MachineEvent.rng [1#8]] : List MachineEvent) = l2 at h
  cases h with
  | nil => simp at hl
  | keep hne _ => simp at hl; exact hne [0#8] hl.1.symm
  | @split coins pieces τ τhw _ hpref hrest =>
    simp at hl; obtain ⟨rfl, rfl⟩ := hl; cases hrest
    rcases pieces with _ | ⟨p1, _ | ⟨p2, _⟩⟩ <;> simp at hr
    subst p1; rcases hpref with ⟨_, htl⟩; simp at htl
theorem not_coinSplit_empty_piece : ¬ CoinSplit [.rng [1#8]] [.rng [], .rng [1#8]] := by
  have key : ∀ l1 l2, CoinSplit l1 l2 → l1 = [.rng [1#8]] → l2 = [.rng [], .rng [1#8]] → False := by
    rintro _ _ (_ | ⟨hne, _⟩ | @⟨_, pieces, _, _, hne, _, hrest⟩) hl hr
    · cases hl
    · simp at hl; exact hne _ hl.1
    · simp at hl; obtain ⟨rfl, rfl⟩ := hl; cases hrest
      rcases pieces with _ | ⟨p1, _⟩ <;> simp at hr
      exact hne p1 (.head _) hr.1
  exact fun h => key _ _ h rfl rfl
theorem callsFit_last_ok_free (p q : Participant) :
    CallsMatchSchedules [(p, true), (q, false)] [p, q, p] (fun _ => true) := by
  refine ⟨⟨[p], rfl⟩, fun k _ _ hk hget => ?_⟩
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0; simp at hget; exact hget.2.symm
theorem not_callsFit_wrong_party {p q : Participant} (hne : p ≠ q) :
    ¬ CallsMatchSchedules [(p, true)] [q] (fun _ => true) := by rintro ⟨⟨_, h⟩, _⟩; simp at h; exact hne h.1
theorem not_callsFit_wrong_intermediate_ok (p q : Participant) :
    ¬ CallsMatchSchedules [(p, true), (q, true)] [p, q] (fun _ => false) := fun h => nomatch h.2 0 p true (by simp) rfl

/-! ## `HooksMatchInterpretation` Checks -/
theorem hooksAgree_cliWitness :
    ExternContractsHoldCli cliWitnessInterp ∧ HooksMatchInterpretation cliWitnessInterp cliWitnessHooks :=
  ⟨cliWitnessInterp_contracts, cliWitnessHooks_agree⟩
theorem not_hooksAgree_flipped_pubKey :
    ¬ HooksMatchInterpretation cliWitnessInterp
      { cliWitnessHooks with C := { cliWitnessHooks.C with pubKey := fun _ => List.Vector.replicate 32 0#8 } } := by
  intro h; have h1 := h.2.2.2.2.1 (List.Vector.replicate 32 0#8)
  have h2 := cliWitnessHooks_agree.2.2.2.2.1 (List.Vector.replicate 32 0#8)
  rw [h1] at h2; dsimp only [cliWitnessHooks] at h2
  have hne : (List.Vector.replicate 32 0#8).toList ≠
      Symbolic.Proofs.Swarm.WIT.Pure.exampleAgreement
        (List.Vector.replicate 32 0#8).toList Symbolic.Proofs.Swarm.WIT.Pure.exampleBasepoint := by decide
  injection h2 with heq; exact hne heq
theorem not_hooksAgree_flipped_torsionFree :
    ¬ HooksMatchInterpretation cliWitnessInterp
      { cliWitnessHooks with Q := { cliWitnessHooks.Q with isTorsionFree := fun _ => true } } := by
  intro h; have h1 := h.2.2.2.2.2.2.2.2 (List.Vector.replicate 160 0#8)
  have h2 := cliWitnessHooks_agree.2.2.2.2.2.2.2.2 (List.Vector.replicate 160 0#8)
  dsimp only [cliWitnessHooks] at h1 h2; rw [← h2] at h1; cases h1

/-! ## Falsifiability and Trace-Level Non-Tautology -/
theorem not_compRefinesCliBinary_nil : ¬ CompRefinesCliBinaryMoves [] := by rintro ⟨_, h, _⟩; cases h
theorem not_compAsmSecurityCliBinary_nil : ¬ CompAsmSecurityCliBinaryMoves [] := by rintro ⟨_, h, _⟩; cases h
theorem compRefinesCli_of_compAsmSecurityCli {ω : Type} {Agree : ExternInterpretation → ω → Prop}
    {R : ExternInterpretation → ω → Inputs → Option Outcome → Prop}
    (h : CompAsmSecurityCliMoves Agree R) : CompRefinesCliMoves Agree R :=
  fun interp hc W hw r hr => let ⟨S, hS⟩ := h interp hc W hw r hr
    ⟨S, fun τ calls htr who ok hfit => (hS τ calls htr who ok hfit).elim (Or.inl ∘ And.left) Or.inr⟩
def rogueRel : ExternInterpretation → Unit → Inputs → Option Outcome → Prop :=
  fun _ _ _ o => o = some (.exited 0 [] (fun _ => none))

private theorem exposures_kind_leak {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.kind = .leak := by
  rcases List.mem_append.mp hv with h1 | h2 <;> obtain ⟨_, _, hj⟩ := List.mem_filterMap.mp ‹_›
  · unfold pqExposureAt at hj; split at hj <;> cases hj <;> rfl
  · unfold trExposureAt at hj; split at hj <;> cases hj <;> rfl

private theorem runMoves_mem_vis_anchored :
    ∀ {ms : List Move} {tr : ExecTrace} {v : VisEntry},
      MovesAnchored ms tr → v ∈ (runMoves ms tr).2 →
      ∃ (m : Move) (tr0 : ExecTrace), m.LogsSessionCompletion tr0 ∧ v ∈ m.vis tr0 ∧ ∀ u ∈ m.vis tr0, u ∈ (runMoves ms tr).2
  | [], _, _, _, hv => by cases hv
  | m :: ms, tr, _, ⟨hm, hms⟩, hv => by
    rcases List.mem_append.mp hv with hv1 | hv2
    · exact ⟨m, tr, hm, hv1, fun _ hu => List.mem_append_left _ hu⟩
    · obtain ⟨m', tr0, hm', hv', hsub⟩ := runMoves_mem_vis_anchored hms hv2
      exact ⟨m', tr0, hm', hv', fun u hu => List.mem_append_right _ (hsub u hu)⟩

private theorem dec_next_of_msg_none (me : Participant) (s msgIdx pqIdx : Nat) (spqrIdx : UInt32)
    (w : Bool) (tr : ExecTrace) (hm : tr.getMessageSentAt msgIdx = none) :
    (Move.decrypt me s msgIdx pqIdx spqrIdx w).next tr = tr := by
  dsimp only [Move.next, Move.act, DY.Libsignal.TripleRatchet.messageDecrypt]
  simp only [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_getLocalState_tr_at (Inv := (· = tr)) me s tr rfl fun _ _ => ?_
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; simp only [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at (Inv := (· = tr)) msgIdx tr rfl fun msg hnet _ => ?_
  have hs : tr.getMessageSentAt msgIdx = some msg := by simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; unfold CompTrace.NetMsgAt at hnet; rw [hnet]
  rw [hm] at hs; cases hs

private theorem decSkip_next_of_msg_none (me : Participant) (s msgIdx skIdx pqIdx : Nat) (spqrIdx : UInt32)
    (w : Bool) (tr : ExecTrace) (hm : tr.getMessageSentAt msgIdx = none) :
    (Move.decryptSkipped me s msgIdx skIdx pqIdx spqrIdx w).next tr = tr := by
  dsimp only [Move.next, Move.act, DY.Libsignal.TripleRatchet.messageDecryptSkipped]
  simp only [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_getLocalState_tr_at (Inv := (· = tr)) me s tr rfl fun _ _ => ?_
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; simp only [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at (Inv := (· = tr)) msgIdx tr rfl fun msg hnet _ => ?_
  have hs : tr.getMessageSentAt msgIdx = some msg := by simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; unfold CompTrace.NetMsgAt at hnet; rw [hnet]
  rw [hm] at hs; cases hs

private theorem move_accept_has_recv {m : Move} {tr : ExecTrace} {v : VisEntry}
    (hanc : m.LogsSessionCompletion tr) (hv : v ∈ m.vis tr) (hk : v.kind = .accept) :
    ∃ u ∈ m.vis tr, u.kind = .recv ∧
      (u.layout = .preKeyRecv ∨ (∃ eks, u.layout = .preKeyInner eks) ∨ u.layout = .whisper) := by
  unfold Move.vis at hv ⊢
  rcases List.mem_append.mp hv with hv | hexp
  · match m, hanc, hv with
    | .aliceStart .., _, hv =>
      rcases List.mem_cons.mp (List.mem_of_mem_take hv) with rfl | hd
      · cases hk
      · exact absurd (hk.symm.trans (aliceDraws_kind _ _ hd)) (by decide)
    | .bobStart b _ kh _ mh _ _ shown, hanc, _ =>
      rcases shown with _ | _
      · exact absurd hanc.1 (by omega)
      · exact ⟨⟨.recv, received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList, .preKeyRecv, none⟩,
          List.mem_append_left _ (by simp [bobVis]), rfl, Or.inl rfl⟩
    | .encrypt .., _, hv =>
      rcases List.mem_append.mp hv with hd | hs
      · rcases encDraws_kind _ hd with h1 | h2 <;> exact absurd (hk.symm.trans ‹_›) (by decide)
      · simp only [↓reduceIte, encSend] at hs
        split at hs <;> [split at hs <;> (rcases List.mem_singleton.mp hs with rfl; cases hk); cases hs]
    | .encryptAbort .., _, hv | .encryptFail .., _, hv =>
      simp only [encVis, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hv
      rcases encDraws_kind _ hv with h1 | h2 <;> exact absurd (hk.symm.trans ‹_›) (by decide)
    | .decrypt me stateIdx msgIdx pqIdx spqrIdx wrapped, _, hv =>
      rcases hm : tr.getMessageSentAt msgIdx with _ | b
      · rw [dec_next_of_msg_none me stateIdx msgIdx pqIdx spqrIdx wrapped tr hm] at hv
        simp [decVis, hm, newRandoms, receivedPlaintext, newIndices] at hv
      · refine ⟨⟨.recv, [b], if wrapped then .preKeyInner (sessionBaseKeys tr stateIdx) else .whisper,
            none⟩, List.mem_append_left _ (by simp [decVis, hm]), rfl, ?_⟩
        cases wrapped <;> [exact Or.inr (Or.inr rfl); exact Or.inr (Or.inl ⟨_, rfl⟩)]
    | .decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrIdx wrapped, _, hv =>
      rcases hm : tr.getMessageSentAt msgIdx with _ | b
      · rw [decSkip_next_of_msg_none me stateIdx msgIdx skIdx pqIdx spqrIdx wrapped tr hm] at hv
        simp [decVis, hm, newRandoms, receivedPlaintext, newIndices] at hv
      · refine ⟨⟨.recv, [b], if wrapped then .preKeyInner (sessionBaseKeys tr stateIdx) else .whisper,
            none⟩, List.mem_append_left _ (by simp [decVis, hm]), rfl, ?_⟩
        cases wrapped <;> [exact Or.inr (Or.inr rfl); exact Or.inr (Or.inl ⟨_, rfl⟩)]
    | .reject _, _, hv =>
      rcases List.mem_cons.mp hv with rfl | hd
      · cases hk
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd; cases hk
    | .setup .., _, hv | .compromiseIK .., _, hv | .compromiseSPK .., _, hv
    | .compromisePQSPK .., _, hv | .compromiseOPK .., _, hv | .exposeKey .., _, hv
    | .exposeSpqr .., _, hv | .exposeSkipped .., _, hv | .attackerSend .., _, hv => cases hv
  · exact absurd (hk.symm.trans (exposures_kind_leak hexp)) (by decide)

private theorem forall2_mem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      (∀ x ∈ xs, ∃ y ∈ ys, R x y) ∧ (∀ y ∈ ys, ∃ x ∈ xs, R x y)
  | _, _, .nil => ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | _, _, .cons h hf => let ⟨hl, hr⟩ := forall2_mem hf
    ⟨(fun _ hx => (List.mem_cons.mp hx).elim (· ▸ ⟨_, .head _, h⟩) fun hm => let ⟨y, hy, r⟩ := hl _ hm; ⟨y, .tail _ hy, r⟩),
     (fun _ hy => (List.mem_cons.mp hy).elim (· ▸ ⟨_, .head _, h⟩) fun hm => let ⟨x, hx, r⟩ := hr _ hm; ⟨x, .tail _ hx, r⟩)⟩

theorem not_compRefinesCli_rogue : ¬ CompRefinesCliMoves (fun _ (_ : Unit) => True) rogueRel := by
  intro href
  obtain ⟨S, hS⟩ := href cliWitnessInterp cliWitnessInterp_contracts () trivial testRecords testRecords_wf
  let t0 := CliTurn.init (initDirs cliWitnessInterp testRecords)
  have hba : testRecords.bob ≠ testRecords.alice := testRecords_wf.1.symm
  have hd : t0.dirs testRecvPreKeyCall.party = filesOf bobInitFiles := by
    simp [t0, CliTurn.init, initDirs, testRecvPreKeyCall, hba, bobInitFiles]
  let inp : Inputs :=
    { argv := testRecvPreKeyCall.cmd.argv, dirs := partyDirs
      files := bobInitFiles ++ testRecvPreKeyCall.extra, stdin := auditPreKeyBytes }
  have hinp : InputsFor testRecvPreKeyCall (t0.dirs testRecvPreKeyCall.party) inp := by
    rw [hd]; exact inputsFor_of_cliFilePaths testRecvPreKeyCall _ bobInitFiles_fp (fun _ h => nomatch h)
      bobInitFiles_bounded (fun _ h => nomatch h) (by dsimp only [testRecvPreKeyCall]; decide)
  have htr : CliTracesMoves (rogueRel cliWitnessInterp ()) cliWitnessInterp testRecords t0
      [.recv auditPreKeyBytes, .rng (List.replicate 32 0#8), .accept []] [(testRecords.bob, true)] := by
    simpa [cliEntryEvents, cliExitEvents, testRecvPreKeyCall] using
      CliTracesMoves.step (Rel := rogueRel cliWitnessInterp ()) (leaks := []) (code := 0) (out := [])
        (files := fun _ => none) (fun _ h => nomatch h) cliNextCall_testRecvPreKeyCall hinp rfl (CliTracesMoves.done _)
  have hfit : CallsMatchSchedules [(testRecords.bob, true)] [testRecords.bob] (fun _ => true) :=
    ⟨List.prefix_rfl, fun _ _ _ hk _ => by simp at hk⟩
  rcases hS _ _ htr [testRecords.bob] (fun _ => true) hfit with
    ⟨τhw, g, ms, hsplit, hmp⟩ | ⟨σ₁, e, σ₂, _, _, _, heq, _, hc⟩
  · obtain ⟨pieces, hshape⟩ : ∃ pieces : List HwBytes,
        τhw = .recv auditPreKeyBytes :: (pieces.map MachineEvent.rng ++ [.accept []]) := by
      have step : ∀ a b, CoinSplit a b → a = [.recv auditPreKeyBytes, .rng (List.replicate 32 0#8), .accept []] →
          ∃ pieces : List HwBytes, b = .recv auditPreKeyBytes :: (pieces.map MachineEvent.rng ++ [.accept []]) := by
        rintro _ _ (_ | ⟨_, h1⟩ | _) ha; · cases ha
        · injection ha with he1 ha1; subst he1
          rcases h1 with _ | ⟨hne, _⟩ | @⟨_, pieces, _, _, _, _, h2⟩; · cases ha1
          · injection ha1 with he2 _; exact absurd he2 (hne _)
          · injection ha1 with _ ha2; rcases h2 with _ | ⟨_, _ | _ | _⟩ | _
            · cases ha2
            · injection ha2 with he3 _; subst he3; exact ⟨pieces, rfl⟩
            · injection ha2 with _ ha3; cases ha3
            · injection ha2 with _ ha3; cases ha3
            · cases ha2
        · cases ha
      exact step _ _ hsplit rfl
    subst hshape
    obtain ⟨hl, hr⟩ := forall2_mem hmp.2.2.2.2.2
    obtain ⟨vacc, hvacc_mem, hvacc_m⟩ := hl (.accept []) (by simp)
    have hvacc_k : vacc.kind = .accept := hvacc_m.1.symm
    have hvacc_ms : vacc ∈ (runMoves ms (setupTrace testRecords)).2 := by
      rcases List.mem_append.mp hvacc_mem with hset | hms
      · exact absurd (hvacc_k.symm.trans (exposures_kind_leak (by simpa [ProtocolSetup.setupMove, Move.vis] using hset))) (by decide)
      · exact hms
    obtain ⟨m, tr0, hm_anc, hv_m, hsub⟩ := runMoves_mem_vis_anchored hmp.2.1.2.2.1.2.1 hvacc_ms
    obtain ⟨u, hu_m, hu_k, hu_l⟩ := move_accept_has_recv hm_anc hv_m hvacc_k
    obtain ⟨e, he_mem, he_m⟩ := hr u (List.mem_append_right _ (hsub u hu_m))
    have he_eq : e = .recv auditPreKeyBytes := by
      have hk : eventKind e = .recv := he_m.1.trans hu_k
      simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at he_mem
      rcases he_mem with rfl | ⟨_, _, rfl⟩ | rfl <;> [rfl; cases hk; cases hk]
    subst he_eq
    rcases hu_l with hpr | ⟨eks, hpi⟩ | hwh
    · simp only [hpr, EventMatchesEntry, PreKeyRecvOpkMatches, eventBytes] at he_m; split at he_m
      · obtain ⟨_, p, hp, _⟩ := he_m.2; rw [parsePreKeyWire_auditPreKeyBytes] at hp; cases hp
      · obtain ⟨_, p, hp, _⟩ := he_m.2; rw [parsePreKeyWire_auditPreKeyBytes] at hp; cases hp
      · exact he_m.2
    · simp only [hpi, EventMatchesEntry, eventBytes] at he_m
      obtain ⟨_, p, _, hp, _⟩ := he_m.2; rw [parsePreKeyWire_auditPreKeyBytes] at hp; cases hp
    · simp only [hwh, EventMatchesEntry, eventBytes] at he_m; obtain ⟨_, _, hb⟩ := he_m.2
      have hh := congrArg List.head? hb; change some wirePrekeyTag = some wireWhisperTag at hh; cases hh
  · have he_mem : e ∈ σ₁ ++ e :: σ₂ := by simp
    rw [← heq] at he_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he_mem
    rcases he_mem with rfl | rfl | rfl
    · simp only [auditPreKeyBytes, preKeyWire] at hc
      rcases hc.2 with ⟨htag, _⟩ | ⟨p, hp, _⟩
      · simp [wirePrekeyTag, wireWhisperTag] at htag
      · change parsePreKeyWire auditPreKeyBytes = some p at hp; rw [parsePreKeyWire_auditPreKeyBytes] at hp; cases hp
    · exact hc
    · exact hc

theorem not_compAsmSecurityCli_rogue : ¬ CompAsmSecurityCliMoves (fun _ (_ : Unit) => True) rogueRel :=
  fun h => not_compRefinesCli_rogue (compRefinesCli_of_compAsmSecurityCli h)

/-! ## Dependency Checks -/

#print axioms DY.Libsignal.Composed.Refinement.Cli.initDirs
#print axioms DY.Libsignal.Composed.Refinement.Cli.FilesVisible
#print axioms DY.Libsignal.Composed.Refinement.Cli.InputsFor
#print axioms DY.Libsignal.Composed.Refinement.Cli.SamePath
#print axioms DY.Libsignal.Composed.Refinement.Cli.scrub
#print axioms DY.Libsignal.Composed.Refinement.Cli.CliTurn.after
#print axioms DY.Libsignal.Composed.Refinement.Cli.CliTurn.clearSession
#print axioms DY.Libsignal.Composed.Refinement.Cli.CoinSplit
#print axioms DY.Libsignal.Composed.Refinement.Cli.ValidCall
#print axioms DY.Libsignal.Composed.Refinement.Cli.CliTracesMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CallsMatchSchedules
#print axioms DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompAsmSecurityCliMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.HooksMatchInterpretation
#print axioms DY.Libsignal.Composed.Refinement.Cli.elfRel
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliElfMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinaryMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompAsmSecurityCliBinaryMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompExternsSatisfiableCli
#print axioms samePath_dot_aliases
#print axioms scrub_deletes_coins_and_bundle
#print axioms scrub_preserves_party_files
#print axioms clearSession_deletes_session_and_alias
#print axioms clearSession_preserves_non_session
#print axioms clearSession_bobOff_behavior
#print axioms leakRecords_bobOff
#print axioms not_cliNextCall_of_bobOff
#print axioms not_filesVisible_dot_or_stdio
#print axioms auditSessionBytes_wf
#print axioms cliNextCall_send_satisfiable
#print axioms cliNextCall_recv_whisper_satisfiable
#print axioms cliNextCall_recv_prekey_satisfiable
#print axioms cliTraces_clear_satisfiable
#print axioms cliTraces_stop_aborted_and_none_satisfiable
#print axioms not_cliNextCall_wrong_coinsLen
#print axioms not_canonicalPreKey_nil
#print axioms not_cliNextCall_init_when_session_exists
#print axioms not_cliNextCall_send_when_no_session
#print axioms coinSplit_multi_piece_and_tail_drop
#print axioms coinSplit_preserves_non_rng
#print axioms not_coinSplit_mismatched_send
#print axioms not_coinSplit_non_prefix_rng
#print axioms not_coinSplit_empty_piece
#print axioms callsFit_last_ok_free
#print axioms not_callsFit_wrong_party
#print axioms not_callsFit_wrong_intermediate_ok
#print axioms hooksAgree_cliWitness
#print axioms not_hooksAgree_flipped_pubKey
#print axioms not_hooksAgree_flipped_torsionFree
#print axioms not_compRefinesCliBinary_nil
#print axioms not_compAsmSecurityCliBinary_nil
#print axioms compRefinesCli_of_compAsmSecurityCli
#print axioms not_compRefinesCli_rogue
#print axioms not_compAsmSecurityCli_rogue
#print axioms DY.Libsignal.Composed.Refinement.Cli.CliReachable
#print axioms DY.Libsignal.Composed.Refinement.Cli.CliElfProgress
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinary
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinaryPlaced
#print axioms live_cliTraces_stop_aborted_only
#print axioms not_filesVisible_slash_or_dotdot
#print axioms cliReachable_step_and_clear_satisfiable
#print axioms not_cliElfProgress_udfElf
end Symbolic.Proofs.Tests.Refinement.Cli.StmtAuditSym
