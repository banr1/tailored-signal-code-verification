/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
public import Symbolic.Proofs.Refinement.Composed.Cli.Model
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3ModelV2SlotsBase
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3RpkSlot
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.Cli.DirBridgeAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.TopEvents
import Symbolic.Proofs.Swarm.UA.Assembly
import Symbolic.Proofs.Swarm.UA.SlotInit
import Symbolic.Proofs.Swarm.UA.SlotRecvW
import Symbolic.Proofs.Swarm.UA.SlotRpkNO
import Symbolic.Proofs.Swarm.UA.SlotRpkProm
import Symbolic.Proofs.Swarm.UA.SlotSend
import Symbolic.Proofs.Swarm.UA.Top
import Symbolic.Proofs.Swarm.UA.XlateInv

/-!
# Guarded Bounded-I/O Model Relation and Machine-Free Refinement

Defines the bounded-I/O postcondition `PqModelPostB2` and run relation `PqModelRelB2`, reduces
within-cap steps to `PqModelPost`, maps above-cap rejected steps to `RunRejected`, and proves
`comp_refines_cli_model_b2` from `comp_refines_cli_model`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli.ParD3
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames.LibsignalSession (GhostState SignalMessage)
open CryptoVerification.E2E (PreKeyBundleFields PreKeyMessageFields UnreachedPqxdhPrimitives PEParams
  RecordExtras initiateTapeLen wireWhisper wirePrekey djbKey kyberKey)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (Inputs Outcome PqParty PublicBundle filesOf encodeDir pqInputs
  pqInitInputs pqSendInputs pqRecvInputs pqxdhExpectedOutcome pqInitModel pqSendModel
  pqRecvWhisperModel pqRecvPrekeyModel PqSessionMatches PqxdhPartyInSpecDomain
  OutcomeMatchesModelExceptPath sessionFile partyAddress publicBundleOf bundleDir coinsFile
  partyDirs stdioPaths stdinCapBytes maxPlaintextBytes fileCapBytes)
open Symbolic.Swarm.CREF.Cli (interpOfParams initDirs_interpOfParams PqPartyInv PqDirInv
  RegularFileList regularFileList_encodeDir regularFile_root filesOf_append_of_regular
  filesOf_eq_none_of_forall_ne filesOf_ne_none_of_mem isScrubbedPath_encodeDir
  isScrubbedPath_congr IsScrubbedPath scrub_filesOf_pqInputs_reject inputsEquiv_pqInputs
  inputsEquiv_pqSendInputs inputsEquiv_pqRecvInputs caller_pqPartyInv_of_allowed
  wfPq_of_pqPartyInv records_of_pqPartyInv keyToBytes32_bytesToKey32 bytesToVec_toList_of_len
  peerOf_eq_addrE_other)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

/-! ## Guarded model postcondition and relation -/

/-- The five bundle filenames opened by `read_bundle`. -/
def bundleReadNamesB2 : List String :=
  ["identity-key", "registration-id", "signed-pre-key", "kyber-pre-key", "one-time-pre-key"]

/-- Every bundle file under `dirName` has length at most `fileCapBytes`. -/
def BundleReadWithinCapB2 (d : DirectorySnapshot) (dirName : String) : Prop :=
  ∀ name ∈ bundleReadNamesB2, ((d (dirName ++ "/" ++ name)).getD []).length ≤ fileCapBytes

instance (d : DirectorySnapshot) (dirName : String) :
    Decidable (BundleReadWithinCapB2 d dirName) := by
  unfold BundleReadWithinCapB2; infer_instance

/-- Guarded PQXDH model postcondition incorporating `stdinCapBytes`, `maxPlaintextBytes`, and
`fileCapBytes` rejection outcomes. -/
structure PqModelPostB2 (_interp : ExternInterpretation) (P : PEParams) (i : Inputs)
    (o : Outcome) : Prop where
  init : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (b : PreKeyBundleFields)
      (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none →
    InputsEquiv i (pqInitInputs P st b t) →
    o = pqxdhExpectedOutcome P (pqInitInputs P st b t) (pqInitModel X P st b t)
  send : ∀ (st : PqParty) (m : HwBytes) (coins : List.Vector (BitVec 8) 64),
    PqxdhPartyInSpecDomain P st → m.length < 2 ^ 32 →
    InputsEquiv i (pqSendInputs P st m coins) →
    o = if m.length > stdinCapBytes then
        .exited 2 [] (filesOf (pqSendInputs P st m coins).files)
      else if m.length > maxPlaintextBytes then
        .exited 1 [] (filesOf (pqSendInputs P st m coins).files)
      else
        pqxdhExpectedOutcome P (pqSendInputs P st m coins) (pqSendModel P st m coins.toList)
  recvWhisper : ∀ (st : PqParty) (body : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
    InputsEquiv i (pqRecvInputs P st (wireWhisper :: body) rc) →
    o = if (wireWhisper :: body).length > stdinCapBytes then
        .exited 2 [] (filesOf (pqRecvInputs P st (wireWhisper :: body) rc).files)
      else
        pqxdhExpectedOutcome P (pqRecvInputs P st (wireWhisper :: body) rc)
          (pqRecvWhisperModel P st body rc)
  recvPrekey : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (m : PreKeyMessageFields)
      (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: m.bytes) rc) →
    o = if (wirePrekey :: m.bytes).length > stdinCapBytes then
        .exited 2 [] (filesOf (pqRecvInputs P st (wirePrekey :: m.bytes) rc).files)
      else
        pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
          (pqRecvPrekeyModel X P st m rc)
  recvPrekeyNoMatch : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (x : RecordExtras)
      (g : GhostState HwBytes) (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → m.inner.length + 2048 < 2 ^ 32 →
    ¬ PqSessionMatches x g m →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: m.bytes) rc) →
    if (wirePrekey :: m.bytes).length > stdinCapBytes then
      o = .exited 2 [] (filesOf (pqRecvInputs P st (wirePrekey :: m.bytes) rc).files)
    else
      OutcomeMatchesModelExceptPath P (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
        (sessionFile (partyAddress st.party.other))
        (pqRecvPrekeyModel X P { st with session := none } m rc) o
  recvOther : ∀ (st : PqParty) (c : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → c.length < 2 ^ 32 →
    c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
    InputsEquiv i (pqRecvInputs P st c rc) →
    o = if c.length > stdinCapBytes then
        .exited 2 [] (filesOf (pqRecvInputs P st c rc).files)
      else
        .exited 1 [] (filesOf (pqRecvInputs P st c rc).files)
  recvPrekeyNoMatchSession : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (x : RecordExtras)
      (g : GhostState HwBytes) (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → m.inner.length + 2048 < 2 ^ 32 →
    (wirePrekey :: m.bytes).length ≤ stdinCapBytes →
    ¬ PqSessionMatches x g m →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: m.bytes) rc) →
    NoMatchSessionFile X P st x g m rc o
  recvOverStdinCap : ∀ (st : PqParty) (body : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → (wirePrekey :: body).length < 2 ^ 32 →
    (wirePrekey :: body).length > stdinCapBytes →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = .exited 2 [] (filesOf (pqRecvInputs P st (wirePrekey :: body) rc).files)
  recvPrekeyReject : ∀ (st : PqParty) (body : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
    (wirePrekey :: body).length ≤ stdinCapBytes →
    parsePreKey body = none →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = .exited 1 [] (filesOf (pqRecvInputs P st (wirePrekey :: body) rc).files)
  recvPrekeyUntyped : ∀ (st : PqParty) (body : HwBytes) (q : PreKeyFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
    (wirePrekey :: body).length ≤ stdinCapBytes →
    parsePreKey body = some q → preKeyOfBody? body = none →
    (∀ x g, st.session = some (x, g) → ¬ PqFieldsMatch x g q) →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = .exited 1 [] (filesOf (pqRecvInputs P st (wirePrekey :: body) rc).files)
  recvPrekeyMatching : ∀ (st : PqParty) (x : RecordExtras) (g : GhostState HwBytes)
      (body : HwBytes) (q : PreKeyFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → body.length < 2 ^ 32 →
    (wirePrekey :: body).length ≤ stdinCapBytes →
    parsePreKey body = some q → PqFieldsMatch x g q →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: body) rc)
      (pqRecvMatchingFieldsModel P st x g q rc)
  recvPrekeyParsed : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (body : HwBytes)
      (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
    (wirePrekey :: body).length ≤ stdinCapBytes →
    preKeyOfBody? body = some m → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: body) rc)
      (pqRecvPrekeyModel X P st m rc)
  recvPrekeyParsedNoMatch : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (x : RecordExtras)
      (g : GhostState HwBytes) (body : HwBytes) (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → body.length < 2 ^ 32 →
    (wirePrekey :: body).length ≤ stdinCapBytes →
    preKeyOfBody? body = some m → m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    OutcomeMatchesModelExceptPath P (pqRecvInputs P st (wirePrekey :: body) rc)
        (sessionFile (partyAddress st.party.other))
        (pqRecvPrekeyModel X P { st with session := none } m rc) o ∧
      NoMatchSessionFile X P st x g m rc o
  initFiles : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (files : List (String × HwBytes))
      (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none → BundleFilesFlat files →
    BundleReadWithinCapB2 (filesOf files) bundleDir →
    parseBundleFiles (filesOf files) = some (publicBundleOf b) →
    InputsEquiv i (pqInitInputsF P st files t) →
    ScrubAgree o (pqxdhExpectedOutcome P (pqInitInputsF P st files t) (pqInitModel X P st b t))
  initOverFileCap : ∀ (st : PqParty) (files : List (String × HwBytes))
      (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none → BundleFilesFlat files →
    ¬ BundleReadWithinCapB2 (filesOf files) bundleDir →
    InputsEquiv i (pqInitInputsF P st files t) →
    o = .exited 1 [] (filesOf (pqInitInputsF P st files t).files)
  initReject : ∀ (st : PqParty) (files : List (String × HwBytes))
      (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none → BundleFilesFlat files →
    parseBundleFiles (filesOf files) = none →
    InputsEquiv i (pqInitInputsF P st files t) →
    o = .exited 1 [] (filesOf (pqInitInputsF P st files t).files)

/-- Guarded PQXDH run relation allowing aborts, missing outcomes, or `PqModelPostB2` exits. -/
def PqModelRelB2 (interp : ExternInterpretation) (P : PEParams) (i : Inputs)
    (o : Option Outcome) : Prop :=
  (o = some .aborted ∨ o = none) ∨ ∃ out_o, o = some out_o ∧ PqModelPostB2 interp P i out_o

/-- Whole-protocol CLI refinement instantiated with `ModelAgree` and `PqModelRelB2`. -/
def CompRefinesCliModelB2 : Prop :=
  CompRefinesCli ModelAgree PqModelRelB2

/-! ## Within-cap reduction -/

private def CallWithinCap (c : CliCall) : Prop :=
  match c.cmd with
  | .init _ _ => BundleReadWithinCapB2 (filesOf c.bundle) bundleDir
  | .send _ => c.stdin.length ≤ maxPlaintextBytes
  | .recv _ => c.stdin.length ≤ stdinCapBytes

private instance (c : CliCall) : Decidable (CallWithinCap c) := by
  unfold CallWithinCap; cases c.cmd <;> infer_instance

private theorem maxPlaintextBytes_le_stdinCapBytes : maxPlaintextBytes ≤ stdinCapBytes := by
  decide

private theorem bundleReadName_props {name : String} (hm : name ∈ bundleReadNamesB2) :
    (bundleDir ++ "/" ++ name) ∉ stdioPaths ∧
    IsScrubbedPath (bundleDir ++ "/" ++ name) = true ∧
    Arm64.normalizePath (bundleDir ++ "/" ++ name) ≠ Arm64.normalizePath coinsFile := by
  simp only [bundleReadNamesB2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

private theorem filesOf_encodeDir_bundle_none (P : PEParams) (st : PqParty) {p : String}
    (hscr : IsScrubbedPath p = true) :
    filesOf (encodeDir P st) p = none :=
  filesOf_eq_none_of_forall_ne (regularFileList_encodeDir P st) fun f hf heq => by
    have := (isScrubbedPath_congr heq).symm.trans hscr
    rw [isScrubbedPath_encodeDir P st f hf] at this; cases this

private theorem filesOf_extra_bundle_eq {bundle : List (String × HwBytes)} (hflat : BundleFilesFlat bundle)
    (coins : HwBytes) {p : String}
    (hne : Arm64.normalizePath p ≠ Arm64.normalizePath coinsFile) :
    filesOf (bundle ++ [(coinsFile, coins)]) p = filesOf bundle p := by
  have hreg_b : RegularFileList bundle := regularFileList_of_bundleFilesFlat hflat
  have hreg_c : RegularFileList [(coinsFile, coins)] :=
    regularFile_root (by decide) (by decide) (by decide) (by decide)
  rw [filesOf_append_of_regular hreg_b hreg_c p]
  have hc_none : filesOf [(coinsFile, coins)] p = none :=
    filesOf_eq_none_of_forall_ne hreg_c fun f hf heq => by
      rcases List.mem_singleton.mp hf with rfl
      exact hne heq
  simp [hc_none]

private theorem filesOf_pqInitInputsF_bundle_eq (P : PEParams) (st : PqParty)
    {files : List (String × HwBytes)} (hflat : BundleFilesFlat files)
    (t : List.Vector (BitVec 8) initiateTapeLen) {name : String} (hm : name ∈ bundleReadNamesB2) :
    filesOf (pqInitInputsF P st files t).files (bundleDir ++ "/" ++ name) =
      filesOf files (bundleDir ++ "/" ++ name) := by
  obtain ⟨_, hscr, hne⟩ := bundleReadName_props hm
  have hreg_f : RegularFileList files := regularFileList_of_bundleFilesFlat hflat
  have hreg_c : RegularFileList [(coinsFile, t.toList)] :=
    regularFile_root (by decide) (by decide) (by decide) (by decide)
  change filesOf (encodeDir P st ++ files ++ [(coinsFile, t.toList)]) _ = _
  rw [List.append_assoc,
      filesOf_append_of_regular (regularFileList_encodeDir P st) (hreg_f.append hreg_c),
      filesOf_extra_bundle_eq hflat t.toList hne,
      filesOf_encodeDir_bundle_none P st hscr, Option.or_none]

private theorem cmd_not_send_of_not_send {c : CliCall} {a : CryptoVerification.SignalSession.Address}
    (h : c.cmd.argv = ["send", a.text]) : ∃ peer, c.cmd = .send peer := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, rfl⟩

private theorem cmd_is_recv_of_argv {c : CliCall} {a : CryptoVerification.SignalSession.Address}
    (h : c.cmd.argv = ["recv", a.text]) : ∃ peer, c.cmd = .recv peer := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, rfl⟩

private theorem cmd_is_init_of_argv {c : CliCall} {a : CryptoVerification.SignalSession.Address}
    {dir : String} (h : c.cmd.argv = ["init", a.text, dir]) : ∃ peer d, c.cmd = .init peer d := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, _, rfl⟩

private theorem pqModelPost_of_b2_withinCap {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {i : Inputs} {o : Outcome}
    {st₀ : PqParty}
    (hnext : ValidCall interp r t c)
    (hin : InputsFor c (t.dirs c.party) i)
    (hdir₀ : t.dirs c.party = filesOf (encodeDir P st₀))
    (hcap : CallWithinCap c)
    (hpost : PqModelPostB2 interp P i o) :
    PqModelPost interp P i o where
  init := hpost.init
  send := fun st m coins hwf hlen heq => by
    obtain ⟨peer, hcmd⟩ := cmd_not_send_of_not_send (hin.1.symm.trans heq.1)
    have hm_eq : m = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle_pt : m.length ≤ maxPlaintextBytes := by
      rw [hm_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hle_sc : m.length ≤ stdinCapBytes := Nat.le_trans hle_pt maxPlaintextBytes_le_stdinCapBytes
    have hs := hpost.send st m coins hwf hlen heq
    simp only [Nat.not_lt.mpr hle_sc, Nat.not_lt.mpr hle_pt, ↓reduceIte] at hs
    exact hs
  recvWhisper := fun st body rc hwf hlen heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wireWhisper :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wireWhisper :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hs := hpost.recvWhisper st body rc hwf hlen heq
    simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hs
    exact hs
  recvPrekey := fun X st m rc hwf hlen hmatch heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: m.bytes) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: m.bytes).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hs := hpost.recvPrekey X st m rc hwf hlen hmatch heq
    simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hs
    exact hs
  recvPrekeyNoMatch := fun X st x g m rc hwf hsess hlen hnm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: m.bytes) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: m.bytes).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hs := hpost.recvPrekeyNoMatch X st x g m rc hwf hsess hlen hnm heq
    simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hs
    exact hs
  recvOther := fun st c_in rc hwf hlen hw hp heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : c_in = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : c_in.length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hs := hpost.recvOther st c_in rc hwf hlen hw hp heq
    simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hs
    exact hs
  recvPrekeyNoMatchSession := fun X st x g m rc hwf hsess hlen hnm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: m.bytes) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: m.bytes).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyNoMatchSession X st x g m rc hwf hsess hlen hle hnm heq
  recvPrekeyReject := fun st body rc hwf hlen hnone heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyReject st body rc hwf hlen hle hnone heq
  recvPrekeyUntyped := fun st body q rc hwf hlen hq hnone hnm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyUntyped st body q rc hwf hlen hle hq hnone hnm heq
  recvPrekeyMatching := fun st x g body q rc hwf hsess hlen hq hfm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyMatching st x g body q rc hwf hsess hlen hle hq hfm heq
  recvPrekeyParsed := fun X st body m rc hwf hlen hm hinner hmatch heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyParsed X st body m rc hwf hlen hle hm hinner hmatch heq
  recvPrekeyParsedNoMatch := fun X st x g body m rc hwf hsess hlen hm hinner hnm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyParsedNoMatch X st x g body m rc hwf hsess hlen hle hm hinner hnm heq
  initFiles := fun X st files b tVec hwf hsess hflat hparse heq => by
    obtain ⟨peer, d, hcmd⟩ := cmd_is_init_of_argv (hin.1.symm.trans heq.1)
    have hguard := hnext.2.2.2.2
    rw [hcmd] at hguard
    have hflat_c : BundleFilesFlat c.bundle := hguard.2.2.2.2.2.1
    have hcap_c : BundleReadWithinCapB2 (filesOf c.bundle) bundleDir := by
      simpa [CallWithinCap, hcmd] using hcap
    have hcap_f : BundleReadWithinCapB2 (filesOf files) bundleDir := by
      intro name hm
      obtain ⟨hns, hscr, hne_coins⟩ := bundleReadName_props hm
      have hi_eq := hin.2.2.2.1 (bundleDir ++ "/" ++ name) hns
      rw [hdir₀, filesOf_encodeDir_bundle_none P st₀ hscr, Option.or_none,
          CliCall.extra, filesOf_extra_bundle_eq hflat_c c.coins hne_coins] at hi_eq
      have hf_eq := (heq.2.2.2 (bundleDir ++ "/" ++ name)).symm.trans hi_eq
      rw [filesOf_pqInitInputsF_bundle_eq P st hflat tVec hm] at hf_eq
      rw [hf_eq]
      exact hcap_c name hm
    exact hpost.initFiles X st files b tVec hwf hsess hflat hcap_f hparse heq
  initReject := hpost.initReject

/-! ## Above-cap step rejection -/

private theorem after_eq_self_of_ne_zero {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hne : code ≠ 0) (hscr : scrub files = t.dirs c.party) :
    t.after r c code out files = t := by
  rcases t with ⟨dirs, sent, bobOff⟩
  cases code with
  | zero => exact absurd rfl hne
  | succ _ =>
    cases c.cmd <;>
      (dsimp only [CliTurn.after]; congr 1
       · funext q; split_ifs with hq <;> [exact hq ▸ hscr; rfl]
       · exact List.append_nil sent
       · simp)

private theorem caller_st_of_validCall {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t_clean : CliTurn} {accepted : List HwBytes} {c : CliCall}
    (hr : ProtocolSetupWF r)
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hnext : ValidCall interp r t c) :
    (c.party = r.alice ∨ c.party = r.bob) ∧
    ∃ st₀, PqPartyInv (interpOfParams interp P) P r accepted c.party st₀ (t.dirs c.party) ∧
      PqxdhPartyInSpecDomain P st₀ := by
  obtain ⟨_, _, hfb, hbca, hguard⟩ := hnext
  have hp : c.party = r.alice ∨ c.party = r.bob := by
    cases hm : c.cmd <;> rw [hm] at hguard
    · exact Or.inl hguard.1
    · exact hguard.1
    · exact hguard.1
  obtain ⟨hd_eq, _, _⟩ := clean_dirs_caller_eq hr hsim hbca hp
  have hbca_clean : BobCallAllowed r t_clean c := fun hbo =>
    absurd (hsim.clean_bobOff.symm.trans hbo) Bool.false_ne_true
  obtain ⟨_, st₀, hst_clean⟩ := caller_pqPartyInv_of_allowed hsim.dirInv hbca_clean hp
  have hst₀ : PqPartyInv (interpOfParams interp P) P r accepted c.party st₀ (t.dirs c.party) :=
    hd_eq ▸ hst_clean
  exact ⟨hp, st₀, hst₀, wfPq_of_pqPartyInv hst₀ hfb⟩

private theorem aboveCap_exited_reject {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t_clean : CliTurn} {accepted : List HwBytes}
    {c : CliCall} {i : Inputs} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hr : ProtocolSetupWF r)
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hnext : ValidCall interp r t c)
    (hin : InputsFor c (t.dirs c.party) i)
    (hnot_cap : ¬ CallWithinCap c)
    (hpost : PqModelPostB2 interp P i (.exited code out files)) :
    code ≠ 0 ∧ out = [] ∧ t.after r c code out files = t ∧
      RunRejected (runEventOf c (some (code, out))) := by
  obtain ⟨_, st₀, hst₀, hwf₀⟩ := caller_st_of_validCall hr hsim hnext
  obtain ⟨hcoins, hsb, _, _, hguard⟩ := hnext
  have hpeer : peerOf r c.party = partyAddress st₀.party.other := by
    rw [peerOf_eq_addrE_other, ← hst₀.party_eq]
  have hin_enc : InputsFor c (filesOf (encodeDir P st₀)) i := hst₀.dir_eq ▸ hin
  have hex_rej : (code = 1 ∨ code = 2) ∧ out = [] ∧ scrub files = t.dirs c.party := by
    cases hm : c.cmd with
    | init peer dir =>
      rw [hm] at hcoins hguard
      obtain ⟨hal, rfl, rfl, hstdin, hrec_none, hflat, _⟩ := hguard
      have hcap' : ¬ BundleReadWithinCapB2 (filesOf c.bundle) bundleDir := by
        simpa [CallWithinCap, hm] using hnot_cap
      have hsess : st₀.session = none := by
        have hrec := records_of_pqPartyInv hst₀
        rw [hal, hrec_none] at hrec
        cases hs : st₀.session <;> simp [hs] at hrec
        rfl
      have hc192 : c.coins.length = initiateTapeLen := by simpa [coinsLen, initiateTapeLen] using hcoins
      let tVec : List.Vector (BitVec 8) initiateTapeLen := bytesToVec initiateTapeLen c.coins
      have htVec : tVec.toList = c.coins := bytesToVec_toList_of_len hc192
      have hcmd_st : c.cmd = .init (partyAddress st₀.party.other) bundleDir := by
        rw [hm, ← hal, hpeer]
      have heq : InputsEquiv i (pqInitInputsF P st₀ c.bundle tVec) := by
        unfold pqInitInputsF; rw [← hcmd_st, htVec, ← hstdin]
        exact inputsEquiv_pqInputs hin_enc (regularFileList_of_bundleFilesFlat hflat) rfl
      have ho := hpost.initOverFileCap st₀ c.bundle tVec hwf₀ hsess hflat hcap' heq
      injection ho with hc hout hfs
      refine ⟨Or.inl hc, hout, ?_⟩
      rw [hfs, hst₀.dir_eq]
      exact scrub_filesOf_pqInputs_reject P st₀ _ c.bundle tVec.toList []
        (regularFileList_of_bundleFilesFlat hflat) (isScrubbedPath_of_bundleFilesFlat hflat)
    | send peer =>
      rw [hm] at hcoins hguard
      obtain ⟨_, rfl, hbun, _, _⟩ := hguard
      have hsb' : c.stdin.length < 2 ^ 32 := by simpa [StdinBounded, hm] using hsb
      have hgt_pt : c.stdin.length > maxPlaintextBytes :=
        Nat.lt_of_not_ge (by simpa [CallWithinCap, hm] using hnot_cap)
      have hc64 : c.coins.length = 64 := by simpa [coinsLen] using hcoins
      let coinsVec : List.Vector (BitVec 8) 64 := bytesToVec 64 c.coins
      have heq : InputsEquiv i (pqSendInputs P st₀ c.stdin coinsVec) :=
        inputsEquiv_pqSendInputs hin_enc (by rw [hm, hpeer]) hbun (bytesToVec_toList_of_len hc64).symm
      have ho := hpost.send st₀ c.stdin coinsVec hwf₀ hsb' heq
      have hscr0 : scrub (filesOf (pqSendInputs P st₀ c.stdin coinsVec).files) = t.dirs c.party := by
        rw [hst₀.dir_eq]
        exact scrub_filesOf_pqInputs_reject P st₀ _ [] coinsVec.toList c.stdin
          (fun _ h => by cases h) (fun _ h => by cases h)
      by_cases hgt_sc : c.stdin.length > stdinCapBytes
      · simp only [hgt_sc, ↓reduceIte] at ho
        injection ho with hc hout hfs
        exact ⟨Or.inr hc, hout, hfs ▸ hscr0⟩
      · simp only [hgt_sc, hgt_pt, ↓reduceIte] at ho
        injection ho with hc hout hfs
        exact ⟨Or.inl hc, hout, hfs ▸ hscr0⟩
    | recv peer =>
      rw [hm] at hcoins hguard
      obtain ⟨_, rfl, hbun, _⟩ := hguard
      have hgt_sc : c.stdin.length > stdinCapBytes :=
        Nat.lt_of_not_ge (by simpa [CallWithinCap, hm] using hnot_cap)
      have hc32 : c.coins.length = 32 := by simpa [coinsLen] using hcoins
      let rc : BitVec 256 := CryptoGames.HKDF.bytesToKey32 c.coins
      have heq : InputsEquiv i (pqRecvInputs P st₀ c.stdin rc) :=
        inputsEquiv_pqRecvInputs hin_enc (by rw [hm, hpeer]) hbun (keyToBytes32_bytesToKey32 hc32).symm
      have hscr0 : scrub (filesOf (pqRecvInputs P st₀ c.stdin rc).files) = t.dirs c.party := by
        rw [hst₀.dir_eq]
        exact scrub_filesOf_pqInputs_reject P st₀ _ [] (CryptoGames.HMAC.keyToBytes32 rc) c.stdin
          (fun _ h => by cases h) (fun _ h => by cases h)
      cases hst_in : c.stdin with
      | nil =>
        rw [hst_in] at hgt_sc
        exact absurd hgt_sc (by decide)
      | cons b0 body =>
        by_cases hbw : b0 = wireWhisper
        · subst hbw
          have htag : wireWhisper = wireWhisperTag := rfl
          have hbody_lt : body.length < 2 ^ 32 := by
            unfold StdinBounded at hsb; rw [hm] at hsb
            exact hsb.1 body (hst_in.trans (by rw [htag]))
          rw [hst_in] at heq hgt_sc hscr0
          have ho := hpost.recvWhisper st₀ body rc hwf₀ hbody_lt heq
          simp only [hgt_sc, ↓reduceIte] at ho
          injection ho with hc hout hfs
          exact ⟨Or.inr hc, hout, hfs ▸ hscr0⟩
        · by_cases hbp : b0 = wirePrekey
          · subst hbp
            have hnot_w : (wirePrekey :: body).head? ≠ some wireWhisperTag := by
              intro h; injection h with h; revert h; decide
            have hlen_lt : (wirePrekey :: body).length < 2 ^ 32 := by
              unfold StdinBounded at hsb; rw [hm, hst_in] at hsb
              exact hsb.2.1 hnot_w
            rw [hst_in] at heq hgt_sc hscr0
            have ho := hpost.recvOverStdinCap st₀ body rc hwf₀ hlen_lt hgt_sc heq
            injection ho with hc hout hfs
            exact ⟨Or.inr hc, hout, hfs ▸ hscr0⟩
          · have hnot_w : (b0 :: body).head? ≠ some wireWhisperTag := fun h =>
              hbw (Option.some.inj h)
            have hlen_lt : (b0 :: body).length < 2 ^ 32 := by
              unfold StdinBounded at hsb; rw [hm, hst_in] at hsb
              exact hsb.2.1 hnot_w
            rw [hst_in] at heq hgt_sc hscr0
            have ho := hpost.recvOther st₀ (b0 :: body) rc hwf₀ hlen_lt
              (fun h => hbw (Option.some.inj h)) (fun h => hbp (Option.some.inj h)) heq
            simp only [hgt_sc, ↓reduceIte] at ho
            injection ho with hc hout hfs
            exact ⟨Or.inr hc, hout, hfs ▸ hscr0⟩
  obtain ⟨hc12, hout, hscr⟩ := hex_rej
  have hne : code ≠ 0 := by rcases hc12 with rfl | rfl <;> decide
  refine ⟨hne, hout, after_eq_self_of_ne_zero hne hscr, fun out' hex => ?_⟩
  simp only [runEventOf, Option.some.injEq, Prod.mk.injEq] at hex
  exact hne hex.1

private theorem coins_le_maxLfs {c : CliCall} (h : c.coins.length = coinsLen c.cmd) :
    c.coins.length ≤ Arm64.MAX_LFS_FILESIZE := by
  have hmax : 192 ≤ Arm64.MAX_LFS_FILESIZE := by decide
  rw [h]
  cases c.cmd <;> simp only [coinsLen] <;> omega

private theorem inputsFor_pqInputs_nil {P : PEParams} {st : PqParty} {c₀ : CliCall}
    {d : DirectorySnapshot} (hdir : d = filesOf (encodeDir P st))
    (hbun : c₀.bundle = []) (hwf : PqxdhPartyInSpecDomain P st)
    (hcoins : c₀.coins.length ≤ Arm64.MAX_LFS_FILESIZE) :
    InputsFor c₀ d (pqInputs P st c₀.cmd [] c₀.coins c₀.stdin) := by
  have hreg_ed : RegularFileList (encodeDir P st) := regularFileList_encodeDir P st
  have hreg_c : RegularFileList [(coinsFile, c₀.coins)] :=
    regularFile_root (by decide) (by decide) (by decide) (by decide)
  have hreg_all : RegularFileList (encodeDir P st ++ [] ++ [(coinsFile, c₀.coins)]) :=
    (hreg_ed.append (fun _ h => by cases h)).append hreg_c
  have hmax : 2 ^ 31 ≤ Arm64.MAX_LFS_FILESIZE := by decide
  have hload := (CryptoVerification.SignalSession.loadable_pqRecvInputs P st [] 0#256).2
  have hvis : ∀ f ∈ encodeDir P st ++ [] ++ [(coinsFile, c₀.coins)],
      (Arm64.hasLeadingSlash f.1 = false ∧ Arm64.hasDotDot f.1 = false) ∧
        f.2.length ≤ Arm64.MAX_LFS_FILESIZE := by
    intro f hf
    rcases List.mem_append.mp hf with hf' | hf'
    · rw [List.append_nil] at hf'
      refine ⟨hload f (by simp [pqRecvInputs, pqInputs, hf']), ?_⟩
      exact Nat.le_trans (Nat.le_of_lt (hwf.2.1 f hf').1) hmax
    · rw [List.mem_singleton] at hf'
      subst hf'
      exact ⟨hload (coinsFile, CryptoGames.HMAC.keyToBytes32 0#256)
        (by simp [pqRecvInputs, pqInputs]), hcoins⟩
  refine ⟨rfl, rfl, rfl, fun p _ => ?_,
    fun f hf => ⟨(hreg_all f hf).1, (hreg_all f hf).2.1, (hvis f hf).1.1, (hvis f hf).1.2,
      (hvis f hf).2⟩⟩
  dsimp only [pqInputs, CliCall.extra]
  rw [hdir, List.append_nil, hbun, List.nil_append,
    filesOf_append_of_regular hreg_ed hreg_c p]

private theorem parseBundleFiles_empty : parseBundleFiles (filesOf []) = none := by
  have hnone : filesOf [] (bundleDir ++ "/" ++ "identity-key") = none :=
    filesOf_eq_none_of_forall_ne (fun _ h => by cases h) (fun _ h => by cases h)
  have hec : ecKeyParses [] = false := by decide
  unfold parseBundleFiles
  simp [hnone, parseEcKey, hec]

private theorem dummy_inCap_rejected_step {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t_clean : CliTurn} {accepted : List HwBytes} {c : CliCall}
    (hr : ProtocolSetupWF r)
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hnext : ValidCall interp r t c) :
    ∃ c₀ i₀ files₀,
      ValidCall interp r t c₀ ∧
      InputsFor c₀ (t.dirs c₀.party) i₀ ∧
      PqModelRel interp P i₀ (some (.exited 1 [] files₀)) ∧
      t.after r c₀ 1 [] files₀ = t ∧
      RunRejected (runEventOf c₀ (some (1, []))) ∧
      (∀ peer, (runEventOf c₀ (some (1, []))).cmd ≠ .send peer) := by
  obtain ⟨hp, st₀, hst₀, hwf₀⟩ := caller_st_of_validCall hr hsim hnext
  obtain ⟨_, _, hfb, hbca, hguard⟩ := hnext
  have hpeer : peerOf r c.party = partyAddress st₀.party.other := by
    rw [peerOf_eq_addrE_other, ← hst₀.party_eq]
  cases hm : c.cmd with
  | init _ _ =>
    rw [hm] at hguard
    have hal : c.party = r.alice := hguard.1
    have hrec_none : t.records r r.alice = none := hguard.2.2.2.2.1
    let tVec₀ : List.Vector (BitVec 8) initiateTapeLen := List.Vector.replicate initiateTapeLen 0#8
    let c₀ : CliCall :=
      { party := r.alice, cmd := .init (peerOf r r.alice) bundleDir, bundle := [],
        stdin := [], coins := tVec₀.toList }
    let i₀ : Inputs := pqInitInputsF P st₀ [] tVec₀
    have hc_eq : c₀.cmd = .init (partyAddress st₀.party.other) bundleDir := by
      dsimp only [c₀]; rw [← hal, hpeer]
    have hi₀_eq : i₀ = pqInputs P st₀ c₀.cmd [] c₀.coins c₀.stdin := by
      unfold i₀ pqInitInputsF; rw [← hc_eq]
    have hfb₀ : FilesBounded (t.dirs c₀.party) := by dsimp only [c₀]; rwa [← hal]
    have hdir₀ : t.dirs c₀.party = filesOf (encodeDir P st₀) := by
      dsimp only [c₀]; rw [← hal]; exact hst₀.dir_eq
    have hvalid₀ : ValidCall interp r t c₀ :=
      ⟨(show tVec₀.toList.length = initiateTapeLen from tVec₀.2), trivial, hfb₀, fun _ => hr.1,
       rfl, rfl, rfl, rfl, hrec_none, (fun _ h => by cases h),
       (fun b hb => by rw [parseBundleFiles_empty] at hb; cases hb)⟩
    have hin₀ : InputsFor c₀ (t.dirs c₀.party) i₀ := by
      rw [hi₀_eq]; exact inputsFor_pqInputs_nil hdir₀ rfl hwf₀ (coins_le_maxLfs hvalid₀.1)
    have hid_none : filesOf i₀.files (bundleDir ++ "/" ++ "identity-key") = none := by
      exact (filesOf_pqInitInputsF_bundle_eq P st₀ (fun _ h => by cases h) tVec₀ (by decide)).trans
        (filesOf_eq_none_of_forall_ne (fun _ h => by cases h) (fun _ h => by cases h))
    have hpost₀ : PqModelPost interp P i₀ (.exited 1 [] (filesOf i₀.files)) :=
      { init := fun _ st' b t' _ _ heq => by
          exfalso
          have hmem : (bundleDir ++ "/identity-key", djbKey b.idPub) ∈
              (pqInitInputs P st' b t').files := by
            unfold pqInitInputs pqInputs PublicBundle.files
            simp only [List.mem_append, List.mem_cons]; left; right; left; left; rfl
          have hflat_b : BundleFilesFlat ((publicBundleOf b).files bundleDir) := by
            intro f hf; unfold PublicBundle.files at hf
            rcases hb_ot : (publicBundleOf b).oneTime with _ | ⟨id_o, k_o⟩ <;>
              simp only [hb_ot, List.append_nil, List.cons_append, List.nil_append,
                List.mem_cons, List.not_mem_nil, or_false] at hf
            · rcases hf with rfl | rfl | rfl | rfl
              · exact ⟨⟨"identity-key", by dsimp only; decide⟩, by simp [publicBundleOf, djbKey]⟩
              · exact ⟨⟨"registration-id", by dsimp only; decide⟩, by simp [CryptoVerification.SignalSession.le32]⟩
              · exact ⟨⟨"signed-pre-key", by dsimp only; decide⟩, by simp [publicBundleOf, djbKey, CryptoVerification.SignalSession.le32]⟩
              · exact ⟨⟨"kyber-pre-key", by dsimp only; decide⟩, by simp [publicBundleOf, CryptoVerification.E2E.kyberKey, CryptoVerification.SignalSession.le32]⟩
            · rcases hf with rfl | rfl | rfl | rfl | rfl
              · exact ⟨⟨"identity-key", by dsimp only; decide⟩, by simp [publicBundleOf, djbKey]⟩
              · exact ⟨⟨"registration-id", by dsimp only; decide⟩, by simp [CryptoVerification.SignalSession.le32]⟩
              · exact ⟨⟨"signed-pre-key", by dsimp only; decide⟩, by simp [publicBundleOf, djbKey, CryptoVerification.SignalSession.le32]⟩
              · exact ⟨⟨"kyber-pre-key", by dsimp only; decide⟩, by simp [publicBundleOf, CryptoVerification.E2E.kyberKey, CryptoVerification.SignalSession.le32]⟩
              · have hot_len : k_o.length = 33 := by
                  rcases ho : b.opk with _ | ⟨_, kv⟩ <;> simp [publicBundleOf, ho] at hb_ot
                  rcases hb_ot with ⟨_, rfl⟩; simp [djbKey]
                exact ⟨⟨"one-time-pre-key", by dsimp only; decide⟩, by simp [CryptoVerification.SignalSession.le32, hot_len]⟩
          have hreg' : RegularFileList (pqInitInputs P st' b t').files :=
            ((regularFileList_encodeDir P st').append (regularFileList_of_bundleFilesFlat hflat_b)).append
              (regularFile_root (by decide) (by decide) (by decide) (by decide))
          exact filesOf_ne_none_of_mem hreg' hmem rfl ((heq.2.2.2 _).symm.trans hid_none)
        send := fun _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqSendInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvWhisper := fun _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvPrekey := fun _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvPrekeyNoMatch := fun _ _ _ _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvOther := fun _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvPrekeyNoMatchSession := fun _ _ _ _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvPrekeyReject := fun _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvPrekeyUntyped := fun _ _ _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvPrekeyMatching := fun _ _ _ _ _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvPrekeyParsed := fun _ _ _ _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        recvPrekeyParsedNoMatch := fun _ _ _ _ _ _ _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
        initFiles := fun _ st' files' _ t' _ _ hflat' hparse heq => by
          exfalso
          have hf_none : filesOf files' (bundleDir ++ "/" ++ "identity-key") = none := by
            rw [← filesOf_pqInitInputsF_bundle_eq P st' hflat' t' (by decide),
                ← heq.2.2.2 (bundleDir ++ "/" ++ "identity-key"), hid_none]
          have hec : ecKeyParses [] = false := by decide
          unfold parseBundleFiles at hparse
          simp [hf_none, parseEcKey, hec] at hparse
        initReject := fun _ _ _ _ _ _ _ heq => congrArg _ (funext heq.2.2.2) }
    have hscr₀ : scrub (filesOf i₀.files) = t.dirs c₀.party := by
      dsimp only [c₀, i₀]; rw [← hal, hst₀.dir_eq]
      exact scrub_filesOf_pqInputs_reject P st₀ _ [] tVec₀.toList []
        (fun _ h => by cases h) (fun _ h => by cases h)
    exact ⟨c₀, i₀, filesOf i₀.files, hvalid₀, hin₀, PqModelRel.of_post hpost₀,
      after_eq_self_of_ne_zero Nat.one_ne_zero hscr₀,
      fun _ h => by simp [runEventOf] at h,
      fun _ h => by cases h⟩
  | send _ | recv _ =>
    rcases hp with hal | hbob
    ·
      have hrec_ne : t.records r r.alice ≠ none := by
        cases hm' : c.cmd <;> rw [hm'] at hm hguard
        · cases hm
        · exact hal ▸ hguard.2.2.2.2
        · rcases hguard.2.2.2 with ⟨hr_ne, _⟩ | ⟨hb, _⟩
          · exact hal ▸ hr_ne
          · exact absurd (hal.symm.trans hb) hr.1
      let c₀ : CliCall :=
        { party := r.alice, cmd := .recv (peerOf r r.alice), bundle := [],
          stdin := [wireWhisperTag], coins := CryptoGames.HMAC.keyToBytes32 0#256 }
      let i₀ : Inputs := pqRecvInputs P st₀ [wireWhisper] 0#256
      have hc_eq : c₀.cmd = .recv (partyAddress st₀.party.other) := by
        dsimp only [c₀]; rw [← hal, hpeer]
      have hi₀_eq : i₀ = pqInputs P st₀ c₀.cmd [] c₀.coins c₀.stdin := by
        unfold i₀ pqRecvInputs; rw [← hc_eq]; rfl
      have hfb₀ : FilesBounded (t.dirs c₀.party) := by dsimp only [c₀]; rwa [← hal]
      have hdir₀ : t.dirs c₀.party = filesOf (encodeDir P st₀) := by
        dsimp only [c₀]; rw [← hal]; exact hst₀.dir_eq
      have hsb₀ : StdinBounded c₀ := by
        refine ⟨fun body hb => ?_, fun h => absurd rfl h, fun q hq => ?_,
          fun _ _ _ _ _ _ _ _ _ _ _ hw => ?_⟩
        · injection hb with _ hnil; subst hnil; decide
        · simp [c₀, parsePreKeyWire, wireWhisperTag, DY.Libsignal.PQXDH.Refinement.wirePrekeyTag] at hq
        · unfold preKeyWire at hw
          simp [c₀, wireWhisperTag, DY.Libsignal.PQXDH.Refinement.wirePrekeyTag] at hw
      have hpq_nil : PqFromHonest t.sent [] := fun _ hm_try => by cases hm_try
      have hvalid₀ : ValidCall interp r t c₀ :=
        ⟨by simp [c₀, CryptoGames.HMAC.keyToBytes32, coinsLen], hsb₀, hfb₀, fun _ => hr.1,
         Or.inl rfl, rfl, rfl, Or.inl ⟨hrec_ne, [], rfl, hpq_nil⟩⟩
      have hin₀ : InputsFor c₀ (t.dirs c₀.party) i₀ := by
        rw [hi₀_eq]; exact inputsFor_pqInputs_nil hdir₀ rfl hwf₀ (coins_le_maxLfs hvalid₀.1)
      have hpost₀ : PqModelPost interp P i₀ (.exited 1 [] (filesOf i₀.files)) :=
        { init := fun _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputs, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
          send := fun _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqSendInputs, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
          recvWhisper := fun st' body' rc' _ _ heq => by
            have hcons : [wireWhisper] = wireWhisper :: body' := heq.2.2.1
            injection hcons with _ hb_nil; subst hb_nil
            have hmod : pqRecvWhisperModel P st' [] rc' = some none := by
              unfold pqRecvWhisperModel; cases st'.session <;> rfl
            rw [hmod]
            exact congrArg (Outcome.exited 1 []) (funext heq.2.2.2)
          recvPrekey := fun _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyNoMatch := fun _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvOther := fun _ _ _ _ _ hcw _ heq => by
            cases heq.2.2.1
            exact absurd rfl hcw
          recvPrekeyNoMatchSession := fun _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyReject := fun _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyUntyped := fun _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyMatching := fun _ _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyParsed := fun _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyParsedNoMatch := fun _ _ _ _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          initFiles := fun _ _ _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
          initReject := fun _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq }
      have hscr₀ : scrub (filesOf i₀.files) = t.dirs c₀.party := by
        dsimp only [c₀, i₀]; rw [← hal, hst₀.dir_eq]
        exact scrub_filesOf_pqInputs_reject P st₀ _ [] (CryptoGames.HMAC.keyToBytes32 0#256)
          [wireWhisper] (fun _ h => by cases h) (fun _ h => by cases h)
      exact ⟨c₀, i₀, filesOf i₀.files, hvalid₀, hin₀, PqModelRel.of_post hpost₀,
        after_eq_self_of_ne_zero Nat.one_ne_zero hscr₀,
        fun _ h => by simp [runEventOf] at h,
        fun _ h => by cases h⟩
    ·
      let c₀ : CliCall :=
        { party := r.bob, cmd := .recv (peerOf r r.bob), bundle := [],
          stdin := [], coins := CryptoGames.HMAC.keyToBytes32 0#256 }
      let i₀ : Inputs := pqRecvInputs P st₀ [] 0#256
      have hc_eq : c₀.cmd = .recv (partyAddress st₀.party.other) := by
        dsimp only [c₀]; rw [← hbob, hpeer]
      have hi₀_eq : i₀ = pqInputs P st₀ c₀.cmd [] c₀.coins c₀.stdin := by
        unfold i₀ pqRecvInputs; rw [← hc_eq]
      have hfb₀ : FilesBounded (t.dirs c₀.party) := by dsimp only [c₀]; rwa [← hbob]
      have hdir₀ : t.dirs c₀.party = filesOf (encodeDir P st₀) := by
        dsimp only [c₀]; rw [← hbob]; exact hst₀.dir_eq
      have hbca₀ : BobCallAllowed r t c₀ := fun hbo hpar => hbca hbo (hbob.trans hpar.symm)
      have hsb₀ : StdinBounded c₀ :=
        ⟨(fun _ hb => by cases hb), (fun _ => by dsimp only [c₀]; decide),
         (fun _ hq => by simp [c₀, parsePreKeyWire] at hq),
         (fun _ _ _ _ _ _ _ _ _ _ _ hw => by unfold preKeyWire at hw; simp [c₀] at hw)⟩
      have hvalid₀ : ValidCall interp r t c₀ :=
        ⟨by simp [c₀, CryptoGames.HMAC.keyToBytes32, coinsLen], hsb₀, hfb₀, hbca₀,
         Or.inr rfl, rfl, rfl,
         Or.inr ⟨rfl, Or.inl (by dsimp only [c₀]; decide), fun _ hq => by simp [c₀, parsePreKeyWire] at hq⟩⟩
      have hin₀ : InputsFor c₀ (t.dirs c₀.party) i₀ := by
        rw [hi₀_eq]; exact inputsFor_pqInputs_nil hdir₀ rfl hwf₀ (coins_le_maxLfs hvalid₀.1)
      have hpost₀ : PqModelPost interp P i₀ (.exited 1 [] (filesOf i₀.files)) :=
        { init := fun _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputs, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
          send := fun _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqSendInputs, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
          recvWhisper := fun _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekey := fun _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyNoMatch := fun _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvOther := fun _ _ _ _ _ _ _ heq => congrArg _ (funext heq.2.2.2)
          recvPrekeyNoMatchSession := fun _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyReject := fun _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyUntyped := fun _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyMatching := fun _ _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyParsed := fun _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          recvPrekeyParsedNoMatch := fun _ _ _ _ _ _ _ _ _ _ _ _ _ heq => by cases heq.2.2.1
          initFiles := fun _ _ _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq
          initReject := fun _ _ _ _ _ _ _ heq => by simp [InputsEquiv, i₀, pqInitInputsF, pqRecvInputs, pqInputs, CryptoVerification.SignalSession.Cmd.argv] at heq }
      have hscr₀ : scrub (filesOf i₀.files) = t.dirs c₀.party := by
        dsimp only [c₀, i₀]; rw [← hbob, hst₀.dir_eq]
        exact scrub_filesOf_pqInputs_reject P st₀ _ [] (CryptoGames.HMAC.keyToBytes32 0#256)
          [] (fun _ h => by cases h) (fun _ h => by cases h)
      exact ⟨c₀, i₀, filesOf i₀.files, hvalid₀, hin₀, PqModelRel.of_post hpost₀,
        after_eq_self_of_ne_zero Nat.one_ne_zero hscr₀,
        fun _ h => by simp [runEventOf] at h,
        fun _ h => by cases h⟩

/-! ## Event-level trace translation -/

private def RelEv (e e' : CliEvent) : Prop :=
  e = e' ∨ ∃ ev ev', e = .run ev ∧ e' = .run ev' ∧
    RunRejected ev ∧ RunRejected ev' ∧ (∀ peer, ev'.cmd ≠ .send peer)

private theorem relEv_refl (e : CliEvent) : RelEv e e := Or.inl rfl

private theorem forall₂_relEv_refl (l : List CliEvent) : List.Forall₂ RelEv l l :=
  List.forall₂_same.mpr fun _ _ => Or.inl rfl

private theorem forall₂_append {α β : Type} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys₁ ys₂ : List β}
    (h₁ : List.Forall₂ R xs₁ ys₁) (h₂ : List.Forall₂ R xs₂ ys₂) :
    List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hxy _ ih => exact .cons hxy ih

private theorem forall₂_append_split_right {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys₁ ys₂ : List β} (h : List.Forall₂ R xs (ys₁ ++ ys₂)) :
    ∃ xs₁ xs₂, xs = xs₁ ++ xs₂ ∧ List.Forall₂ R xs₁ ys₁ ∧ List.Forall₂ R xs₂ ys₂ := by
  induction ys₁ generalizing xs with
  | nil => exact ⟨[], xs, rfl, .nil, h⟩
  | cons y ys₁ ih =>
    cases h with
    | cons hxy hrest =>
      obtain ⟨xs₁, xs₂, rfl, h₁, h₂⟩ := ih hrest
      exact ⟨_ :: xs₁, xs₂, rfl, .cons hxy h₁, h₂⟩

private theorem forall₂_append_split_left {α β : Type} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys : List β} (h : List.Forall₂ R (xs₁ ++ xs₂) ys) :
    ∃ ys₁ ys₂, ys = ys₁ ++ ys₂ ∧ List.Forall₂ R xs₁ ys₁ ∧ List.Forall₂ R xs₂ ys₂ := by
  induction xs₁ generalizing ys with
  | nil => exact ⟨[], ys, rfl, .nil, h⟩
  | cons x xs₁ ih =>
    cases h with
    | cons hxy hrest =>
      obtain ⟨ys₁, ys₂, rfl, h₁, h₂⟩ := ih hrest
      exact ⟨_ :: ys₁, ys₂, rfl, .cons hxy h₁, h₂⟩

private theorem traces_b2_to_inCap {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t : CliTurn} {evs : List CliEvent}
    (htr : CliTraces (PqModelRelB2 interp P) interp r t evs) :
    ∀ {t_clean : CliTurn} {accepted : List HwBytes},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      ∃ evs', CliTraces (PqModelRel interp P) interp r t evs' ∧ List.Forall₂ RelEv evs evs' := by
  induction htr with
  | done t =>
    intro _ _ _
    exact ⟨[], .done t, .nil⟩
  | clear p _ ih =>
    intro _ _ hsim
    obtain ⟨evs', htr', hrel⟩ := ih (pqTurnSim1A_clearSession p hr hsim)
    exact ⟨evs', .clear p htr', hrel⟩
  | breakInvert hbi _ ih =>
    intro _ _ hsim
    obtain ⟨evs', htr', hrel⟩ := ih hsim
    exact ⟨.env _ :: evs', .breakInvert hbi htr', .cons (relEv_refl _) hrel⟩
  | @step t leaks c i code out files evs_rest hleak hnext hin hRel _ ih =>
    intro t_clean accepted hsim
    have hpost : PqModelPostB2 interp P i (.exited code out files) := by
      rcases hRel with (h | h) | ⟨_, ho, hp⟩
      · cases h
      · cases h
      · injection ho with ho'; exact ho' ▸ hp
    by_cases hcap : CallWithinCap c
    · obtain ⟨_, st₀, hst₀, _⟩ := caller_st_of_validCall hr hsim hnext
      have hpost1 : PqModelPost interp P i (.exited code out files) :=
        pqModelPost_of_b2_withinCap hnext hin hst₀.dir_eq hcap hpost
      have hRel1 : PqModelRel interp P i (some (.exited code out files)) :=
        PqModelRel.of_post hpost1
      obtain ⟨t_clean', accepted', hsim', _⟩ :=
        Symbolic.Proofs.Swarm.UA.Assembly.uaSlot_dispatch
          Symbolic.Proofs.Swarm.UA.SlotInit.slot_init_ua
          Symbolic.Proofs.Swarm.UA.SlotSend.slot_send_ua
          (Symbolic.Proofs.Swarm.UA.SlotRecvW.slot_recvw_ua_of
            Symbolic.Proofs.Swarm.UA.XlateInv.xlate_inv
            Symbolic.Proofs.Swarm.UA.Top.xlate_exc_w)
          Symbolic.Proofs.Swarm.UA.SlotRpkNO.slot_rpk_no_ua
          (Symbolic.Proofs.Swarm.UA.SlotRpkProm.slot_rpk_prom_ua_of_exc_w
            Symbolic.Proofs.Swarm.UA.Top.xlate_exc_w)
          interp P r hext hagree hr (evs_pre := []) hsim hnext hin hRel1
      obtain ⟨evs', htr', hrel⟩ := ih hsim'
      exact ⟨leaks ++ .run (runEventOf c (some (code, out))) :: evs',
        .step hleak hnext hin hRel1 htr',
        forall₂_append (forall₂_relEv_refl leaks) (.cons (relEv_refl _) hrel)⟩
    · obtain ⟨_, _, hafter, hrej⟩ := aboveCap_exited_reject hr hsim hnext hin hcap hpost
      have hsim' : PqTurnSim1A (interpOfParams interp P) P r
          (t.after r c code out files) t_clean accepted := hafter.symm ▸ hsim
      obtain ⟨evs', htr', hrel⟩ := ih hsim'
      obtain ⟨c₀, i₀, files₀, hvalid₀, hin₀, hRel₀, hafter₀, hrej₀, hnsend₀⟩ :=
        dummy_inCap_rejected_step hr hsim hnext
      have htr₀ : CliTraces (PqModelRel interp P) interp r
          (t.after r c₀ 1 [] files₀) evs' := hafter₀.symm ▸ (hafter ▸ htr')
      have hrel_step : RelEv (.run (runEventOf c (some (code, out))))
          (.run (runEventOf c₀ (some (1, [])))) :=
        Or.inr ⟨_, _, rfl, rfl, hrej, hrej₀, hnsend₀⟩
      exact ⟨leaks ++ .run (runEventOf c₀ (some (1, []))) :: evs',
        .step hleak hvalid₀ hin₀ hRel₀ htr₀,
        forall₂_append (forall₂_relEv_refl leaks) (.cons hrel_step hrel)⟩
  | @stop t leaks c i o hleak hnext hin hRel habort =>
    intro _ _ _
    exact ⟨leaks ++ [.run (runEventOf c none)],
      .stop hleak hnext hin (Or.inl habort) habort,
      forall₂_append (forall₂_relEv_refl leaks) (.cons (relEv_refl _) .nil)⟩

/-! ## Guard, explanation, and collision transfer -/

private theorem mem_env_of_forall₂_relEv {evs evs' : List CliEvent} {e : EnvEvent}
    (hrel : List.Forall₂ RelEv evs evs') (hm : CliEvent.env e ∈ evs) :
    CliEvent.env e ∈ evs' := by
  induction hrel with
  | nil => cases hm
  | @cons x y _ _ hxy _ ih =>
    rcases List.mem_cons.mp hm with rfl | htl
    · rcases hxy with rfl | ⟨_, _, h1, _⟩
      · exact List.mem_cons_self ..
      · cases h1
    · exact List.mem_cons_of_mem _ (ih htl)

private theorem mem_exit0_of_forall₂_relEv {evs evs' : List CliEvent} {ev : RunEvent} {out : HwBytes}
    (hrel : List.Forall₂ RelEv evs evs') (hm : CliEvent.run ev ∈ evs)
    (hex : ev.exit = some (0, out)) :
    CliEvent.run ev ∈ evs' := by
  induction hrel with
  | nil => cases hm
  | @cons x y _ _ hxy _ ih =>
    rcases List.mem_cons.mp hm with rfl | htl
    · rcases hxy with rfl | ⟨ev₁, _, h1, _, hrej₁, _⟩
      · exact List.mem_cons_self ..
      · cases h1; exact absurd hex (hrej₁ out)
    · exact List.mem_cons_of_mem _ (ih htl)

private theorem invertsGuarded_of_forall₂_relEv {interp : ExternInterpretation} {r : ProtocolSetup}
    {evs evs' : List CliEvent} (hrel : List.Forall₂ RelEv evs evs')
    (hg : InvertsGuarded interp r evs) :
    InvertsGuarded interp r evs' := by
  intro pre' post' e heq'
  rw [heq'] at hrel
  obtain ⟨pre, rest, rfl, hpre, hrest⟩ := forall₂_append_split_right hrel
  cases hrest with
  | @cons x _ post _ hxe _ =>
    have hx : x = .env e := by
      rcases hxe with rfl | ⟨_, _, _, h2, _⟩
      · rfl
      · cases h2
    subst hx
    have hg0 := hg pre post e rfl
    cases e with
    | invertDH pk sk =>
      obtain ⟨hbrk, hdh, hpk⟩ := hg0
      refine ⟨mem_env_of_forall₂_relEv hpre hbrk, ?_, hpk⟩
      rcases hdh with hsetup | ⟨ev, out, hm, hex, hsk⟩
      · exact Or.inl hsetup
      · exact Or.inr ⟨ev, out, mem_exit0_of_forall₂_relEv hpre hm hex, hex, hsk⟩
    | invertKEM pk sk =>
      obtain ⟨hbrk, hsk, hpk⟩ := hg0
      exact ⟨mem_env_of_forall₂_relEv hpre hbrk, hsk, hpk⟩
    | breakDH | breakKEM | leak _ _ | registerCorrupt _ _ => trivial

private theorem matchesEvents_of_forall₂_relEv_left {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {evs evs' : List CliEvent} (hrel : List.Forall₂ RelEv evs evs') :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss evs vis →
      MatchesEventsAt interp r S g initIds tr ss evs' vis := by
  induction hrel with
  | nil => exact fun h => h
  | @cons x y xs ys hxy _ ih =>
    intro initIds tr ss vis hm
    rcases hxy with rfl | ⟨ev, ev', rfl, rfl, hrej, hrej', _⟩
    · cases hm with
      | run1 hinv hrm hrest => exact .run1 hinv hrm (ih hrest)
      | run0 hinv hrj hrest => exact .run0 hinv hrj (ih hrest)
      | env hinv hem hrest => exact .env hinv hem (ih hrest)
    · cases hm with
      | run1 _ hrm _ =>
        obtain ⟨out, hex⟩ := hrm.2.2.2.2.2.1
        exact absurd hex (hrej out)
      | run0 hinv _ hrest =>
        exact .run0 hinv hrej' (ih hrest)

private theorem matchesEvents_of_forall₂_relEv_right {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {evs evs' : List CliEvent} (hrel : List.Forall₂ RelEv evs evs') :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss evs' vis →
      MatchesEventsAt interp r S g initIds tr ss evs vis := by
  induction hrel with
  | nil => exact fun h => h
  | @cons x y xs ys hxy _ ih =>
    intro initIds tr ss vis hm
    rcases hxy with rfl | ⟨ev, ev', rfl, rfl, hrej, hrej', _⟩
    · cases hm with
      | run1 hinv hrm hrest => exact .run1 hinv hrm (ih hrest)
      | run0 hinv hrj hrest => exact .run0 hinv hrj (ih hrest)
      | env hinv hem hrest => exact .env hinv hem (ih hrest)
    · cases hm with
      | run1 _ hrm _ =>
        obtain ⟨out, hex⟩ := hrm.2.2.2.2.2.1
        exact absurd hex (hrej' out)
      | run0 hinv _ hrest =>
        exact .run0 hinv hrej (ih hrest)

private theorem explains_iff_of_forall₂_relEv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {vis : List VisEntry} {evs evs' : List CliEvent}
    (hrel : List.Forall₂ RelEv evs evs') :
    Explains interp r S g ss vis evs ↔ Explains interp r S g ss vis evs' :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, matchesEvents_of_forall₂_relEv_left hrel h4⟩,
   fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, matchesEvents_of_forall₂_relEv_right hrel h4⟩⟩

private theorem readCollisionCli_iff_of_forall₂_relEv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {evs evs' : List CliEvent} (hrel : List.Forall₂ RelEv evs evs') :
    ReadCollisionCli interp r S g ss evs ↔ ReadCollisionCli interp r S g ss evs' := by
  constructor
  · rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
      rfl, hss, hcmd, hex, hrb, hm, hdec, hget, hcol⟩
    obtain ⟨evs'₁, rest', rfl, hrel₁, hrest⟩ := forall₂_append_split_left hrel
    cases hrest with
    | @cons _ y _ evs'₂ hxy _ =>
      have hy : y = .run ev := by
        rcases hxy with rfl | ⟨_, _, h1, _, hrej, _⟩
        · rfl
        · cases h1; exact absurd hex (hrej out)
      subst hy
      exact ⟨evs'₁, ev, evs'₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
        rfl, hss, hcmd, hex, hrb, matchesEvents_of_forall₂_relEv_left hrel₁ hm, hdec, hget, hcol⟩
  · rintro ⟨evs'₁, ev, evs'₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
      rfl, hss, hcmd, hex, hrb, hm, hdec, hget, hcol⟩
    obtain ⟨evs₁, rest, rfl, hrel₁, hrest⟩ := forall₂_append_split_right hrel
    cases hrest with
    | @cons x _ evs₂ _ hxy _ =>
      have hx : x = .run ev := by
        rcases hxy with rfl | ⟨_, _, _, h2, _, hrej', _⟩
        · rfl
        · cases h2; exact absurd hex (hrej' out)
      subst hx
      exact ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
        rfl, hss, hcmd, hex, hrb, matchesEvents_of_forall₂_relEv_right hrel₁ hm, hdec, hget, hcol⟩

private theorem modelAccepts_iff_of_forall₂_relEv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {evs₁ evs'₁ : List CliEvent} {ev : RunEvent} {t : DY.Bytes}
    (hrel₁ : List.Forall₂ RelEv evs₁ evs'₁) :
    ModelAcceptsTermAfterAttackerSends interp r S g ss evs₁ ev t ↔
      ModelAcceptsTermAfterAttackerSends interp r S g ss evs'₁ ev t := by
  have hrel_app : List.Forall₂ RelEv (evs₁ ++ [.run ev]) (evs'₁ ++ [.run ev]) :=
    forall₂_append hrel₁ (.cons (relEv_refl _) .nil)
  constructor
  · rintro ⟨ext, m, msgIdx, g₁, vis₁, hkn, hdec, haddr, hσ, hget, hex⟩
    exact ⟨ext, m, msgIdx, g₁, vis₁, hkn, hdec, haddr, hσ, hget,
      (explains_iff_of_forall₂_relEv hrel_app).mp hex⟩
  · rintro ⟨ext, m, msgIdx, g₁, vis₁, hkn, hdec, haddr, hσ, hget, hex⟩
    exact ⟨ext, m, msgIdx, g₁, vis₁, hkn, hdec, haddr, hσ, hget,
      (explains_iff_of_forall₂_relEv hrel_app).mpr hex⟩

private theorem signalMsgCollides_of_forall₂_relEv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {evs₁ evs'₁ : List CliEvent} {ev : RunEvent} {b : HwBytes}
    (hrel₁ : List.Forall₂ RelEv evs₁ evs'₁)
    (h : SignalMsgAcceptedOnlyViaCollision interp r S g ss evs'₁ ev b) :
    SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev b := by
  refine ⟨h.1, fun g' ss' vis' hex hnrc => ?_⟩
  have hex' := (explains_iff_of_forall₂_relEv hrel₁).mp hex
  have hnrc' := fun hrc' => hnrc ((readCollisionCli_iff_of_forall₂_relEv hrel₁).mpr hrc')
  rcases h.2 g' ss' vis' hex' hnrc' with h1 | ⟨⟨t, htr, hacc⟩, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨⟨t, htr, (modelAccepts_iff_of_forall₂_relEv hrel₁).mpr hacc⟩,
      fun t htr hacc' => h2 t htr ((modelAccepts_iff_of_forall₂_relEv hrel₁).mp hacc')⟩

private theorem preKeyCollides_of_forall₂_relEv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {evs₁ evs'₁ : List CliEvent} {b : HwBytes} {p : PreKeyFields}
    (hrel₁ : List.Forall₂ RelEv evs₁ evs'₁)
    (h : PreKeyStartCollidesOrRejects interp r S g ss evs'₁ b p) :
    PreKeyStartCollidesOrRejects interp r S g ss evs₁ b p := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hkm | hall
  · exact Or.inl hkm
  · exact Or.inr fun g' ss' vis' hex hnrc =>
      hall g' ss' vis' ((explains_iff_of_forall₂_relEv hrel₁).mp hex)
        (fun hrc' => hnrc ((readCollisionCli_iff_of_forall₂_relEv hrel₁).mpr hrc'))

private theorem collision_of_forall₂_relEv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {evs evs' : List CliEvent}
    (hrel : List.Forall₂ RelEv evs evs')
    (hcol : CollisionAfterExplainedPrefix interp r S evs') :
    CollisionAfterExplainedPrefix interp r S evs := by
  obtain ⟨evs'₁, ev', evs'₂, g, ss, vis, rfl, hex', hnext'⟩ := hcol
  obtain ⟨evs₁, rest, rfl, hrel₁, hrest⟩ := forall₂_append_split_right hrel
  cases hrest with
  | @cons x _ evs₂ _ hxy _ =>
    have hx : x = .run ev' := by
      rcases hxy with rfl | ⟨_, ev'₀, _, h2, _, hrej', hnsend'⟩
      · rfl
      · cases h2
        exfalso
        dsimp only [NextEventCollides] at hnext'
        cases hcmd : ev'.cmd with
        | init _ _ => simp only [hcmd] at hnext'
        | send _ => exact hnsend' _ hcmd
        | recv _ =>
          simp only [hcmd] at hnext'
          obtain ⟨⟨out, hex⟩, _⟩ := hnext'
          exact hrej' out hex
    subst hx
    refine ⟨evs₁, ev', evs₂, g, ss, vis, rfl,
      (explains_iff_of_forall₂_relEv hrel₁).mpr hex', ?_⟩
    dsimp only [NextEventCollides] at hnext' ⊢
    cases hcmd : ev'.cmd with
    | init _ _ => simp only [hcmd] at hnext'
    | send _ =>
      simp only [hcmd] at hnext' ⊢
      refine ⟨hnext'.1, fun g' hg' => hnext'.2 g' ⟨hg'.1, ?_⟩⟩
      obtain ⟨vis', hv⟩ := hg'.2
      exact ⟨vis', (explains_iff_of_forall₂_relEv hrel₁).mp hv⟩
    | recv _ =>
      simp only [hcmd] at hnext' ⊢
      refine ⟨hnext'.1, ?_⟩
      cases hinp : ev'.input with
      | nil => simp only [hinp] at hnext'; exact hnext'.2
      | cons tag body =>
        simp only [hinp] at hnext'
        rcases hnext'.2 with ⟨htag, hsm⟩ | ⟨p, hp, ⟨hk, hver, hidk, hsm⟩ | ⟨hnk, hpk⟩⟩
        · exact Or.inl ⟨htag, signalMsgCollides_of_forall₂_relEv hrel₁ hsm⟩
        · exact Or.inr ⟨p, hp, Or.inl ⟨hk, hver, hidk, signalMsgCollides_of_forall₂_relEv hrel₁ hsm⟩⟩
        · exact Or.inr ⟨p, hp, Or.inr ⟨hnk, preKeyCollides_of_forall₂_relEv hrel₁ hpk⟩⟩

/-! ## Bounded-I/O model refinement -/

/-- Whole-protocol CLI refinement for the bounded-I/O model relation `PqModelRelB2`. -/
theorem comp_refines_cli_model_b2 : CompRefinesCliModelB2 := by
  intro interp hext P hagree r hr
  obtain ⟨S, hS⟩ := comp_refines_cli_model interp hext P hagree r hr
  refine ⟨S, fun evs htr hg => ?_⟩
  have hsim₀ : PqTurnSim1A (interpOfParams interp P) P r
      (CliTurn.init (initDirs interp r))
      (CliTurn.init (initDirs (interpOfParams interp P) r)) [] := by
    have hdirs_eq : initDirs interp r = initDirs (interpOfParams interp P) r :=
      congrFun (initDirs_interpOfParams interp P).symm r
    rw [hdirs_eq]
    exact pqTurnSim1A_init hr hagree
  obtain ⟨evs', htr', hrel⟩ := traces_b2_to_inCap hext hagree hr htr hsim₀
  rcases hS evs' htr' (invertsGuarded_of_forall₂_relEv hrel hg) with ⟨g, ss, vis, hex'⟩ | hcol'
  · exact Or.inl ⟨g, ss, vis, (explains_iff_of_forall₂_relEv hrel).mpr hex'⟩
  · exact Or.inr (collision_of_forall₂_relEv hrel hcol')

/--
info: 'DY.Libsignal.Composed.Refinement.Cli.comp_refines_cli_model_b2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms comp_refines_cli_model_b2

end DY.Libsignal.Composed.Refinement.Cli
