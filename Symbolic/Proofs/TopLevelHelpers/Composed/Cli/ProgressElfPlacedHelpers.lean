/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Support.Phi
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BinaryOomSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import Symbolic.Proofs.Refinement.Composed.Cli.ModelB2
public import Symbolic.Proofs.Refinement.Composed.Cli.ParD3RpkSlot
public import Symbolic.Proofs.Refinement.Composed.Cli.PksmParseEquiv
public import Symbolic.Specifications.Refinement.Statement
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3ModelV2SlotsBase
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.Cli.DirBridgeAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge

/-!
# Input-Extensionality, Pre-Key Parser, and I/O Cap Helpers for Placed Progress

**Checked by Lean.**

Provides `InputsEquiv` transport lemmas for `cliRunPlacedSig`, pre-key parser equivalences
(`preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3`, `pqFieldsMatch_iff_sessMatchesPm_f3`), and I/O cap
reductions (`CallWithinCap`, `pqModelPost_of_b2_withinCap_f3`, `aboveCap_after_eq_self_f3`) used by
`ProgressElfPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers

open Arm64 (hasDotDot hasLeadingSlash normalizePath)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (
  PreKeyFields ProtocolSetup ProtocolSetupWF decodePreKey parsePreKey vec32
)
open DY.Libsignal.Composed.Refinement.Cli (
  BobCallAllowed BundleFilesFlat BundleReadWithinCapB2 CliCall CliTurn DirectorySnapshot
  FilesVisible InputsEquiv InputsFor PqFieldsMatch PqModelPost PqModelPostB2 StdinBounded
  ValidCall bundleReadNamesB2 coinsLen peerOf pqInitInputsF preKeyOfBody? scrub
)
open DY.Libsignal.Composed.Refinement.Cli.ParD3 (
  PqTurnSim1A isScrubbedPath_of_bundleFilesFlat regularFileList_of_bundleFilesFlat
)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.Proofs.Refinement.Composed.Cli (
  decodePreKey_eq_map_decodeProto pksmParse_parsePreKey_cases protoToPreKeyMsg
)
open Symbolic.Swarm.CREF.Cli (
  IsScrubbedPath PqPartyInv RegularFileList bytesToVec_toList_of_len caller_pqPartyInv_of_allowed
  filesOf_append_of_regular filesOf_eq_none_of_forall_ne inputsEquiv_pqInputs
  inputsEquiv_pqRecvInputs inputsEquiv_pqSendInputs interpOfParams isScrubbedPath_congr
  isScrubbedPath_encodeDir keyToBytes32_bytesToKey32 peerOf_eq_addrE_other records_of_pqPartyInv
  regularFileList_encodeDir regularFile_root scrub_filesOf_pqInputs_reject wfPq_of_pqPartyInv
)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)
open CryptoGames.LibsignalSession (
  GhostState PublicKey SessionState SignalMessage currentVersion preKyberVersion
)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.E2E (
  PEParams RecordExtras UnreachedPqxdhPrimitives initiateTapeLen wirePrekey wireWhisper
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (
  Address CliHooks Inputs Outcome PqParty PqxdhPartyInSpecDomain bundleDir coinsFile encodeDir
  filesOf maxPlaintextBytes partyAddress partyDirs pqRecvInputs pqSendInputs stdinCapBytes
  stdioPaths
)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli (InputsLoadable)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkToE? pkVecTag?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (decodeProto kyberOk pksmParse)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  d3PqSessionOf kyberPayload_isSome_of_pksmParse_v4 version_three_or_four_of_pksmParse_some
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity (FilesVisibleRaw InputsEquivRaw LoadableFile)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3 (
  cliRunPlacedSig_some_of_inputsEquiv
)

/-! ## Input-extensionality transport -/

def defaultExtrasProg : UnreachedPqxdhPrimitives :=
  { sigPkGen := fun _ => [], sigSign := fun _ _ _ => [], scalarMul := fun _ _ => [],
    scalarAdd := fun _ _ => [], kemKeyGen := fun _ => ([], []), pow8 := fun _ => [],
    isValidDhTriple := fun _ _ _ => false }

theorem inputsEquivRaw_of_inputsEquiv {i i' : Inputs} (h : InputsEquiv i i') :
    InputsEquivRaw i i' :=
  h

theorem inputsEquivRaw_symm_of_inputsEquiv {i i₀ : Inputs} (h : InputsEquiv i i₀) :
    InputsEquivRaw i₀ i :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun p => (h.2.2.2 p).symm⟩

theorem filesVisibleRaw_of_filesVisible {files : List (String × HwBytes)}
    (h : FilesVisible files) :
    FilesVisibleRaw files :=
  fun f hf => ⟨(h f hf).1, (h f hf).2.1⟩

theorem loadableFiles_of_filesVisible {files : List (String × HwBytes)}
    (h : FilesVisible files) :
    ∀ f ∈ files, LoadableFile f :=
  fun f hf => ⟨⟨(h f hf).2.2.1, (h f hf).2.2.2.1⟩, (h f hf).2.2.2.2⟩

theorem inputsLoadable_of_init_inputsFor {c : CliCall} {peer : Address} {dir : String}
    {d : DirectorySnapshot} {i : Inputs}
    (hm : c.cmd = .init peer dir) (hdir : dir = bundleDir) (hin : InputsFor c d i) :
    InputsLoadable i := by
  refine ⟨?_, fun f hf =>
    ⟨⟨(hin.2.2.2.2 f hf).2.2.1, (hin.2.2.2.2 f hf).2.2.2.1⟩, (hin.2.2.2.2 f hf).2.2.2.2⟩⟩
  have hdirs_i : i.dirs = partyDirs ++ [bundleDir] := by
    rw [hin.2.1, hm, hdir]
  rw [hdirs_i]
  intro dirEntry hmem
  have hb : (hasLeadingSlash dirEntry || hasDotDot dirEntry) = false := by
    revert dirEntry hmem; decide
  exact Bool.or_eq_false_iff.mp hb

theorem cliRunPlacedSig_some_of_inputsEquiv_symm {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {i i₀ : Inputs} {o : Outcome}
    (hr₀ : cliRunPlacedSig mpl mmpl elf W i₀ = some o)
    (heq : InputsEquiv i i₀) (hvis : FilesVisible i.files)
    (hvis₀ : FilesVisibleRaw i₀.files) :
    cliRunPlacedSig mpl mmpl elf W i = some o :=
  cliRunPlacedSig_some_of_inputsEquiv
    (inputsEquivRaw_symm_of_inputsEquiv heq)
    hvis₀
    (filesVisibleRaw_of_filesVisible hvis)
    (loadableFiles_of_filesVisible hvis)
    hr₀

/-- Transports `cliRunPlacedSig mpl mmpl elf W i₀ ≠ none` across `InputsEquiv i i₀`. -/
theorem cliRunPlacedSig_ne_none_of_inputsEquiv {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {i i₀ : Inputs}
    (hne₀ : cliRunPlacedSig mpl mmpl elf W i₀ ≠ none)
    (heq : InputsEquiv i i₀) (hvis : FilesVisible i.files)
    (hvis₀ : FilesVisibleRaw i₀.files) :
    cliRunPlacedSig mpl mmpl elf W i ≠ none := by
  cases hr₀ : cliRunPlacedSig mpl mmpl elf W i₀ with
  | none => exact absurd hr₀ hne₀
  | some o =>
    have hr := cliRunPlacedSig_some_of_inputsEquiv_symm hr₀ heq hvis hvis₀
    rw [hr]; intro hnone; cases hnone

theorem cliRunPlacedSig_ne_none_of_eq_some_inputsEquiv {mpl mmpl : MultiPlacement}
    {elf : ElfImage} {W : CliHooks} {i i₀ : Inputs} {o : Outcome}
    (hr₀ : cliRunPlacedSig mpl mmpl elf W i₀ = some o)
    (heq : InputsEquiv i i₀) (hvis : FilesVisible i.files)
    (hvis₀ : FilesVisibleRaw i₀.files) :
    cliRunPlacedSig mpl mmpl elf W i ≠ none :=
  by
    rw [cliRunPlacedSig_some_of_inputsEquiv_symm hr₀ heq hvis hvis₀]
    intro hnone; cases hnone

/-! ## Pre-key parser equivalences -/

private theorem vec32_drop1_of_take33_eq_f3 {b : HwBytes} {v : List.Vector (BitVec 8) 32}
    (h : b.take 33 = 5#8 :: v.toList) :
    vec32 (b.drop 1) = v := by
  rcases v with ⟨l, hl_v⟩
  cases b with
  | nil => cases h
  | cons _ rest =>
    dsimp only [List.Vector.toList] at h
    have hrest : rest.take 32 = l := (List.cons.inj h).2
    have hlen : 32 ≤ rest.length := by
      have hl := congrArg List.length hrest
      rw [List.length_take, hl_v] at hl
      omega
    have heq : (rest ++ List.replicate 32 0#8).take 32 = l := by
      rw [List.take_append_of_le_length hlen, hrest]
    dsimp only [List.drop_succ_cons, List.drop_zero, vec32]
    exact Subtype.ext heq

private theorem decodeProto_drop1_of_pksmParse_some_f3 {body : HwBytes}
    {pm : PreKeySignalMessage} (h : pksmParse body = some pm) :
    ∃ m,
      decodeProto (body.drop 1) = some m ∧
        pm.registrationId = m.registrationId.getD 0#32 := by
  cases body with
  | nil => simp [pksmParse] at h
  | cons vb rest =>
    unfold pksmParse at h
    dsimp only [List.drop_succ_cons, List.drop_zero] at h ⊢
    by_cases hver : (vb >>> 4) < preKyberVersion ∨ currentVersion < (vb >>> 4)
    · simp [hver] at h
    · simp only [hver, ↓reduceIte] at h
      rcases hdec : decodeProto rest with _ | m
      · simp [hdec] at h
      rw [hdec] at h
      rcases hbk : m.baseKey with _ | bk
      · simp [hbk] at h
      rcases hik : m.identityKey with _ | ik
      · simp [hbk, hik] at h
      rcases hmsg : m.message with _ | msg
      · simp [hbk, hik, hmsg] at h
      rcases hsid : m.signedPreKeyId with _ | sid
      · simp [hbk, hik, hmsg, hsid] at h
      simp only [hbk, hik, hmsg, hsid] at h
      cases hkyb : kyberOk (vb >>> 4) m
      · simp [hkyb] at h
      simp only [hkyb, ↓reduceIte] at h
      rcases h1 : PublicKey.deserialize bk with _ | baseKey
      · simp [h1] at h
      rcases h2 : PublicKey.deserialize ik with _ | idKey
      · simp [h1, h2] at h
      rcases h3 : SignalMessage.tryFrom protoSignalCodec msg with _ | inner
      · simp [h1, h2, h3] at h
      simp only [h1, h2, h3, Option.some.injEq] at h
      subst h
      exact ⟨m, hdec, rfl⟩

private theorem bv8_toNat_eq_four_iff_f3 (v : BitVec 8) :
    v.toNat = 4 ↔ v = 4#8 := by
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)
  · rintro rfl
    rfl

theorem preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3 (body : HwBytes) :
    preKeyOfBody? body = (pksmParse body).bind pkToE? := by
  rcases pksmParse_parsePreKey_cases body with ⟨hpm, hq⟩ | ⟨pm, q, hpm, hq, ha⟩
  · simp [preKeyOfBody?, hpm, hq]
  · obtain ⟨m, hdec, hreg⟩ := decodeProto_drop1_of_pksmParse_some_f3 hpm
    have hraw : decodePreKey (body.drop 1) = some (protoToPreKeyMsg m) := by
      rw [decodePreKey_eq_map_decodeProto, hdec]
      rfl
    unfold preKeyOfBody?
    rw [hq, hraw, hpm]
    dsimp only [Option.bind]
    by_cases hv4 : pm.messageVersion = 4#8
    · have hqv4 : q.version = 4 := ha.version_eq.trans (by rw [hv4]; rfl)
      obtain ⟨kp, hkp⟩ := kyberPayload_isSome_of_pksmParse_v4 hpm hv4
      have hkid : q.kyberPreKeyId = some kp.preKeyId := by
        rw [ha.kyberPreKeyId_eq, hkp]
        rfl
      have hkct : q.kyberCiphertext = some kp.ciphertext := by
        rw [ha.kyberCiphertext_eq, hkp]
        rfl
      have hbk : vec32 (q.baseKey.drop 1) = pm.baseKey.bytes :=
        vec32_drop1_of_take33_eq_f3 ha.baseKey_take33_eq
      have hik : vec32 (q.identityKey.drop 1) = pm.identityKey.publicKey.bytes :=
        vec32_drop1_of_take33_eq_f3 ha.identityKey_take33_eq
      have hrhs : pkToE? pm =
          match pkVecTag? 8#8 1568 kp.ciphertext with
          | none => none
          | some ct =>
            some { regId := pm.registrationId, opkId := pm.preKeyId, spkId := pm.signedPreKeyId,
                   kpkId := kp.preKeyId, kyberCt := ct, baseKey := pm.baseKey.bytes,
                   idPub := pm.identityKey.publicKey.bytes, inner := pm.message.serialized } := by
        unfold pkToE?
        rw [hv4, hkp]
        rfl
      rw [hqv4, hkid, hkct, hrhs]
      simp only [↓reduceIte]
      cases kp.ciphertext with
      | nil => rfl
      | cons t ct =>
        dsimp only [pkVecTag?]
        have hreg' : (protoToPreKeyMsg m).registrationId.getD 0 = pm.registrationId :=
          hreg.symm
        rw [hreg', ha.preKeyId_eq, ha.signedPreKeyId_eq, hbk, hik, ha.message_serialized_eq]
        split <;> rfl
    · have hqv4 : q.version ≠ 4 := by
        rw [ha.version_eq]
        exact fun h => hv4 ((bv8_toNat_eq_four_iff_f3 pm.messageVersion).mp h)
      unfold pkToE?
      simp [hqv4, hv4]

theorem pqFieldsMatch_iff_sessMatchesPm_f3 (x : RecordExtras)
    (g : GhostState HwBytes) {body : HwBytes} {q : PreKeyFields} {pm : PreKeySignalMessage}
    (hq : parsePreKey body = some q) (hpm : pksmParse body = some pm) :
    PqFieldsMatch x g q ↔ SessMatchesPm (d3PqSessionOf x g) pm := by
  rcases pksmParse_parsePreKey_cases body with ⟨hnone, _⟩ | ⟨pm', q', hpm', hq', ha⟩
  · rw [hpm] at hnone
    cases hnone
  · cases hpm.symm.trans hpm'
    cases hq.symm.trans hq'
    unfold PqFieldsMatch SessMatchesPm d3PqSessionOf
    dsimp only
    rw [ha.baseKey_take33_eq, ha.version_eq, and_comm]
    refine and_congr_left' ?_
    rcases version_three_or_four_of_pksmParse_some hpm with hv | hv <;>
      rw [hv] <;>
      unfold SessionState.version
    · split
      · next h0 => rw [h0]; decide
      · exact ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => by rw [h]; rfl⟩
    · split
      · next h0 => rw [h0]; decide
      · exact ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => by rw [h]; rfl⟩

/-! ## I/O cap reduction and above-cap unchanged-turn lemmas -/

/-- Whether a CLI call `c` lies within the I/O caps (`BundleReadWithinCapB2` on `init` bundle files,
`maxPlaintextBytes` on `send` stdin, `stdinCapBytes` on `recv` stdin). -/
def CallWithinCap (c : CliCall) : Prop :=
  match c.cmd with
  | .init _ _ => BundleReadWithinCapB2 (filesOf c.bundle) bundleDir
  | .send _ => c.stdin.length ≤ maxPlaintextBytes
  | .recv _ => c.stdin.length ≤ stdinCapBytes

instance instDecidableCallWithinCap (c : CliCall) : Decidable (CallWithinCap c) := by
  unfold CallWithinCap; cases c.cmd <;> infer_instance

private theorem maxPlaintextBytes_le_stdinCapBytes : maxPlaintextBytes ≤ stdinCapBytes := by
  decide

private theorem bundleReadName_props {name : String} (hm : name ∈ bundleReadNamesB2) :
    (bundleDir ++ "/" ++ name) ∉ stdioPaths ∧
    IsScrubbedPath (bundleDir ++ "/" ++ name) = true ∧
    normalizePath (bundleDir ++ "/" ++ name) ≠ normalizePath coinsFile := by
  simp only [bundleReadNamesB2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

private theorem filesOf_encodeDir_bundle_none (P : PEParams) (st : PqParty) {p : String}
    (hscr : IsScrubbedPath p = true) :
    filesOf (encodeDir P st) p = none :=
  filesOf_eq_none_of_forall_ne (regularFileList_encodeDir P st) fun f hf heq => by
    have := (isScrubbedPath_congr heq).symm.trans hscr
    rw [isScrubbedPath_encodeDir P st f hf] at this; cases this

private theorem filesOf_extra_bundle_eq {bundle : List (String × HwBytes)}
    (hflat : BundleFilesFlat bundle) (coins : HwBytes) {p : String}
    (hne : normalizePath p ≠ normalizePath coinsFile) :
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

private theorem cmd_is_send_of_argv {c : CliCall} {a : Address}
    (h : c.cmd.argv = ["send", a.text]) : ∃ peer, c.cmd = .send peer := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, rfl⟩

private theorem cmd_is_recv_of_argv {c : CliCall} {a : Address}
    (h : c.cmd.argv = ["recv", a.text]) : ∃ peer, c.cmd = .recv peer := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, rfl⟩

private theorem cmd_is_init_of_argv {c : CliCall} {a : Address}
    {dir : String} (h : c.cmd.argv = ["init", a.text, dir]) : ∃ peer d, c.cmd = .init peer d := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, _, rfl⟩

/-- When `CallWithinCap c` holds, `PqModelPostB2` reduces to `PqModelPost`. -/
theorem pqModelPost_of_b2_withinCap_f3 {interp : ExternInterpretation} {P : PEParams}
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
    obtain ⟨peer, hcmd⟩ := cmd_is_send_of_argv (hin.1.symm.trans heq.1)
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

theorem caller_st_of_validCall_f3 {interp : ExternInterpretation} {P : PEParams}
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
  have hd_eq : t_clean.dirs c.party = t.dirs c.party := by
    rcases hp with ha | hb
    · exact ha ▸ hsim.dirs_other r.alice hr.1
    · have hoff : t.bobOff = false := by
        cases hbo : t.bobOff with
        | false => rfl
        | true => exact absurd hb (hbca hbo)
      rw [hsim.bobOff_false_eq hoff]
  have hbca_clean : BobCallAllowed r t_clean c := fun hbo =>
    absurd (hsim.clean_bobOff.symm.trans hbo) Bool.false_ne_true
  obtain ⟨_, st₀, hst_clean⟩ := caller_pqPartyInv_of_allowed hsim.dirInv hbca_clean hp
  have hst₀ : PqPartyInv (interpOfParams interp P) P r accepted c.party st₀ (t.dirs c.party) :=
    hd_eq ▸ hst_clean
  exact ⟨hp, st₀, hst₀, wfPq_of_pqPartyInv hst₀ hfb⟩

/-- Every above-cap call (`¬ CallWithinCap c`) under `PqModelPostB2` exits with non-zero code
(`1` or `2`), empty stdout, and unchanged scrubbed directory, leaving `t.after r c code out files = t`. -/
theorem aboveCap_after_eq_self_f3 {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t_clean : CliTurn} {accepted : List HwBytes}
    {c : CliCall} {i : Inputs} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hr : ProtocolSetupWF r)
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hnext : ValidCall interp r t c)
    (hin : InputsFor c (t.dirs c.party) i)
    (hnot_cap : ¬ CallWithinCap c)
    (hpost : PqModelPostB2 interp P i (.exited code out files)) :
    t.after r c code out files = t := by
  obtain ⟨_, st₀, hst₀, hwf₀⟩ := caller_st_of_validCall_f3 hr hsim hnext
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
  obtain ⟨hc12, _, hscr⟩ := hex_rej
  have hne : code ≠ 0 := by rcases hc12 with rfl | rfl <;> decide
  exact after_eq_self_of_ne_zero hne hscr

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers.inputsLoadable_of_init_inputsFor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms inputsLoadable_of_init_inputsFor

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers.preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers.pqFieldsMatch_iff_sessMatchesPm_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pqFieldsMatch_iff_sessMatchesPm_f3

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers.pqModelPost_of_b2_withinCap_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pqModelPost_of_b2_withinCap_f3

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers.aboveCap_after_eq_self_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms aboveCap_after_eq_self_f3

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers
