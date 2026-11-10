/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Common443.CompSmallSubgroupTrace
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge

/-!
# 3-Call Small-Subgroup CLI Implementation Trace Builder

Constructs a generic 3-call (`alice` `init`, `alice` `send`, `bob` `recv`) `ImplHalf` builder
parameterized over a plausible `PQXDHSpqrSetup` and concrete post-call file lists validated by
`ValidCall0Files`. Provides `compI0` setup witnesses (`cliCompFitsPinned_compI0_of_plausible`),
decidable `CanonicalPreKey` checks, and the concrete `Cheval26SmallSubgroupHighBitCli`
instantiation (`impl_half_pinned_of_three_calls`, `impl_half_of_three_calls`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent EnvEvent RunEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession
  (Address Cmd Inputs Outcome PublicBundle filesOf stdioPaths partyDirs bundleDir coinsFile
   addressFile identityKeyPairFile registrationIdFile identityFile sessionFile
   signedPreKeyFile lastResortKyberPreKeyFile baseKeysFile cliRunAbortOnPanic)
open CryptoVerification.RecordCodecs
  (IdentityKeyPairStructure SignedPreKeyRecordStructure)
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compLookupPub)
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
  (cliCoins0 cliCoins0_length)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compI0_cryptoEquationsHold compI0_pubCanonical compI0_kyberCorrectOn
   compI0_torsionShiftsRejected)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (compHooks0 compI0_hooksAgree compI0_externContractsHoldCli cliCompFitsPinned
   compRecordsI0 compI0_gamma_randTerm_pos compI0_gamma_kemPk compI0_gamma_sign
   compRecordsI0_ne compRecordsI0_randomsAt compRecordsI0_public)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
  (evInit evSend evRecv cliEvents rngMsg39 acceptMsg40)
open Symbolic.Proofs.Tests.Refinement.Cli
  (cliParentDirs CliFilePath cliStepAt cliEvalAt cliFilesOf_eq_evalAt cliEvalAt_idle
   filesBounded_of_cliFilePaths bundleFiles_cliFilePath inputsFor_of_cliFilePaths
   honestPublicBundle honestBundleDir_honestPublicBundle parseBundleFiles_of_honestBundleDir
   honestBundleDir_to_flat_and_honest commonFiles_alice_cliFilePath commonFiles_bob_cliFilePath
   bobPreKeyFiles_cliFilePath commonFiles_alice_bounded commonFiles_bob_bounded
   bobPreKeyFiles_bounded initDirs_alice_no_session textBytes_eq_flatMap)

theorem cliCompFits_of_pinned {w : PQXDHSpqrSetup}
    {iw : ExternInterpretation × CryptoVerification.SignalSession.CliHooks}
    {r : ProtocolSetup}
    (h : cliCompFitsPinned w iw r) : cliCompFits w iw r :=
  ⟨h.1.1, h.2.1, h.2.2⟩

theorem compRecordsI0_secrets (w : PQXDHSpqrSetup) :
    secretBytes (compRecordsI0 w) 0 = w.aliceId ∧
    secretBytes (compRecordsI0 w) 1 = w.bobId ∧
    secretBytes (compRecordsI0 w) 2 = w.spk ∧
    secretBytes (compRecordsI0 w) 3 = fillFresh 11 64 ∧
    secretBytes (compRecordsI0 w) 4 = fillFresh 16 64 ∧
    secretBytes (compRecordsI0 w) 5 = fillFresh 17 64 := by
  have hR := compRecordsI0_randomsAt w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [secretBytes, hR]; simp [compRecordsI0, PQXDHSpqrSetup.fresh])

theorem compRecordsI0_opaque (w : PQXDHSpqrSetup) :
    (compRecordsI0 w).opaqueBytes (setupPublic (compRecordsI0 w) 5) = w.spkSig ∧
    (compRecordsI0 w).opaqueBytes (setupPublic (compRecordsI0 w) 6) = w.kyberPk ∧
    (compRecordsI0 w).opaqueBytes (setupPublic (compRecordsI0 w) 7) = w.kyberPkSig := by
  obtain ⟨h5, h6, h7⟩ := compRecordsI0_public w
  refine ⟨?_, ?_, ?_⟩
  · rw [h5]
    show gamma compI0 w.compSem w.compGhost _ = _
    rw [compI0_gamma_sign]
    show (if gamma compI0 w.compSem w.compGhost (randTerm 11 64) = fillFresh 11 64
      then _ else _) = _
    rw [compI0_gamma_randTerm_pos w 11 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh]
  · rw [h6]
    show gamma compI0 w.compSem w.compGhost _ = _
    rw [compI0_gamma_kemPk]; rfl
  · rw [h7]
    show gamma compI0 w.compSem w.compGhost _ = _
    rw [compI0_gamma_sign]
    show (if gamma compI0 w.compSem w.compGhost (randTerm 17 64) = fillFresh 11 64
      then _ else _) = _
    rw [compI0_gamma_randTerm_pos w 17 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh, fillFresh_ne_11_17]

theorem compRecordsI0_wf_of_plausible (w : PQXDHSpqrSetup) (h : w.Plausible) :
    ProtocolSetupWF (compRecordsI0 w) := by
  obtain ⟨ha, hb, hs, hss, hk, hks, hsec, hslice, hnd, _⟩ := h
  obtain ⟨o5, o6, o7⟩ := compRecordsI0_opaque w
  have hR := compRecordsI0_randomsAt w
  refine ⟨compRecordsI0_ne w, ?_, ?_, ?_, ?_, ?_, hsec, ?_⟩
  · rw [hR]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [compRecordsI0, PQXDHSpqrSetup.fresh, fillFresh, ha, hb, hs]
  · rw [hR]
    simpa [compRecordsI0, PQXDHSpqrSetup.fresh] using hnd
  · dsimp only [ProtocolSetup.spkSigTerm]; rw [o5]; exact hss
  · dsimp only [ProtocolSetup.pqpkPubTerm]; rw [o6]; exact hk
  · dsimp only [ProtocolSetup.pqpkSigTerm]; rw [o7]; exact hks
  · show slice w.kyberSec 1537 1568 = _
    dsimp only [ProtocolSetup.pqpkPubTerm]
    rw [o6]; exact hslice

theorem cliCompFitsPinned_compI0_of_plausible (w : PQXDHSpqrSetup)
    (h : w.Plausible) (htor : TorsionShiftsRecorded compI0 w.torsionShifts) :
    cliCompFitsPinned w (compI0, compHooks0) (compRecordsI0 w) := by
  have hwf := compRecordsI0_wf_of_plausible w h
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5⟩ := compRecordsI0_secrets w
  obtain ⟨o5, o6, o7⟩ := compRecordsI0_opaque w
  exact ⟨⟨⟨hwf, rfl, rfl, rfl, rfl, rfl, hs0, hs1, hs2, o5, o6, o7, rfl,
      compI0_cryptoEquationsHold, compI0_pubCanonical,
      compI0_kyberCorrectOn (compRecordsI0 w) w.kyberCts⟩,
     rfl, ⟨hs3, hs4, hs5⟩, ⟨rfl, rfl⟩,
     compI0_torsionShiftsRejected, htor⟩,
    compI0_externContractsHoldCli, compI0_hooksAgree⟩

theorem cliCompFitsPinned_hb :
    cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup
      (compI0, compHooks0)
      (compRecordsI0 Witnesses.Cheval26SmallSubgroupHighBitCli.setup) :=
  cliCompFitsPinned_compI0_of_plausible
    Witnesses.Cheval26SmallSubgroupHighBitCli.setup
    (by decide +kernel)
    (fun _ h => nomatch h)

def isNotInvertEvent : CliEvent → Bool
  | .env (.invertDH _ _) => false
  | .env (.invertKEM _ _) => false
  | _ => true

theorem invertsGuarded_of_noInverts {interp : ExternInterpretation} {r : ProtocolSetup}
    {evs : List CliEvent} (h : evs.all isNotInvertEvent = true) :
    InvertsGuarded interp r evs := by
  intro pre post e heq
  have hmem : CliEvent.env e ∈ evs := by rw [heq]; simp
  have hni : isNotInvertEvent (.env e) = true := List.all_eq_true.mp h _ hmem
  cases e <;> simp [isNotInvertEvent] at hni ⊢

/-- Decidable check for `CanonicalPreKey` via `decodePreKey` and `preKeyWire` round-tripping. -/
def checkCanonicalPreKey (b : HwBytes) : Bool :=
  match decodePreKey (b.drop 2) with
  | none => false
  | some m =>
    let preKeyId := m.preKeyId
    let spkId := m.signedPreKeyId.getD 0
    let kpkId := m.kyberPreKeyId.getD 0
    let regId := m.registrationId.getD 0
    let ik := (m.identityKey.getD []).drop 1
    let ek := (m.baseKey.getD []).drop 1
    let ct := (m.kyberCiphertext.getD []).drop 1
    let msg := m.message.getD []
    (ik.length == 32) && (ek.length == 32) && (ct.length == 1568) &&
      (b == preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg)

theorem canonicalPreKey_of_check {b : HwBytes} (h : checkCanonicalPreKey b = true) :
    CanonicalPreKey b := by
  unfold checkCanonicalPreKey at h
  cases hm : decodePreKey (b.drop 2) with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨m.preKeyId, m.signedPreKeyId.getD 0, m.kyberPreKeyId.getD 0, m.registrationId.getD 0,
      (m.identityKey.getD []).drop 1, (m.baseKey.getD []).drop 1,
      (m.kyberCiphertext.getD []).drop 1, m.message.getD [],
      h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem msg_length_le_preKeyWire (preKeyId : Option (BitVec 32))
    (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes) :
    msg.length ≤ (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length := by
  unfold preKeyWire DY.Libsignal.PQXDH.Refinement.PreKeyProto.encode
    CryptoVerification.LibsignalProtoCodec.encodeBytesField
  simp only [List.length_cons, List.length_append]; omega

/-- Decidable `StdinBounded` check for a `.recv` call. -/
def checkRecvStdinBounded (stdin : HwBytes) : Bool :=
  decide (stdin.length + 2048 < 2 ^ 32) &&
  match parsePreKeyWire stdin with
  | some q => decide (q.message.length + 2048 < 2 ^ 32)
  | none => true

theorem stdinBounded_recv_of_check {party : Participant} {peer : Address} {stdin coins : HwBytes}
    (h : checkRecvStdinBounded stdin = true) :
    StdinBounded { party, cmd := .recv peer, bundle := [], stdin, coins } := by
  unfold checkRecvStdinBounded at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, hq_bound⟩ := h
  unfold StdinBounded
  dsimp only
  refine ⟨?_, fun _ => by omega, ?_, ?_⟩
  · intro body hb; rw [hb] at hlt; simp at hlt; omega
  · intro q hq
    simp only [hq, decide_eq_true_eq] at hq_bound
    exact hq_bound
  · intro preKeyId spkId kpkId regId ik ek ct msg _ _ _ hst
    have hle := msg_length_le_preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg
    rw [← hst] at hle; omega

theorem canonicalPreKey_highBitWireFast :
    CanonicalPreKey CompSmallSubgroupTrace.highBitWireFast :=
  canonicalPreKey_of_check (by decide +kernel)

theorem canonicalPreKey_highBitWireBytes :
    CanonicalPreKey CompSmallSubgroupTrace.highBitWireBytes := by
  rw [CompSmallSubgroupTrace.highBitWireBytes_eq]
  exact canonicalPreKey_highBitWireFast

theorem canonicalPreKey_torsionWireFast :
    CanonicalPreKey CompSmallSubgroupTrace.torsionWireFast :=
  canonicalPreKey_of_check (by decide +kernel)

theorem canonicalPreKey_torsionWireBytes :
    CanonicalPreKey CompSmallSubgroupTrace.torsionWireBytes := by
  rw [CompSmallSubgroupTrace.torsionWireBytes_eq]
  exact canonicalPreKey_torsionWireFast

theorem canonicalPreKey_head_ne_whisper {b : HwBytes} (h : CanonicalPreKey b) :
    b.head? ≠ some wireWhisperTag := by
  obtain ⟨preKeyId, spkId, kpkId, regId, ik, ek, ct, msg, _, _, _, rfl⟩ := h
  unfold preKeyWire wireWhisperTag
  change some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag ≠ some 2#8
  decide

def isScrubbedPath (p : String) : Bool :=
  SamePath p coinsFile || (Arm64.normalizePath p).head? == some bundleDir

/-- List counterpart of `scrub` that drops `coins` and `bundle/*` entries. -/
def scrubList (files : List (String × HwBytes)) : List (String × HwBytes) :=
  files.filter fun f => !isScrubbedPath f.1

private theorem isScrubbedPath_of_norm_eq {p q : String}
    (h : Arm64.normalizePath p = Arm64.normalizePath q) :
    isScrubbedPath p = isScrubbedPath q := by
  unfold isScrubbedPath SamePath
  rw [h]

private theorem cliEvalAt_scrubList_of_false {p : String} (hp : isScrubbedPath p = false) :
    ∀ (files : List (String × HwBytes)) (v : Option HwBytes),
      cliEvalAt (Arm64.normalizePath p) v (scrubList files) =
        cliEvalAt (Arm64.normalizePath p) v files
  | [], _ => rfl
  | f :: rest, v => by
    simp only [scrubList, List.filter_cons, cliEvalAt, List.foldl_cons]
    cases hs : isScrubbedPath f.1
    · simp only [Bool.not_false, ↓reduceIte]
      exact cliEvalAt_scrubList_of_false hp rest (cliStepAt (Arm64.normalizePath p) v f)
    · simp only [Bool.not_true]
      have hne : Arm64.normalizePath p ≠ Arm64.normalizePath f.1 := by
        intro heq
        have := (isScrubbedPath_of_norm_eq heq).symm.trans hp
        rw [hs] at this
        cases this
      have hstep : cliStepAt (Arm64.normalizePath p) v f = v := by
        unfold cliStepAt
        simp [hne]
      rw [hstep]
      exact cliEvalAt_scrubList_of_false hp rest v

theorem scrub_filesOf_eq_filesOf_scrubList {files : List (String × HwBytes)}
    (hl : ∀ x ∈ files, CliFilePath x.1) :
    scrub (filesOf files) = filesOf (scrubList files) := by
  have hl' : ∀ x ∈ scrubList files, CliFilePath x.1 :=
    fun x hx => hl x (List.mem_of_mem_filter hx)
  funext p
  change (if isScrubbedPath p then none else filesOf files p) = filesOf (scrubList files) p
  cases hp : isScrubbedPath p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [cliFilesOf_eq_evalAt hl, cliFilesOf_eq_evalAt hl']
    split
    · rfl
    · split
      · rfl
      · exact (cliEvalAt_scrubList_of_false hp files none).symm
  · simp only [↓reduceIte]
    rw [cliFilesOf_eq_evalAt hl']
    split
    · rfl
    · split
      · rfl
      · symm
        apply cliEvalAt_idle
        intro x hx heq
        have hfx : (!isScrubbedPath x.1) = true := (List.mem_filter.mp hx).2
        rw [isScrubbedPath_of_norm_eq heq, hp] at hfx
        cases hfx

/-- Alice's session path written without `toString` so `Arm64.normalizePath` reduces in the kernel. -/
def aliceSessPath : String := "sessions/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"

private theorem nat_repr_one : Nat.repr 1 = "1" := by
  rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]; rfl

theorem sessionFile_bobUuid_eq : sessionFile ⟨bobUuid, 1⟩ = aliceSessPath := by
  simp [sessionFile, CryptoVerification.SignalSession.Address.text, bobUuid, aliceSessPath,
    nat_repr_one]

/-- Checks that `files0` uses valid `CliFilePath`s, remains `< 2^31` bytes per file after
scrubbing, and leaves a non-empty session record at `aliceSessPath`. -/
def ValidCall0Files (files0 : List (String × HwBytes)) : Bool :=
  files0.all (fun f => decide (CliFilePath f.1)) &&
  (scrubList files0).all (fun f => decide (f.2.length < 2 ^ 31)) &&
  match cliEvalAt (Arm64.normalizePath aliceSessPath) none (scrubList files0) with
  | some rec_ => !rec_.isEmpty
  | none => false

theorem validCall0Files_smoke :
    ValidCall0Files [("address", [1#8]), (aliceSessPath, [1#8])] = true := by
  decide +kernel

/-- Vacuous post-condition on Alice's Call 1 output files, since Call 2 runs on Bob's directory and
ends the trace. -/
def ValidCall1Files (_files1 : List (String × HwBytes)) : Bool := true

theorem validCall0Files_cliFilePath {files0 : List (String × HwBytes)}
    (h : ValidCall0Files files0 = true) : ∀ x ∈ files0, CliFilePath x.1 := by
  unfold ValidCall0Files at h
  simp only [Bool.and_eq_true] at h
  intro x hx
  exact of_decide_eq_true (List.all_eq_true.mp h.1.1 x hx)

theorem validCall0Files_scrub_cliFilePath {files0 : List (String × HwBytes)}
    (h : ValidCall0Files files0 = true) : ∀ x ∈ scrubList files0, CliFilePath x.1 :=
  fun x hx => validCall0Files_cliFilePath h x (List.mem_of_mem_filter hx)

theorem validCall0Files_scrub_bounded {files0 : List (String × HwBytes)}
    (h : ValidCall0Files files0 = true) : FilesBounded (filesOf (scrubList files0)) := by
  apply filesBounded_of_cliFilePaths (validCall0Files_scrub_cliFilePath h)
  unfold ValidCall0Files at h
  simp only [Bool.and_eq_true] at h
  intro x hx
  exact of_decide_eq_true (List.all_eq_true.mp h.1.2 x hx)

theorem validCall0Files_alice_records_ne_none {files0 : List (String × HwBytes)}
    (h : ValidCall0Files files0 = true) {r : ProtocolSetup} (ha : r.alice = "alice")
    (bDir : DirectorySnapshot) (sent : List HwBytes) (bobOff : Bool) :
    ({ dirs := fun q => if q = "alice" then filesOf (scrubList files0)
                        else if q = "bob" then bDir else fun _ => none
       sent, bobOff } : CliTurn).records r "alice" ≠ none := by
  have hsp : sessionPathOf r "alice" = aliceSessPath := by
    simp [sessionPathOf, peerOf, peerNameOf, ha, sessionFile_bobUuid_eq]
  have hnot_stdio : Arm64.normalizePath aliceSessPath ∉ stdioPaths.map Arm64.normalizePath := by
    decide +kernel
  have hnot_empty : (Arm64.normalizePath aliceSessPath).isEmpty = false := by
    decide +kernel
  have hf : filesOf (scrubList files0) aliceSessPath =
      cliEvalAt (Arm64.normalizePath aliceSessPath) none (scrubList files0) := by
    rw [cliFilesOf_eq_evalAt (validCall0Files_scrub_cliFilePath h)]
    simp [hnot_stdio, hnot_empty]
  unfold ValidCall0Files at h
  simp only [Bool.and_eq_true] at h
  have hrec := h.2
  unfold CliTurn.records
  simp only [↓reduceIte, hsp, hf]
  cases hev : cliEvalAt (Arm64.normalizePath aliceSessPath) none (scrubList files0) with
  | none => simp [hev] at hrec
  | some rec_ =>
    simp only [hev, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hrec
    simp [hrec]

/-- UTF-8 byte encoder that avoids `ByteArray` for kernel reduction. -/
def textBytesFast (s : String) : HwBytes :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

theorem textBytes_eq_textBytesFast (s : String) :
    DY.Libsignal.Composed.Refinement.Cli.textBytes s = textBytesFast s :=
  textBytes_eq_flatMap s

def ssBundle (w : PQXDHSpqrSetup) : PublicBundle where
  registrationId := w.regIdB
  identityKey := ecKey (compLookupPub (clamp w.bobId))
  signedId := w.spkId
  signedKey := ecKey (compLookupPub (clamp w.spk))
  signedSig := w.spkSig
  kyberId := w.kpkId
  kyberKey := kyberKey w.kyberPk
  kyberSig := w.kyberPkSig
  oneTime := none

private theorem pubBytes_compI0_eq (sk : HwBytes) :
    pubBytes compI0 sk = compLookupPub (clamp sk) := rfl

theorem honestPublicBundle_eq_ssBundle (w : PQXDHSpqrSetup) :
    honestPublicBundle compI0 (compRecordsI0 w) = ssBundle w := by
  obtain ⟨_, hs1, hs2, _, _, _⟩ := compRecordsI0_secrets w
  obtain ⟨o5, o6, o7⟩ := compRecordsI0_opaque w
  unfold honestPublicBundle ssBundle
  rw [hs1, hs2, o5, o6, o7, pubBytes_compI0_eq, pubBytes_compI0_eq]
  rfl

def ssAliceBaseFiles (w : PQXDHSpqrSetup) : List (String × HwBytes) :=
  [(addressFile, textBytesFast "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"),
   (identityKeyPairFile,
     IdentityKeyPairStructure.encode
       ⟨ecKey (compLookupPub (clamp w.aliceId)), w.aliceId⟩),
   (registrationIdFile, CryptoVerification.SignalSession.le32 w.regIdA),
   (identityFile bobUuid, ecKey (compLookupPub (clamp w.bobId)))]

theorem commonFiles_alice_eq_ssAliceBaseFiles (w : PQXDHSpqrSetup) :
    commonFiles compI0 (compRecordsI0 w) "alice" = ssAliceBaseFiles w := by
  obtain ⟨hs0, hs1, _, _, _, _⟩ := compRecordsI0_secrets w
  have haddr : (addrOf (compRecordsI0 w) "alice").text =
      "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1" := by
    simp [addrOf, nameOf, compRecordsI0, aliceUuid, CryptoVerification.SignalSession.Address.text,
      nat_repr_one]
  unfold commonFiles ssAliceBaseFiles
  rw [haddr, textBytes_eq_textBytesFast]
  simp only [idSecret, peerIdSecret, ProtocolSetup.ikASecBytes, ProtocolSetup.ikBSecBytes,
    regIdOf, peerNameOf,
    show (compRecordsI0 w).alice = "alice" from rfl, ↓reduceIte,
    hs0, hs1, pubBytes_compI0_eq]
  rfl

private theorem toString_seven : toString (7 : Nat) = "7" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_seven.mpr rfl]; rfl

private theorem toString_nine : toString (9 : Nat) = "9" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_nine.mpr rfl]; rfl

/-- Initial Bob directory entries with literal paths for setups having `spkId = 7` and `kpkId = 9`. -/
def ssBobBaseFiles (w : PQXDHSpqrSetup) : List (String × HwBytes) :=
  [(addressFile, textBytesFast "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"),
   (identityKeyPairFile,
     IdentityKeyPairStructure.encode
       ⟨ecKey (compLookupPub (clamp w.bobId)), w.bobId⟩),
   (registrationIdFile, CryptoVerification.SignalSession.le32 w.regIdB),
   (identityFile aliceUuid, ecKey (compLookupPub (clamp w.aliceId))),
   ("signed-pre-keys/7", SignedPreKeyRecordStructure.encode
     ⟨w.spkId, ecKey (compLookupPub (clamp w.spk)), w.spk, w.spkSig, 0⟩),
   ("last-resort-kyber-pre-keys/9", SignedPreKeyRecordStructure.encode
     ⟨w.kpkId, kyberKey w.kyberPk, kyberKey (w.kyberSec.drop 1), w.kyberPkSig, 0⟩),
   ("last-resort-kyber-pre-keys/9.base-keys", [])]

theorem bobFiles_eq_ssBobBaseFiles (w : PQXDHSpqrSetup)
    (hSpk : w.spkId = 7) (hKpk : w.kpkId = 9) :
    commonFiles compI0 (compRecordsI0 w) "bob" ++ bobPreKeyFiles compI0 (compRecordsI0 w) =
      ssBobBaseFiles w := by
  obtain ⟨hs0, hs1, hs2, _, _, _⟩ := compRecordsI0_secrets w
  obtain ⟨o5, o6, o7⟩ := compRecordsI0_opaque w
  have hba : ("bob" : String) ≠ "alice" := by decide
  have haddr : (addrOf (compRecordsI0 w) "bob").text =
      "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1" := by
    simp [addrOf, nameOf, compRecordsI0, hba, bobUuid,
      CryptoVerification.SignalSession.Address.text, nat_repr_one]
  have hspkIdR : (compRecordsI0 w).spkId = w.spkId := rfl
  have hkpkIdR : (compRecordsI0 w).kpkId = w.kpkId := rfl
  have h7 : (7 : BitVec 32).toNat = 7 := rfl
  have h9 : (9 : BitVec 32).toNat = 9 := rfl
  have hspkF : signedPreKeyFile (compRecordsI0 w).spkId = "signed-pre-keys/7" := by
    rw [hspkIdR, hSpk]; unfold signedPreKeyFile; rw [h7, toString_seven]; rfl
  have hkpkF : lastResortKyberPreKeyFile (compRecordsI0 w).kpkId =
      "last-resort-kyber-pre-keys/9" := by
    rw [hkpkIdR, hKpk]; unfold lastResortKyberPreKeyFile; rw [h9, toString_nine]; rfl
  have hbkF : baseKeysFile (compRecordsI0 w).kpkId =
      "last-resort-kyber-pre-keys/9.base-keys" := by
    rw [hkpkIdR, hKpk]; unfold baseKeysFile; rw [h9, toString_nine]; rfl
  unfold commonFiles bobPreKeyFiles ssBobBaseFiles
  rw [haddr, textBytes_eq_textBytesFast, hspkF, hkpkF, hbkF]
  simp only [idSecret, peerIdSecret, ProtocolSetup.ikASecBytes, ProtocolSetup.ikBSecBytes,
    ProtocolSetup.spkSecBytes, ProtocolSetup.spkSigTerm, ProtocolSetup.pqpkPubTerm,
    ProtocolSetup.pqpkSigTerm, regIdOf, peerNameOf,
    show (compRecordsI0 w).alice = "alice" from rfl,
    show (compRecordsI0 w).withOpk = false from rfl,
    hba, ↓reduceIte, Bool.false_eq_true, List.append_nil,
    hs0, hs1, hs2, o5, o6, o7, pubBytes_compI0_eq]
  rfl

def ssC0Coins : HwBytes := cliCoins0

theorem cliCoins0_eq_ssC0Coins : cliCoins0 = ssC0Coins := rfl

def ssC1Pt : HwBytes := hexBytes "68656c6c6f20626f62"

theorem ptB_eq_ssC1Pt : CompRX0SS38.ptB = ssC1Pt := CompRX0SS38.ptB_eq_hex

def ssC1Coins : HwBytes :=
  hexBytes "23251f46b973b8989c462587d02a8056f38d75b313c67290aa215b5b52df0e3ee1f2c0f23cdbb316da32ab9063b3f652f24ac6d065a0889afbc534bb1e4b9fd2"

theorem cB_eq_ssC1Coins : CompRX0SS38.cB = ssC1Coins := CompRX0SS38.cB_eq_hex

def ssC1Out : HwBytes := CompSmallSubgroupTrace.sentWireFast

theorem sentWirePlant_eq_ssC1Out : CompRPlantWire.sentWireBytes = ssC1Out := by
  rw [CompRPlantWire.sentWireBytes_eq]; rfl

theorem sentWireSS_eq_ssC1Out : CompSmallSubgroupTrace.sentWireBytes = ssC1Out :=
  CompSmallSubgroupTrace.sentWireBytes_eq

def ssC2Coins : HwBytes :=
  hexBytes "277e2a7f356d98732990e6c96848114813f782d86b9349fbf714af9e97857fdc"

theorem rngMsg39_eq_ssC2Coins : rngMsg39 = ssC2Coins :=
  Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.rngMsg39_eq_hex

def ssC2Out : HwBytes := hexBytes "68656c6c6f20626f62"

theorem acceptMsg40_eq_ssC2Out : acceptMsg40 = ssC2Out :=
  Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.acceptMsg40_eq_hex

def ssCall0 (w : PQXDHSpqrSetup) : CliCall where
  party := "alice"
  cmd := .init ⟨bobUuid, 1⟩ bundleDir
  bundle := (ssBundle w).files bundleDir
  stdin := []
  coins := ssC0Coins

def ssCall1 : CliCall where
  party := "alice"
  cmd := .send ⟨bobUuid, 1⟩
  bundle := []
  stdin := ssC1Pt
  coins := ssC1Coins

def ssCall2 (c2Msg c2Coins : HwBytes) : CliCall where
  party := "bob"
  cmd := .recv ⟨aliceUuid, 1⟩
  bundle := []
  stdin := c2Msg
  coins := c2Coins

def mkInp (c : CliCall) (base : List (String × HwBytes)) : Inputs where
  argv := c.cmd.argv
  dirs := partyDirs ++ (match c.cmd with | .init _ dir => [dir] | _ => [])
  files := base ++ c.extra
  stdin := c.stdin

def ssInp0 (w : PQXDHSpqrSetup) : Inputs where
  argv := ["init", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1", bundleDir]
  dirs := partyDirs ++ [bundleDir]
  files := ssAliceBaseFiles w ++ (ssCall0 w).extra
  stdin := []

def ssInp1 (files0 : List (String × HwBytes)) : Inputs where
  argv := ["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"]
  dirs := partyDirs
  files := scrubList files0 ++ ssCall1.extra
  stdin := ssC1Pt

def ssInp2 (w : PQXDHSpqrSetup) (c2Msg c2Coins : HwBytes) : Inputs where
  argv := ["recv", "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"]
  dirs := partyDirs
  files := ssBobBaseFiles w ++ (ssCall2 c2Msg c2Coins).extra
  stdin := c2Msg

private theorem ssInp0_eq_mkInp (w : PQXDHSpqrSetup) :
    ssInp0 w = mkInp (ssCall0 w) (ssAliceBaseFiles w) := by
  simp [ssInp0, mkInp, ssCall0, CryptoVerification.SignalSession.Cmd.argv,
    CryptoVerification.SignalSession.Address.text, bobUuid, nat_repr_one]

private theorem ssInp1_eq_mkInp (files0 : List (String × HwBytes)) :
    ssInp1 files0 = mkInp ssCall1 (scrubList files0) := by
  simp [ssInp1, mkInp, ssCall1, CryptoVerification.SignalSession.Cmd.argv,
    CryptoVerification.SignalSession.Address.text, bobUuid, nat_repr_one]

private theorem ssInp2_eq_mkInp (w : PQXDHSpqrSetup) (c2Msg c2Coins : HwBytes) :
    ssInp2 w c2Msg c2Coins = mkInp (ssCall2 c2Msg c2Coins) (ssBobBaseFiles w) := by
  simp [ssInp2, mkInp, ssCall2, CryptoVerification.SignalSession.Cmd.argv,
    CryptoVerification.SignalSession.Address.text, aliceUuid, nat_repr_one]

def ssOut0 (files0 : List (String × HwBytes)) : Outcome := .exited 0 [] (filesOf files0)
def ssOut1 (files1 : List (String × HwBytes)) : Outcome := .exited 0 ssC1Out (filesOf files1)
def ssOut2 (c2Out : HwBytes) (files2 : List (String × HwBytes)) : Outcome :=
  .exited 0 c2Out (filesOf files2)

def mkTurn (aDir bDir : DirectorySnapshot) (sent : List HwBytes) (bobOff : Bool) : CliTurn where
  dirs := fun q => if q = "alice" then aDir else if q = "bob" then bDir else fun _ => none
  sent := sent
  bobOff := bobOff

private theorem cliTurn_mk_eq {d1 d2 : Participant → DirectorySnapshot}
    {s1 s2 : List HwBytes} {b1 b2 : Bool}
    (hd : d1 = d2) (hs : s1 = s2) (hb : b1 = b2) :
    CliTurn.mk d1 s1 b1 = CliTurn.mk d2 s2 b2 := by
  subst hd hs hb; rfl

private theorem initTurn_eq_mkTurn (w : PQXDHSpqrSetup)
    (hSpk : w.spkId = 7) (hKpk : w.kpkId = 9) :
    CliTurn.init (initDirs compI0 (compRecordsI0 w)) =
      mkTurn (filesOf (ssAliceBaseFiles w)) (filesOf (ssBobBaseFiles w)) [] false := by
  unfold CliTurn.init mkTurn
  refine cliTurn_mk_eq (funext fun p => ?_) rfl rfl
  simp only [initDirs,
    show (compRecordsI0 w).alice = "alice" from rfl,
    show (compRecordsI0 w).bob = "bob" from rfl]
  by_cases hpa : p = "alice"
  · subst hpa
    simp [commonFiles_alice_eq_ssAliceBaseFiles w]
  · by_cases hpb : p = "bob"
    · subst hpb
      simp [hpa, bobFiles_eq_ssBobBaseFiles w hSpk hKpk]
    · simp [hpa, hpb]

open Classical in
private theorem after_alice_mkTurn {w : PQXDHSpqrSetup} {aDir bDir outDir : DirectorySnapshot}
    {sent : List HwBytes} {c : CliCall} {out : HwBytes} (hp : c.party = "alice") :
    (mkTurn aDir bDir sent false).after (compRecordsI0 w) c 0 out outDir =
      mkTurn (scrub outDir) bDir
        (sent ++ (match c.cmd with | .send _ => (sentBody out).toList | _ => [])) false := by
  have hnm : ¬ (0 = 0 ∧ PreKeyNoMatch (compRecordsI0 w) (mkTurn aDir bDir sent false) c) := by
    rintro ⟨_, hbob, _⟩
    have hab : ("alice" : String) = "bob" := hp.symm.trans hbob
    exact absurd hab (by decide)
  have hbob : ((mkTurn aDir bDir sent false).bobOff ||
      decide (0 = 0 ∧ PreKeyNoMatch (compRecordsI0 w) (mkTurn aDir bDir sent false) c)) = false := by
    rw [show (mkTurn aDir bDir sent false).bobOff = false from rfl, Bool.false_or]
    exact decide_eq_false hnm
  unfold CliTurn.after; rw [hbob]; simp only [hp]; unfold mkTurn
  refine cliTurn_mk_eq (funext fun q => ?_) (by cases c.cmd <;> rfl) rfl
  by_cases hqa : q = "alice" <;> simp [hqa]

/-- Builds `cliCompShape.ImplHalf` at `cliCompFitsPinned w` from three `cliRunAbortOnPanic`
executions (`init`, `send`, `recv`) with arbitrary Call 1 and Call 2 output snapshots. -/
theorem ss_impl_half_pinned_of_three_calls_dirs
    {w : PQXDHSpqrSetup} {evs : List CliEvent}
    (hPlaus : w.Plausible)
    (hTor : TorsionShiftsRecorded compI0 w.torsionShifts)
    (hSpkId : w.spkId = 7) (hKpkId : w.kpkId = 9)
    (hBun : bundleBlob (ssBundle w) = CompSmallSubgroupTrace.bundleFast)
    {c2Msg : HwBytes}
    (hCanon : checkCanonicalPreKey c2Msg = true)
    (hStdin2 : checkRecvStdinBounded c2Msg = true)
    (hPq2 : ∀ q, parsePreKeyWire c2Msg = some q →
      PqFromHonest (sentBody CompSmallSubgroupTrace.sentWireBytes).toList q.message)
    (hEvs : cliEvents c2Msg = evs)
    (H : Arm64.Process.ElfImage)
    (files0 : List (String × HwBytes)) (outDir1 outDir2 : DirectorySnapshot)
    (hValid0 : ValidCall0Files files0 = true)
    (hRun0 : cliRunAbortOnPanic H compHooks0 (ssInp0 w) = some (ssOut0 files0))
    (hRun1 : cliRunAbortOnPanic H compHooks0 (ssInp1 files0) = some (.exited 0 ssC1Out outDir1))
    (hRun2 : cliRunAbortOnPanic H compHooks0 (ssInp2 w c2Msg ssC2Coins) =
      some (.exited 0 ssC2Out outDir2)) :
    cliCompShape.ImplHalf (cliCompFitsPinned w) H evs := by
  have hFits := cliCompFitsPinned_compI0_of_plausible w hPlaus hTor
  have hwf := compRecordsI0_wf_of_plausible w hPlaus
  refine ⟨(compI0, compHooks0), compRecordsI0 w, hFits, ⟨hFits.2.1, hFits.2.2⟩, ?_, ?_⟩
  ·
    rw [← hEvs]
    have hHonBun : HonestBundleDir compI0 (compRecordsI0 w) (ssBundle w) := by
      rw [← honestPublicBundle_eq_ssBundle w]
      exact honestBundleDir_honestPublicBundle compI0_cryptoEquationsHold hwf
    have hAliceFp : ∀ x ∈ ssAliceBaseFiles w, CliFilePath x.1 := by
      rw [← commonFiles_alice_eq_ssAliceBaseFiles w]
      exact commonFiles_alice_cliFilePath compI0 (compRecordsI0 w)
    have hBobFp : ∀ x ∈ ssBobBaseFiles w, CliFilePath x.1 := by
      rw [← bobFiles_eq_ssBobBaseFiles w hSpkId hKpkId]
      intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact commonFiles_bob_cliFilePath hwf.1 x h1
      · exact bobPreKeyFiles_cliFilePath rfl hSpkId hKpkId x h2
    have hAliceBd : FilesBounded (filesOf (ssAliceBaseFiles w)) := by
      rw [← commonFiles_alice_eq_ssAliceBaseFiles w]
      exact filesBounded_of_cliFilePaths (commonFiles_alice_cliFilePath compI0 (compRecordsI0 w))
        (commonFiles_alice_bounded compI0_cryptoEquationsHold hwf)
    have hBobBd : FilesBounded (filesOf (ssBobBaseFiles w)) := by
      rw [← bobFiles_eq_ssBobBaseFiles w hSpkId hKpkId]
      apply filesBounded_of_cliFilePaths
      · intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact commonFiles_bob_cliFilePath hwf.1 x h1
        · exact bobPreKeyFiles_cliFilePath rfl hSpkId hKpkId x h2
      · intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact commonFiles_bob_bounded compI0_cryptoEquationsHold hwf x h1
        · exact bobPreKeyFiles_bounded compI0_cryptoEquationsHold hwf rfl x h2
    let t0 := mkTurn (filesOf (ssAliceBaseFiles w)) (filesOf (ssBobBaseFiles w)) [] false
    rw [initTurn_eq_mkTurn w hSpkId hKpkId]
    have hVal0 : ValidCall compI0 (compRecordsI0 w) t0 (ssCall0 w) := by
      have hNoSess0 : t0.records (compRecordsI0 w) "alice" = none := by
        dsimp only [t0]
        rw [← initTurn_eq_mkTurn w hSpkId hKpkId]
        exact initDirs_alice_no_session compI0 (compRecordsI0 w)
      have hc0Len : ssC0Coins.length = 192 := cliCoins0_length
      dsimp only [ValidCall, StdinBounded, BobCallAllowed, ssCall0, t0]
      exact ⟨hc0Len, trivial, by simpa [mkTurn] using hAliceBd, (fun h => nomatch h),
        rfl, rfl, rfl, rfl, hNoSess0, honestBundleDir_to_flat_and_honest hHonBun⟩
    have hInp0 : InputsFor (ssCall0 w) (t0.dirs "alice") (ssInp0 w) := by
      rw [ssInp0_eq_mkInp]
      exact inputsFor_of_cliFilePaths (ssCall0 w) (ssAliceBaseFiles w) hAliceFp
        (bundleFiles_cliFilePath (ssBundle w))
        (by rw [← commonFiles_alice_eq_ssAliceBaseFiles w]
            exact commonFiles_alice_bounded compI0_cryptoEquationsHold hwf)
        (fun x hx => ((honestBundleDir_to_flat_and_honest hHonBun).1 x hx).2)
        (by have hc0Len : ssC0Coins.length = 192 := cliCoins0_length; dsimp only [ssCall0]; omega)
    have hEv0 : runEventOf (ssCall0 w) (some (0, [])) = evInit := by
      have hpbf := parseBundleFiles_of_honestBundleDir hHonBun
      have hbunEq : CompRX0SS38.bunBytes = CompSmallSubgroupTrace.bundleFast := by
        rw [CompRX0SS38.bunBytes_eq]; rfl
      unfold runEventOf runInput ssCall0 evInit
      dsimp only
      rw [hpbf, Option.map_some, Option.getD_some, hBun, ← hbunEq, cliCoins0_eq_ssC0Coins]
      rfl
    let t1 := mkTurn (filesOf (scrubList files0)) (filesOf (ssBobBaseFiles w)) [] false
    have hAfter0 : t0.after (compRecordsI0 w) (ssCall0 w) 0 [] (filesOf files0) = t1 := by
      rw [after_alice_mkTurn (w := w) rfl,
        scrub_filesOf_eq_filesOf_scrubList (validCall0Files_cliFilePath hValid0)]
      rfl
    have hVal1 : ValidCall compI0 (compRecordsI0 w) t1 ssCall1 := by
      have hc1Len : ssC1Coins.length = 64 := by decide +kernel
      have hptLen : ssC1Pt.length < 2 ^ 32 := by decide +kernel
      dsimp only [ValidCall, StdinBounded, BobCallAllowed, ssCall1, t1, mkTurn]
      exact ⟨hc1Len, hptLen,
        validCall0Files_scrub_bounded hValid0,
        (fun h => nomatch h), Or.inl rfl, rfl, rfl, by decide,
        validCall0Files_alice_records_ne_none hValid0 rfl (filesOf (ssBobBaseFiles w)) [] false⟩
    have hInp1 : InputsFor ssCall1 (t1.dirs "alice") (ssInp1 files0) := by
      rw [ssInp1_eq_mkInp]
      exact inputsFor_of_cliFilePaths ssCall1 (scrubList files0)
        (validCall0Files_scrub_cliFilePath hValid0) (fun _ h => nomatch h)
        (fun x hx => by
          have hv := hValid0; unfold ValidCall0Files at hv; simp only [Bool.and_eq_true] at hv
          exact of_decide_eq_true (List.all_eq_true.mp hv.1.2 x hx))
        (fun _ h => nomatch h)
        (by change ssC1Coins.length < 2 ^ 31; decide +kernel)
    have hEv1 : runEventOf ssCall1 (some (0, ssC1Out)) = evSend := by
      unfold runEventOf runInput ssCall1 evSend
      rw [ptB_eq_ssC1Pt, cB_eq_ssC1Coins, sentWirePlant_eq_ssC1Out]
      rfl
    let t2 := mkTurn (scrub outDir1) (filesOf (ssBobBaseFiles w)) (sentBody ssC1Out).toList false
    have hAfter1 : t1.after (compRecordsI0 w) ssCall1 0 ssC1Out outDir1 = t2 :=
      after_alice_mkTurn (w := w) rfl
    have hVal2 : ValidCall compI0 (compRecordsI0 w) t2 (ssCall2 c2Msg ssC2Coins) := by
      have hba : ("bob" : String) ≠ "alice" := by decide
      have hc2Len : ssC2Coins.length = 32 := by decide +kernel
      have hHeadNe := canonicalPreKey_head_ne_whisper (canonicalPreKey_of_check hCanon)
      dsimp only [ValidCall, BobCallAllowed, ssCall2, t2]
      refine ⟨hc2Len, stdinBounded_recv_of_check hStdin2,
        by simpa [mkTurn, hba] using hBobBd, (fun h => nomatch h),
        Or.inr rfl, rfl, rfl, Or.inr ⟨rfl, Or.inl hHeadNe, ?_⟩⟩
      intro q hq
      have hPq2' := hPq2 q hq
      rw [sentWireSS_eq_ssC1Out] at hPq2'
      exact hPq2'
    have hba : ("bob" : String) ≠ "alice" := by decide
    have hInp2 : InputsFor (ssCall2 c2Msg ssC2Coins) (t2.dirs "bob")
        (ssInp2 w c2Msg ssC2Coins) := by
      dsimp only [t2, mkTurn]
      simp only [hba, ↓reduceIte]
      rw [ssInp2_eq_mkInp]
      exact inputsFor_of_cliFilePaths (ssCall2 c2Msg ssC2Coins) (ssBobBaseFiles w) hBobFp
        (fun _ h => nomatch h)
        (by rw [← bobFiles_eq_ssBobBaseFiles w hSpkId hKpkId]
            intro x hx
            exact (List.mem_append.mp hx).elim
              (commonFiles_bob_bounded compI0_cryptoEquationsHold hwf x)
              (bobPreKeyFiles_bounded compI0_cryptoEquationsHold hwf rfl x))
        (fun _ h => nomatch h)
        (by change ssC2Coins.length < 2 ^ 31; decide +kernel)
    have hEv2 : runEventOf (ssCall2 c2Msg ssC2Coins) (some (0, ssC2Out)) = evRecv c2Msg := by
      unfold runEventOf runInput ssCall2 evRecv
      rw [rngMsg39_eq_ssC2Coins, acceptMsg40_eq_ssC2Out]
      rfl
    unfold cliEvents
    rw [← hEv0, ← hEv1, ← hEv2]
    refine CliTraces.step (leaks := []) (fun _ h => nomatch h) hVal0 hInp0 hRun0 ?_
    rw [hAfter0]
    refine CliTraces.step (leaks := []) (fun _ h => nomatch h) hVal1 hInp1 hRun1 ?_
    rw [hAfter1]
    refine CliTraces.step (leaks := []) (fun _ h => nomatch h) hVal2 hInp2 hRun2 ?_
    exact CliTraces.done _
  ·
    rw [← hEvs]
    apply invertsGuarded_of_noInverts
    unfold cliEvents evInit evSend evRecv
    rfl

/-- Specialization of `ss_impl_half_pinned_of_three_calls_dirs` to concrete post-call file lists. -/
theorem ss_impl_half_pinned_of_three_calls
    {w : PQXDHSpqrSetup} {evs : List CliEvent}
    (hPlaus : w.Plausible)
    (hTor : TorsionShiftsRecorded compI0 w.torsionShifts)
    (hSpkId : w.spkId = 7) (hKpkId : w.kpkId = 9)
    (hBun : bundleBlob (ssBundle w) = CompSmallSubgroupTrace.bundleFast)
    {c2Msg : HwBytes}
    (hCanon : checkCanonicalPreKey c2Msg = true)
    (hStdin2 : checkRecvStdinBounded c2Msg = true)
    (hPq2 : ∀ q, parsePreKeyWire c2Msg = some q →
      PqFromHonest (sentBody CompSmallSubgroupTrace.sentWireBytes).toList q.message)
    (hEvs : cliEvents c2Msg = evs)
    (H : Arm64.Process.ElfImage)
    (files0 files1 files2 : List (String × HwBytes))
    (hValid0 : ValidCall0Files files0 = true)
    (_hValid1 : ValidCall1Files files1 = true)
    (hRun0 : cliRunAbortOnPanic H compHooks0 (ssInp0 w) = some (ssOut0 files0))
    (hRun1 : cliRunAbortOnPanic H compHooks0 (ssInp1 files0) = some (ssOut1 files1))
    (hRun2 : cliRunAbortOnPanic H compHooks0 (ssInp2 w c2Msg ssC2Coins) =
      some (ssOut2 ssC2Out files2)) :
    cliCompShape.ImplHalf (cliCompFitsPinned w) H evs :=
  ss_impl_half_pinned_of_three_calls_dirs hPlaus hTor hSpkId hKpkId hBun hCanon hStdin2 hPq2 hEvs
    H files0 (filesOf files1) (filesOf files2) hValid0 hRun0 hRun1 hRun2

def hbC2Msg : HwBytes := CompSmallSubgroupTrace.highBitWireFast

def hbInp0 : Inputs := ssInp0 Witnesses.Cheval26SmallSubgroupHighBitCli.setup
def hbInp1 (files0 : List (String × HwBytes)) : Inputs := ssInp1 files0
def hbInp2 : Inputs := ssInp2 Witnesses.Cheval26SmallSubgroupHighBitCli.setup hbC2Msg ssC2Coins

def hbOut0 (files0 : List (String × HwBytes)) : Outcome := ssOut0 files0
def hbOut1 (files1 : List (String × HwBytes)) : Outcome := ssOut1 files1
def hbOut2 (files2 : List (String × HwBytes)) : Outcome := ssOut2 ssC2Out files2

theorem hbBundle_blob_eq :
    bundleBlob (ssBundle Witnesses.Cheval26SmallSubgroupHighBitCli.setup) =
      CompSmallSubgroupTrace.bundleFast := by
  decide +kernel

theorem hbTrace_invertsGuarded :
    InvertsGuarded compI0 (compRecordsI0 Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
      Witnesses.Cheval26SmallSubgroupHighBitCli.trace := by
  rw [← Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.cliEvents_eq]
  exact invertsGuarded_of_noInverts rfl

private theorem hb_pqFromHonest :
    ∀ q, parsePreKeyWire hbC2Msg = some q →
      PqFromHonest (sentBody CompSmallSubgroupTrace.sentWireBytes).toList q.message := by
  intro q hq
  apply CompSmallSubgroupTrace.highBit_pqFromHonest q
  rw [CompSmallSubgroupTrace.highBitWireBytes_eq]
  exact hq

private theorem hb_cliEvents_eq :
    cliEvents hbC2Msg = Witnesses.Cheval26SmallSubgroupHighBitCli.trace := by
  have h1 : hbC2Msg = CompSmallSubgroupTrace.highBitWireBytes :=
    CompSmallSubgroupTrace.highBitWireBytes_eq.symm
  rw [h1,
    ← Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.recvMsg38_eq_ss_highBitWireBytes]
  exact Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.cliEvents_eq

theorem impl_half_pinned_of_three_calls_dirs
    (H : Arm64.Process.ElfImage)
    (files0 : List (String × HwBytes)) (outDir1 outDir2 : DirectorySnapshot)
    (hValid0 : ValidCall0Files files0 = true)
    (hRun0 : cliRunAbortOnPanic H compHooks0 hbInp0 = some (hbOut0 files0))
    (hRun1 : cliRunAbortOnPanic H compHooks0 (hbInp1 files0) = some (.exited 0 ssC1Out outDir1))
    (hRun2 : cliRunAbortOnPanic H compHooks0 hbInp2 = some (.exited 0 ssC2Out outDir2)) :
    cliCompShape.ImplHalf
      (cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
      H Witnesses.Cheval26SmallSubgroupHighBitCli.trace :=
  ss_impl_half_pinned_of_three_calls_dirs
    (w := Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
    (by decide +kernel) (fun _ h => nomatch h) rfl rfl hbBundle_blob_eq
    (by decide +kernel) (by decide +kernel) hb_pqFromHonest hb_cliEvents_eq
    H files0 outDir1 outDir2 hValid0 hRun0 hRun1 hRun2

/-- Pinned `ImplHalf` for `Cheval26SmallSubgroupHighBitCli` from three concrete CLI runs. -/
theorem impl_half_pinned_of_three_calls
    (H : Arm64.Process.ElfImage)
    (files0 files1 files2 : List (String × HwBytes))
    (hValid0 : ValidCall0Files files0 = true)
    (hValid1 : ValidCall1Files files1 = true)
    (hRun0 : cliRunAbortOnPanic H compHooks0 hbInp0 = some (hbOut0 files0))
    (hRun1 : cliRunAbortOnPanic H compHooks0 (hbInp1 files0) = some (hbOut1 files1))
    (hRun2 : cliRunAbortOnPanic H compHooks0 hbInp2 = some (hbOut2 files2)) :
    cliCompShape.ImplHalf
      (cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
      H Witnesses.Cheval26SmallSubgroupHighBitCli.trace :=
  ss_impl_half_pinned_of_three_calls
    (w := Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
    (by decide +kernel) (fun _ h => nomatch h) rfl rfl hbBundle_blob_eq
    (by decide +kernel) (by decide +kernel) hb_pqFromHonest hb_cliEvents_eq
    H files0 files1 files2 hValid0 hValid1 hRun0 hRun1 hRun2

/-- Unpinned `ImplHalf` for `Cheval26SmallSubgroupHighBitCli` from three concrete CLI runs. -/
theorem impl_half_of_three_calls
    (H : Arm64.Process.ElfImage)
    (files0 files1 files2 : List (String × HwBytes))
    (hValid0 : ValidCall0Files files0 = true)
    (hValid1 : ValidCall1Files files1 = true)
    (hRun0 : cliRunAbortOnPanic H compHooks0 hbInp0 = some (hbOut0 files0))
    (hRun1 : cliRunAbortOnPanic H compHooks0 (hbInp1 files0) = some (hbOut1 files1))
    (hRun2 : cliRunAbortOnPanic H compHooks0 hbInp2 = some (hbOut2 files2)) :
    cliCompShape.ImplHalf
      Witnesses.Cheval26SmallSubgroupHighBitCli.fits
      H Witnesses.Cheval26SmallSubgroupHighBitCli.trace := by
  obtain ⟨iw, r, hfit, hc, htr⟩ :=
    impl_half_pinned_of_three_calls H files0 files1 files2 hValid0 hValid1 hRun0 hRun1 hRun2
  exact ⟨iw, r, cliCompFits_of_pinned hfit, hc, htr⟩

theorem hbInputs_kernel_reducible :
    hbInp0.argv = ["init", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1", "bundle"] ∧
      hbInp0.files.length = 9 ∧
      hbInp0.files.all (fun f => decide (CliFilePath f.1)) = true ∧
      hbInp0.files.foldl (fun acc f => acc + f.2.length) 0 > 0 ∧
      hbInp2.argv = ["recv", "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"] ∧
      hbInp2.files.length = 8 ∧
      hbInp2.files.all (fun f => decide (CliFilePath f.1)) = true ∧
      hbInp2.files.foldl (fun acc f => acc + f.2.length) 0 > 0 ∧
      hbInp2.stdin.length > 0 := by
  decide +kernel

end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace
