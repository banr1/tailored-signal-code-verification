/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel58
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Data.String.Defs
import Symbolic.Proofs.Refinement.Composed.Cli.ParD7PureGates
import Symbolic.Proofs.Swarm.CREF.Cli.DirCodecBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux

/-!
# Concrete Multi-Turn CLI Traces for Session Non-Vacuity

Constructs `CliTraces (runFnToRelation run) myInterp r0 (CliTurn.init (initDirs myInterp r0))`
derivations for `evsHonest` (7 exit-0 calls across Alice and Bob) and `evsExposed` (9 exit-0
calls with two chain-key `.leak` events before Call 7), quantified over all
`(X : UnreachedPqxdhPrimitives)` and `(run : CliRun)` satisfying `CliSpecPqxdh run X myParams`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionTraces

set_option maxRecDepth 200000

open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (PreKeyProto)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (secretBytes setupPublic slice pubBytes ecKey kyberKey
   HonestBundle parsePreKeyWire preKeyWire sentBody PqFromHonest
   EligibleForSessionPromotion recordBytes KeyInRecord)
open DY.Libsignal.Composed.Refinement.Cli
  (DirectorySnapshot CliCall CliTurn initDirs commonFiles bobPreKeyFiles idSecret peerIdSecret
   peerOf sessionPathOf bundleBlob parseBundleFiles
   ValidCall StdinBounded FilesBounded InputsFor
   PreKeyNoMatch KeyInDir LeaksFrom HonestBundleFiles
   runInput runEventOf CliTraces InvertsGuarded CoinsFresh runFnToRelation scrub
   ModelAgree bundleFilesFlat_publicBundleOf parseBundleFiles_publicBundleOf)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.LibsignalProtoCodec (encodeBytesField)
open CryptoVerification.E2E
  (UnreachedPqxdhPrimitives RecordExtras PreKeyMessageFields wirePrekey wireWhisper encodeRecordUnderExtras keyPairOf)
open CryptoVerification.SignalSession
  (CliRun CliSpecPqxdh PqParty PqxdhPartyInSpecDomain Address publicBundleOf PqSessionMatches
   pqInputs pqInitInputs pqSendInputs pqRecvInputs
   filesOf encodeDir signedRecordBytes sessionFile bundleDir partyAddress le32)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs (invertsGuarded_of_noInverts)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myParams myInterp myHooks_agree pt0 pt1 ptReply0 pt2 mkRecords_wf)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 tapeInitBytes tapeInit cSend0 cSend1 cSendReply0 cSend2
   cSend0Vec cSend1Vec cSendReply0Vec cSend2Vec
   rc3Bytes rc4Bytes rc6Bytes rc8Bytes rc3 rc4 rc6 rc8)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04
  (stA0_cli stA1_cli stA2_cli stA3_cli stB0_cli stB1_cli stB2_cli bE_cli
   x_A x_B g_B1 pkMsg0 pkMsg1 wire0 wire1 rck_A0
   keyToBytes32_rc3 keyToBytes32_rc4 r0_opaque5 r0_opaque6 r0_opaque7
   kp_idA kp_idB kp_spkB
   wire0_eq wire1_eq call0_model_X call1_model call2_model
   call3_model_X call4_sessionMatches call4_model_X)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel58
  (sck_A4 g_A4 stA4_cli stA5_cli stB3_cli stB4_cli
   bodyReply0 wireReply0 body2 wire2
   keyToBytes32_rc6 keyToBytes32_rc8 wireReply0_eq wire2_eq
   call5_model call6_model call7_model call8_model
   wfPq_stA0 wfPq_stB0 wfPq_stA1 wfPq_stA2 wfPq_stA3 wfPq_stA4
   wfPq_stB1 wfPq_stB2 wfPq_stB3)
open Symbolic.Swarm.CREF.Cli
  (RegularFileList regularFile_root regularFileList_encodeDir regularFileList_bundle_files
   filesOf_append_of_regular mem_of_filesOf_eq_some
   filesOf_eq_none_of_forall_ne filesOf_eq_some_of_mem_nodup
   isScrubbedPath_bundle_files scrub_filesOf_pqInputs_accept
   secretBytes_2_length pubBytes_eq_keyPairOf_of_modelAgree pubBytes_length_of_modelAgree
   bytesToVec_toList_of_len encodeDir_norm_nodup encodeRecordX_ne_nil
   pqSession encodeRecordX_eq_recordBytes_of_wfPq sentBody_wireWhisper)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)

/-! ## Concrete `CliCall`s, Leaked Keys, and CLI Event Sequences -/

def call0 : CliCall := ⟨"alice", .init (peerOf r0 "alice") bundleDir,
  (publicBundleOf bE_cli).files bundleDir, [], tapeInitBytes⟩
def call1 : CliCall := ⟨"alice", .send (peerOf r0 "alice"), [], pt0, cSend0⟩
def call2 : CliCall := ⟨"alice", .send (peerOf r0 "alice"), [], pt1, cSend1⟩
def call3 : CliCall := ⟨"bob", .recv (peerOf r0 "bob"), [], wire0, rc3Bytes⟩
def call4 : CliCall := ⟨"bob", .recv (peerOf r0 "bob"), [], wire1, rc4Bytes⟩
def call5 : CliCall := ⟨"bob", .send (peerOf r0 "bob"), [], ptReply0, cSendReply0⟩
def call6 : CliCall := ⟨"alice", .recv (peerOf r0 "alice"), [], wireReply0, rc6Bytes⟩
def call7 : CliCall := ⟨"alice", .send (peerOf r0 "alice"), [], pt2, cSend2⟩
def call8 : CliCall := ⟨"bob", .recv (peerOf r0 "bob"), [], wire2, rc8Bytes⟩

def ckrBytes : HwBytes := CryptoGames.HMAC.keyToBytes32 rck_A0
def cksBytes : HwBytes := CryptoGames.HMAC.keyToBytes32 sck_A4

def runEv0 : RunEvent := runEventOf call0 (some (0, []))
def runEv1 : RunEvent := runEventOf call1 (some (0, wire0))
def runEv2 : RunEvent := runEventOf call2 (some (0, wire1))
def runEv3 : RunEvent := runEventOf call3 (some (0, pt0))
def runEv4 : RunEvent := runEventOf call4 (some (0, pt1))
def runEv5 : RunEvent := runEventOf call5 (some (0, wireReply0))
def runEv6 : RunEvent := runEventOf call6 (some (0, ptReply0))
def runEv7 : RunEvent := runEventOf call7 (some (0, wire2))
def runEv8 : RunEvent := runEventOf call8 (some (0, pt2))

def leakEvCkr : EnvEvent := .leak "alice" ckrBytes
def leakEvCks : EnvEvent := .leak "alice" cksBytes
def evLeaks : List CliEvent := [.env leakEvCkr, .env leakEvCks]

def evsHonest : List CliEvent :=
  [.run runEv0, .run runEv1, .run runEv2, .run runEv3, .run runEv4, .run runEv5, .run runEv6]

def evsExposed : List CliEvent :=
  evsHonest ++ [.env leakEvCkr, .env leakEvCks, .run runEv7, .run runEv8]

theorem runEv0_input : runEv0.input = bundleBlob (publicBundleOf bE_cli) := by
  dsimp only [runEv0, runEventOf, runInput, call0]
  rw [parseBundleFiles_publicBundleOf bE_cli]
  rfl

/-! ## Turn Representation and Provisioned Directory Equations -/

def mkTurn (stA stB : PqParty) (sent : List HwBytes) : CliTurn where
  dirs p :=
    if p = "alice" then filesOf (encodeDir myParams stA)
    else if p = "bob" then filesOf (encodeDir myParams stB)
    else fun _ => none
  sent := sent
  bobOff := false

private theorem r0_secretBytes_eq (k : Nat) :
    secretBytes r0 k =
      (([(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)][k]?).map fun p =>
        r0.fresh p.1 p.2).getD [] := by
  unfold secretBytes
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r0 (mkRecords_wf false).1,
      show r0.withOpk = false from rfl]
  simp

private theorem initDirs_alice_eq :
    initDirs myInterp r0 "alice" = filesOf (encodeDir myParams stA0_cli) := by
  have hAg : ModelAgree myInterp myParams := myHooks_agree
  have hid : idSecret r0 "alice" = (List.Vector.replicate 32 1#8).toList := by
    unfold idSecret DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    simp only [(show ("alice" : Participant) = r0.alice from rfl), ↓reduceIte, r0_secretBytes_eq]
    rfl
  have hpid : peerIdSecret r0 "alice" = (List.Vector.replicate 32 6#8).toList := by
    unfold peerIdSecret DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes
    simp only [(show ("alice" : Participant) = r0.alice from rfl), ↓reduceIte, r0_secretBytes_eq]
    rfl
  have hdir : initDirs myInterp r0 "alice" = filesOf (commonFiles myInterp r0 "alice") := by
    unfold initDirs
    simp only [(show ("alice" : Participant) = r0.alice from rfl), ↓reduceIte]
  rw [hdir]
  apply congrArg filesOf
  unfold commonFiles encodeDir stA0_cli
  dsimp only
  rw [hid, pubBytes_eq_keyPairOf_of_modelAgree hAg, kp_idA,
      hpid, pubBytes_eq_keyPairOf_of_modelAgree hAg, kp_idB]
  decide +kernel

private theorem initDirs_bob_eq :
    initDirs myInterp r0 "bob" = filesOf (encodeDir myParams stB0_cli) := by
  have hAg : ModelAgree myInterp myParams := myHooks_agree
  have hid : idSecret r0 "bob" = (List.Vector.replicate 32 6#8).toList := by
    unfold idSecret DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes
    simp only [(show ("bob" : Participant) = r0.bob from rfl),
      (show (r0.bob = r0.alice) = False by decide), ↓reduceIte, r0_secretBytes_eq]
    rfl
  have hpid : peerIdSecret r0 "bob" = (List.Vector.replicate 32 1#8).toList := by
    unfold peerIdSecret DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    simp only [(show ("bob" : Participant) = r0.bob from rfl),
      (show (r0.bob = r0.alice) = False by decide), ↓reduceIte, r0_secretBytes_eq]
    rfl
  have hsec2 : secretBytes r0 2 = (List.Vector.replicate 32 11#8).toList := by
    rw [r0_secretBytes_eq]; rfl
  have hdir : initDirs myInterp r0 "bob" =
      filesOf (commonFiles myInterp r0 "bob" ++ bobPreKeyFiles myInterp r0) := by
    unfold initDirs
    simp only [(show ("bob" : Participant) = r0.bob from rfl),
      (show (r0.bob = r0.alice) = False by decide), ↓reduceIte]
  rw [hdir]
  apply congrArg filesOf
  unfold commonFiles bobPreKeyFiles
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecBytes
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm
    encodeDir signedRecordBytes stB0_cli
  simp only [(show r0.withOpk = false from rfl), Bool.false_eq_true, ↓reduceIte, List.map]
  rw [hid, pubBytes_eq_keyPairOf_of_modelAgree hAg, kp_idB,
      hpid, pubBytes_eq_keyPairOf_of_modelAgree hAg, kp_idA,
      hsec2, pubBytes_eq_keyPairOf_of_modelAgree hAg, kp_spkB,
      r0_opaque5, r0_opaque6, r0_opaque7]
  decide +kernel

private theorem initTurn_eq :
    CliTurn.init (initDirs myInterp r0) = mkTurn stA0_cli stB0_cli [] := by
  unfold CliTurn.init mkTurn
  apply congrArg (CliTurn.mk · [] false)
  funext p
  by_cases ha : p = "alice"
  · subst ha; simp [initDirs_alice_eq]
  · by_cases hb : p = "bob"
    · subst hb; simp [ha, initDirs_bob_eq]
    · simp only [ha, hb, ↓reduceIte]
      unfold initDirs
      change (if p = "alice" then _ else if p = "bob" then _ else _) = _
      simp [ha, hb]

/-! ## Guard, `InputsFor`, `scrub`, Promotion, and Leak Helpers -/

private theorem inputsFor_pqInputs {c : CliCall} {st : PqParty}
    (hwf : PqxdhPartyInSpecDomain myParams st)
    (hload_enc : ∀ p ∈ (encodeDir myParams st).map Prod.fst,
      (Arm64.hasLeadingSlash p || Arm64.hasDotDot p) = false)
    (hreg_bun : RegularFileList c.bundle)
    (hload_bun : ∀ f ∈ c.bundle,
      (Arm64.hasLeadingSlash f.1 || Arm64.hasDotDot f.1) = false ∧ f.2.length < 2 ^ 31)
    (hco_lt : c.coins.length < 2 ^ 31) :
    InputsFor c (filesOf (encodeDir myParams st))
      (pqInputs myParams st c.cmd c.bundle c.coins c.stdin) := by
  have hreg_enc := regularFileList_encodeDir myParams st
  have hreg_ex : RegularFileList c.extra :=
    hreg_bun.append (regularFile_root (by decide) (by decide) (by decide) (by decide))
  have hfiles_eq : (pqInputs myParams st c.cmd c.bundle c.coins c.stdin).files =
      encodeDir myParams st ++ c.extra := by
    unfold pqInputs CliCall.extra
    exact List.append_assoc _ _ _
  refine ⟨rfl, rfl, rfl, fun p _ => ?_, ?_⟩
  · rw [hfiles_eq, filesOf_append_of_regular hreg_enc hreg_ex p]
  · rw [hfiles_eq]
    intro f hf
    obtain ⟨h1, h2, _, _⟩ := (hreg_enc.append hreg_ex) f hf
    have ⟨hl, hsz⟩ : (Arm64.hasLeadingSlash f.1 || Arm64.hasDotDot f.1) = false ∧
        f.2.length < 2 ^ 31 := by
      rcases List.mem_append.mp hf with hfe | hfx
      · exact ⟨hload_enc f.1 (List.mem_map_of_mem hfe), (hwf.2.1 f hfe).1⟩
      · rcases List.mem_append.mp hfx with hfb | hfc
        · exact hload_bun f hfb
        · simp only [List.mem_singleton] at hfc
          subst hfc
          exact ⟨by dsimp only; decide, hco_lt⟩
    rw [Bool.or_eq_false_iff] at hl
    exact ⟨h1, h2, hl.1, hl.2, Nat.le_trans (Nat.le_of_lt hsz) (by decide)⟩

private theorem filesBounded_of_wfPq {st : PqParty} (hwf : PqxdhPartyInSpecDomain myParams st) :
    FilesBounded (filesOf (encodeDir myParams st)) := by
  intro path b h
  obtain ⟨f, hf, _, hfb⟩ := mem_of_filesOf_eq_some (regularFileList_encodeDir myParams st) h
  exact hfb ▸ (hwf.2.1 f hf).1

private theorem sub_of_fst_sub {l₁ l₂ : List (String × HwBytes)}
    (h : ∀ p ∈ l₁.map Prod.fst, p ∈ l₂.map Prod.fst) :
    ∀ f ∈ l₁, ∃ g ∈ l₂, f.1 = g.1 := by
  intro f hf
  obtain ⟨g, hg, heq⟩ := List.mem_map.mp (h f.1 (List.mem_map_of_mem hf))
  exact ⟨g, hg, heq.symm⟩

private theorem records_alice_stA0 :
    (mkTurn stA0_cli stB0_cli []).records r0 "alice" = none := by
  have hdir : (mkTurn stA0_cli stB0_cli []).dirs "alice" = filesOf (encodeDir myParams stA0_cli) := by
    simp [mkTurn]
  have hd : filesOf (encodeDir myParams stA0_cli) (sessionPathOf r0 "alice") = none := by
    have hall : ((encodeDir myParams stA0_cli).all fun f =>
        Arm64.normalizePath (sessionPathOf r0 "alice") != Arm64.normalizePath f.1) = true := by
      decide
    exact filesOf_eq_none_of_forall_ne (regularFileList_encodeDir myParams stA0_cli)
      (fun f hf => bne_iff_ne.mp (List.all_eq_true.mp hall f hf))
  unfold CliTurn.records
  rw [hdir, hd]

private theorem records_bob_stB0 {stA : PqParty} {sent : List HwBytes} :
    (mkTurn stA stB0_cli sent).records r0 "bob" = none := by
  have hdir : (mkTurn stA stB0_cli sent).dirs "bob" = filesOf (encodeDir myParams stB0_cli) := by
    simp [mkTurn, show ("bob" : String) ≠ "alice" by decide]
  have hd : filesOf (encodeDir myParams stB0_cli) (sessionPathOf r0 "bob") = none := by
    have hall : ((encodeDir myParams stB0_cli).all fun f =>
        Arm64.normalizePath (sessionPathOf r0 "bob") != Arm64.normalizePath f.1) = true := by
      decide
    exact filesOf_eq_none_of_forall_ne (regularFileList_encodeDir myParams stB0_cli)
      (fun f hf => bne_iff_ne.mp (List.all_eq_true.mp hall f hf))
  unfold CliTurn.records
  rw [hdir, hd]

private theorem records_some_of_session {stA stB st : PqParty} {sent : List HwBytes}
    {p : Participant} {x : RecordExtras} {g : GhostState HwBytes}
    (hdir : (mkTurn stA stB sent).dirs p = filesOf (encodeDir myParams st))
    (hsess : st.session = some (x, g))
    (hpath : sessionPathOf r0 p = sessionFile (partyAddress st.party.other))
    (hsig : st.signed.length ≤ 1) (hot : st.oneTime.length ≤ 1)
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort.length ≤ 1) :
    (mkTurn stA stB sent).records r0 p = some (encodeRecordUnderExtras (fun _ => x) g) := by
  unfold CliTurn.records
  rw [hdir, hpath, filesOf_eq_some_of_mem_nodup (regularFileList_encodeDir myParams st)
    (encodeDir_norm_nodup myParams st hsig hot hkot hklr)
    (b := encodeRecordUnderExtras (fun _ => x) g)
    (by unfold encodeDir; simp [hsess]) rfl]
  simp only [encodeRecordX_ne_nil x g, ↓reduceIte]

private theorem stdinBounded_recv_of_len {c : CliCall} {peer : Address}
    (hcmd : c.cmd = .recv peer)
    (hlen : c.stdin.length ≤ 2500)
    (hpkw : ((parsePreKeyWire c.stdin).map fun q => decide (q.message.length + 2048 < 2 ^ 32)).getD true = true) :
    StdinBounded c := by
  unfold StdinBounded
  rw [hcmd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro body hb
    have hl := congrArg List.length hb
    rw [List.length_cons] at hl; omega
  · intro _; omega
  · intro q hq
    rw [hq] at hpkw
    exact of_decide_eq_true hpkw
  · intro preKeyId spkId kpkId regId ik ek ct msg _ _ _ heq
    have hl := congrArg List.length heq
    unfold preKeyWire PreKeyProto.encode at hl
    dsimp only at hl
    have hm : msg.length ≤ (encodeBytesField 4 (some msg)).length := by
      unfold encodeBytesField
      simp only [List.length_append]
      omega
    simp only [List.length_cons, List.length_append] at hl
    omega

private theorem slice_mid {a b c : HwBytes} {off len : Nat}
    (ha : a.length = off) (hb : b.length = len) :
    slice (a ++ b ++ c) off len = b := by
  unfold slice
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hb]

private theorem honestBundle_bE_cli :
    HonestBundle myInterp r0 (bundleBlob (publicBundleOf bE_cli)) := by
  intro _
  dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecBytes,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes]
  have hAg : ModelAgree myInterp myParams := myHooks_agree
  have hb : bundleBlob (publicBundleOf bE_cli) =
      (le32 20#32 ++ List.replicate 38 0#8 ++ le32 1#32) ++
      ecKey (pubBytes myInterp (secretBytes r0 2)) ++
      r0.opaqueBytes (setupPublic r0 5) ++
      le32 2#32 ++
      kyberKey (r0.opaqueBytes (setupPublic r0 6)) ++
      r0.opaqueBytes (setupPublic r0 7) ++
      ecKey (pubBytes myInterp (secretBytes r0 1)) := by
    have hpub2 : pubBytes myInterp (secretBytes r0 2) =
        (keyPairOf myParams.C (List.Vector.replicate 32 11#8)).publicKey.bytes.toList := by
      rw [r0_secretBytes_eq]
      exact pubBytes_eq_keyPairOf_of_modelAgree hAg (List.Vector.replicate 32 11#8)
    have hpub1 : pubBytes myInterp (secretBytes r0 1) =
        (keyPairOf myParams.C (List.Vector.replicate 32 6#8)).publicKey.bytes.toList := by
      rw [r0_secretBytes_eq]
      exact pubBytes_eq_keyPairOf_of_modelAgree hAg (List.Vector.replicate 32 6#8)
    rw [hpub2, kp_spkB, hpub1, kp_idB, r0_opaque5, r0_opaque6, r0_opaque7]
    rfl
  have h2len : (ecKey (pubBytes myInterp (secretBytes r0 2))).length = 33 := by
    have hAg' := pubBytes_length_of_modelAgree hAg (secretBytes_2_length (mkRecords_wf false))
    simp [ecKey, hAg']
  have h1len : (ecKey (pubBytes myInterp (secretBytes r0 1))).length = 33 := by
    have h1 : (secretBytes r0 1).length = 32 := by rw [r0_secretBytes_eq]; rfl
    have hAg' := pubBytes_length_of_modelAgree hAg h1
    simp [ecKey, hAg']
  have hop5 : (r0.opaqueBytes (setupPublic r0 5)).length = 64 := (mkRecords_wf false).2.2.2.1
  have hop6 : (kyberKey (r0.opaqueBytes (setupPublic r0 6))).length = 1569 := by
    have h6 : (r0.opaqueBytes (setupPublic r0 6)).length = 1568 := (mkRecords_wf false).2.2.2.2.1
    simp [kyberKey, h6]
  have hop7 : (r0.opaqueBytes (setupPublic r0 7)).length = 64 := (mkRecords_wf false).2.2.2.2.2.1
  have hl20 : (le32 20#32).length = 4 := rfl
  have hl1 : (le32 1#32).length = 4 := rfl
  have hl2 : (le32 2#32).length = 4 := rfl
  rw [hb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using slice_mid
      (a := le32 20#32 ++ List.replicate 38 0#8 ++ le32 1#32)
      (by simp only [List.length_append, List.length_replicate, hl20, hl1]) h2len
      (c := r0.opaqueBytes (setupPublic r0 5) ++ le32 2#32 ++
        kyberKey (r0.opaqueBytes (setupPublic r0 6)) ++
        r0.opaqueBytes (setupPublic r0 7) ++ ecKey (pubBytes myInterp (secretBytes r0 1)))
  · simpa [List.append_assoc] using slice_mid
      (a := (le32 20#32 ++ List.replicate 38 0#8 ++ le32 1#32) ++
        ecKey (pubBytes myInterp (secretBytes r0 2)))
      (by simp only [List.length_append, List.length_replicate, hl20, hl1, h2len]) hop5
      (c := le32 2#32 ++ kyberKey (r0.opaqueBytes (setupPublic r0 6)) ++
        r0.opaqueBytes (setupPublic r0 7) ++ ecKey (pubBytes myInterp (secretBytes r0 1)))
  · simpa [List.append_assoc] using slice_mid
      (a := (le32 20#32 ++ List.replicate 38 0#8 ++ le32 1#32) ++
        ecKey (pubBytes myInterp (secretBytes r0 2)) ++
        r0.opaqueBytes (setupPublic r0 5) ++ le32 2#32)
      (by simp only [List.length_append, List.length_replicate, hl20, hl1, h2len, hop5, hl2]) hop6
      (c := r0.opaqueBytes (setupPublic r0 7) ++ ecKey (pubBytes myInterp (secretBytes r0 1)))
  · simpa [List.append_assoc] using slice_mid
      (a := (le32 20#32 ++ List.replicate 38 0#8 ++ le32 1#32) ++
        ecKey (pubBytes myInterp (secretBytes r0 2)) ++
        r0.opaqueBytes (setupPublic r0 5) ++ le32 2#32 ++
        kyberKey (r0.opaqueBytes (setupPublic r0 6)))
      (by simp only [List.length_append, List.length_replicate, hl20, hl1, h2len, hop5, hl2, hop6])
      hop7 (c := ecKey (pubBytes myInterp (secretBytes r0 1)))
  · simpa [List.append_assoc] using slice_mid
      (a := (le32 20#32 ++ List.replicate 38 0#8 ++ le32 1#32) ++
        ecKey (pubBytes myInterp (secretBytes r0 2)) ++
        r0.opaqueBytes (setupPublic r0 5) ++ le32 2#32 ++
        kyberKey (r0.opaqueBytes (setupPublic r0 6)) ++
        r0.opaqueBytes (setupPublic r0 7))
      (by simp only [List.length_append, List.length_replicate, hl20, hl1, h2len, hop5, hl2, hop6, hop7])
      h1len (c := [])

private theorem honestBundleFiles_call0 : HonestBundleFiles myInterp r0 call0.bundle := by
  intro b hb
  rw [show call0.bundle = (publicBundleOf bE_cli).files bundleDir from rfl,
      parseBundleFiles_publicBundleOf bE_cli] at hb
  cases hb
  exact honestBundle_bE_cli

private theorem pqFromHonest_of_mem {sent : List HwBytes} {msg : HwBytes}
    (hmem : msg ∈ sent) : PqFromHonest sent msg :=
  fun m hm => ⟨msg, hmem, m, hm, rfl⟩

private theorem sentBody_wire0 : (sentBody wire0).toList = [pkMsg0.inner] := by decide +kernel
private theorem sentBody_wire1 : (sentBody wire1).toList = [pkMsg1.inner] := by decide +kernel

private theorem parsePreKey_wire0_msg {q} (h : parsePreKeyWire wire0 = some q) :
    q.message = pkMsg0.inner := by
  have hp : (parsePreKeyWire wire0).map (·.message) = some pkMsg0.inner := by decide +kernel
  rw [h] at hp; exact Option.some.inj hp

private theorem parsePreKey_wire1_msg {q} (h : parsePreKeyWire wire1 = some q) :
    q.message = pkMsg1.inner := by
  have hp : (parsePreKeyWire wire1).map (·.message) = some pkMsg1.inner := by decide +kernel
  rw [h] at hp; exact Option.some.inj hp

private theorem eligible_call4 :
    EligibleForSessionPromotion (encodeRecordUnderExtras (fun _ => x_B) g_B1) wire1 := by
  rw [encodeRecordX_eq_recordBytes_of_wfPq wfPq_stB1 rfl rfl]
  have hp : (parsePreKeyWire wire1).isSome = true := by decide +kernel
  obtain ⟨p1, hp1⟩ := Option.isSome_iff_exists.mp hp
  refine ⟨sessionToRecordRec (pqSession x_B g_B1), p1, rfl, rfl, hp1, ?_⟩
  have hbk : (parsePreKeyWire wire1).map (fun p => p.baseKey.take 33) =
      some (sessionToRecordRec (pqSession x_B g_B1)).current.aliceBaseKey := by decide +kernel
  rw [hp1] at hbk
  exact (Option.some.inj hbk).symm

private theorem not_preKeyNoMatch_alice {t : CliTurn} {c : CliCall}
    (hp : c.party = "alice") : ¬ PreKeyNoMatch r0 t c := by
  rintro ⟨hb, _⟩; rw [hp] at hb; exact absurd hb (by decide)

private theorem not_preKeyNoMatch_whisper {t : CliTurn} {c : CliCall} {body : HwBytes}
    (hs : c.stdin = wireWhisper :: body) : ¬ PreKeyNoMatch r0 t c := by
  rintro ⟨_, _, htag, _⟩; apply htag; rw [hs]; rfl

private theorem not_preKeyNoMatch_call3 {stA : PqParty} {sent : List HwBytes} :
    ¬ PreKeyNoMatch r0 (mkTurn stA stB0_cli sent) call3 := by
  rintro ⟨_, _, _, rec_, hrec, _⟩
  change (mkTurn stA stB0_cli sent).records r0 "bob" = some rec_ at hrec
  rw [records_bob_stB0] at hrec; cases hrec

private theorem not_preKeyNoMatch_call4 {stA : PqParty} {sent : List HwBytes} :
    ¬ PreKeyNoMatch r0 (mkTurn stA stB1_cli sent) call4 := by
  rintro ⟨_, _, _, rec_, hrec, hnelig⟩
  have hrecB : (mkTurn stA stB1_cli sent).records r0 "bob" =
      some (encodeRecordUnderExtras (fun _ => x_B) g_B1) :=
    records_some_of_session (st := stB1_cli) (by simp [mkTurn]) rfl (by decide)
      (by decide) (by decide) rfl (by decide)
  change (mkTurn stA stB1_cli sent).records r0 "bob" = some rec_ at hrec
  rw [hrecB] at hrec
  exact hnelig (Option.some.inj hrec ▸ eligible_call4)

private theorem after_alice {stA stA' stB : PqParty} {sent sent' : List HwBytes}
    {c : CliCall} {out : HwBytes} {files : DirectorySnapshot}
    (hp : c.party = "alice")
    (hscr : scrub files = filesOf (encodeDir myParams stA'))
    (hsent : sent ++ (match 0, c.cmd with | 0, .send _ => (sentBody out).toList | _, _ => []) = sent') :
    (mkTurn stA stB sent).after r0 c 0 out files = mkTurn stA' stB sent' := by
  have hnm := not_preKeyNoMatch_alice (t := mkTurn stA stB sent) hp
  unfold CliTurn.after mkTurn
  simp only [CliTurn.mk.injEq]
  refine ⟨?_, hsent, ?_⟩
  · funext q
    by_cases hq : q = "alice" <;> simp [hp, hq, hscr]
  · simp only [Bool.false_or, decide_eq_false_iff_not]
    rintro ⟨_, h⟩; exact hnm h

private theorem after_bob {stA stB stB' : PqParty} {sent sent' : List HwBytes}
    {c : CliCall} {out : HwBytes} {files : DirectorySnapshot}
    (hp : c.party = "bob")
    (hnm : ¬ PreKeyNoMatch r0 (mkTurn stA stB sent) c)
    (hscr : scrub files = filesOf (encodeDir myParams stB'))
    (hsent : sent ++ (match 0, c.cmd with | 0, .send _ => (sentBody out).toList | _, _ => []) = sent') :
    (mkTurn stA stB sent).after r0 c 0 out files = mkTurn stA stB' sent' := by
  unfold CliTurn.after mkTurn
  simp only [CliTurn.mk.injEq]
  refine ⟨?_, hsent, ?_⟩
  · funext q
    by_cases hqa : q = "alice"
    · subst hqa; simp [hp, show ("alice" : String) ≠ "bob" by decide]
    · by_cases hqb : q = "bob" <;> simp [hp, hqa, hqb, hscr]
  · simp only [Bool.false_or, decide_eq_false_iff_not]
    rintro ⟨_, h⟩; exact hnm h

private theorem leaksFrom_evLeaks {stB : PqParty} {sent : List HwBytes} :
    LeaksFrom r0 (mkTurn stA4_cli stB sent) evLeaks := by
  have hrecA : (mkTurn stA4_cli stB sent).records r0 "alice" =
      some (recordBytes (sessionToRecordRec (pqSession x_A g_A4))) := by
    rw [records_some_of_session (st := stA4_cli) (by simp [mkTurn]) rfl (by decide)
          (by decide) (by decide) rfl (by decide),
        encodeRecordX_eq_recordBytes_of_wfPq wfPq_stA4 rfl rfl]
  intro e he
  simp only [evLeaks, leakEvCkr, leakEvCks, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · refine ⟨"alice", ckrBytes, Or.inr (Or.inr
      ⟨sessionToRecordRec (pqSession x_A g_A4), hrecA, ?_⟩), rfl⟩
    refine Or.inr (Or.inr (Or.inl ?_))
    refine ⟨((sessionToRecordRec (pqSession x_A g_A4)).current.receiverChains)[0],
      List.getElem_mem .., Or.inr (Or.inl ⟨(0, ckrBytes), ?_, rfl⟩)⟩
    decide +kernel
  · refine ⟨"alice", cksBytes, Or.inr (Or.inr
      ⟨sessionToRecordRec (pqSession x_A g_A4), hrecA, ?_⟩), rfl⟩
    refine Or.inr (Or.inl ?_)
    cases hs : (sessionToRecordRec (pqSession x_A g_A4)).current.senderChain with
    | none => exact absurd hs (by decide +kernel)
    | some sc =>
      refine ⟨sc, rfl, Or.inr ⟨(0, cksBytes), ?_, rfl⟩⟩
      have h : ((sessionToRecordRec (pqSession x_A g_A4)).current.senderChain).bind (·.chainKey) =
          some (0, cksBytes) := by decide +kernel
      rw [hs] at h; exact h

/-! ## Per-Command `CliTraces.step` Builders -/

private theorem step_call0 {X : UnreachedPqxdhPrimitives} {run : CliRun} (hSpec : CliSpecPqxdh run X myParams)
    {evs : List CliEvent}
    (hnext : CliTraces (runFnToRelation run) myInterp r0
      (mkTurn stA1_cli stB0_cli []) evs) :
    CliTraces (runFnToRelation run) myInterp r0
      (mkTurn stA0_cli stB0_cli []) (.run runEv0 :: evs) := by
  let i0 := pqInitInputs myParams stA0_cli bE_cli tapeInit
  have hi0 : i0 = pqInputs myParams stA0_cli call0.cmd call0.bundle call0.coins call0.stdin := by
    unfold i0 pqInitInputs
    have hcmd : call0.cmd = .init (partyAddress stA0_cli.party.other) bundleDir := rfl
    have ht : tapeInit.toList = tapeInitBytes := bytesToVec_toList_of_len (by decide)
    rw [hcmd, ht]; rfl
  have hval : ValidCall myInterp r0 (mkTurn stA0_cli stB0_cli []) call0 := by
    refine ⟨by decide, trivial, ?_, (fun h => nomatch h),
      rfl, rfl, rfl, rfl, records_alice_stA0,
      bundleFilesFlat_publicBundleOf bE_cli,
      honestBundleFiles_call0⟩
    simpa [mkTurn, call0] using filesBounded_of_wfPq wfPq_stA0
  have hinp : InputsFor call0 ((mkTurn stA0_cli stB0_cli []).dirs call0.party) i0 := by
    rw [hi0]; simpa [mkTurn, call0] using inputsFor_pqInputs wfPq_stA0
      (by dsimp only [encodeDir, stA0_cli, List.map, List.flatten]; decide)
      (regularFileList_bundle_files _)
      (fun f hf => ⟨by
        have hp : f.1 ∈ ((publicBundleOf bE_cli).files bundleDir).map Prod.fst :=
          List.mem_map_of_mem hf
        generalize f.1 = p at hp ⊢
        clear f hf
        cases hopk : bE_cli.opk <;>
          simp only [CryptoVerification.SignalSession.PublicBundle.files, publicBundleOf, hopk,
            Option.map, List.map_append, List.map_cons, List.map_nil] at hp <;>
          revert p hp <;> decide,
        (bundleFilesFlat_publicBundleOf bE_cli f hf).2⟩)
      (by dsimp only [call0]; decide +kernel)
  have hrun : runFnToRelation run i0
      (some (.exited 0 [] (filesOf (i0.files ++ encodeDir myParams stA1_cli)))) := by
    show run i0 = _
    rw [(hSpec stA0_cli wfPq_stA0).1 bE_cli tapeInit rfl, call0_model_X X]; rfl
  have hscr : scrub (filesOf (i0.files ++ encodeDir myParams stA1_cli)) =
      filesOf (encodeDir myParams stA1_cli) := by
    rw [hi0]
    exact scrub_filesOf_pqInputs_accept myParams stA0_cli stA1_cli call0.cmd call0.bundle
      call0.coins call0.stdin (regularFileList_bundle_files _) (isScrubbedPath_bundle_files _)
      (sub_of_fst_sub (by dsimp only [encodeDir, stA0_cli, stA1_cli, List.map, List.flatten]; decide))
  have haft := after_alice (stA := stA0_cli) (stA' := stA1_cli) (stB := stB0_cli)
    (sent := []) (sent' := []) (c := call0) (out := []) rfl hscr rfl
  exact CliTraces.step (leaks := []) (fun _ h => nomatch h) hval hinp hrun (haft.symm ▸ hnext)

private theorem step_send {X : UnreachedPqxdhPrimitives} {run : CliRun} (hSpec : CliSpecPqxdh run X myParams)
    {stA stB st st' stA' stB' : PqParty} {x : RecordExtras} {g : GhostState HwBytes}
    {sent : List HwBytes} {c : CliCall} {coinsVec : List.Vector (BitVec 8) 64} {out body : HwBytes}
    {leaks evs : List CliEvent}
    (hwf : PqxdhPartyInSpecDomain myParams st) (hsess : st.session = some (x, g))
    (hsig : st.signed.length ≤ 1) (hot : st.oneTime.length ≤ 1)
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort.length ≤ 1)
    (hp_or : c.party = r0.alice ∨ c.party = r0.bob)
    (hdir : (mkTurn stA stB sent).dirs c.party = filesOf (encodeDir myParams st))
    (hpe : partyAddress st.party.other = peerOf r0 c.party)
    (hpath : sessionPathOf r0 c.party = sessionFile (partyAddress st.party.other))
    (hcmd : c.cmd = .send (peerOf r0 c.party)) (hbun : c.bundle = [])
    (hcoins : coinsVec.toList = c.coins) (hco_len : c.coins.length = 64)
    (hin_len : c.stdin.length ≤ CryptoVerification.SignalSession.maxPlaintextBytes)
    (hsent_len : sent.length < 2 ^ 32 - 1)
    (hmod : CryptoVerification.SignalSession.pqSendModel myParams st c.stdin c.coins =
      some (some (st', out)))
    (hload_enc : ∀ p ∈ (encodeDir myParams st).map Prod.fst,
      (Arm64.hasLeadingSlash p || Arm64.hasDotDot p) = false)
    (hsub : ∀ p ∈ (encodeDir myParams st).map Prod.fst, p ∈ (encodeDir myParams st').map Prod.fst)
    (hafter : ∀ files, scrub files = filesOf (encodeDir myParams st') →
      (mkTurn stA stB sent).after r0 c 0 out files = mkTurn stA' stB' (sent ++ [body]))
    (hleaks : LeaksFrom r0 (mkTurn stA stB sent) leaks)
    (hnext : CliTraces (runFnToRelation run) myInterp r0
      (mkTurn stA' stB' (sent ++ [body])) evs) :
    CliTraces (runFnToRelation run) myInterp r0 (mkTurn stA stB sent)
      (leaks ++ .run (runEventOf c (some (0, out))) :: evs) := by
  let iS := pqSendInputs myParams st c.stdin coinsVec
  have hiS : iS = pqInputs myParams st c.cmd c.bundle c.coins c.stdin := by
    unfold iS pqSendInputs; rw [hpe, ← hcmd, hbun, hcoins]
  have hrec : (mkTurn stA stB sent).records r0 c.party ≠ none := by
    rw [records_some_of_session hdir hsess hpath hsig hot hkot hklr]; simp
  have hin_lt : c.stdin.length < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hin_len (by decide)
  have hval : ValidCall myInterp r0 (mkTurn stA stB sent) c := by
    refine ⟨by rw [hcmd]; exact hco_len, by unfold StdinBounded; rw [hcmd]; exact hin_lt,
      hdir ▸ filesBounded_of_wfPq hwf, (fun h => nomatch h), ?_⟩
    rw [hcmd]; exact ⟨hp_or, rfl, hbun, hsent_len, hrec⟩
  have hinp : InputsFor c ((mkTurn stA stB sent).dirs c.party) iS := by
    rw [hiS, hdir]
    exact inputsFor_pqInputs hwf hload_enc
      (by rw [hbun]; intro _ h; nomatch h) (by rw [hbun]; intro _ h; nomatch h) (by omega)
  have hrun : runFnToRelation run iS
      (some (.exited 0 out (filesOf (iS.files ++ encodeDir myParams st')))) := by
    have hsc : ¬ List.length c.stdin > CryptoVerification.SignalSession.stdinCapBytes :=
      Nat.not_lt.mpr (Nat.le_trans hin_len (by decide))
    have hmp : ¬ List.length c.stdin > CryptoVerification.SignalSession.maxPlaintextBytes :=
      Nat.not_lt.mpr hin_len
    show run iS = _; rw [(hSpec st hwf).2.1 c.stdin coinsVec hin_lt, ite_eq_right hsc, ite_eq_right hmp, hcoins, hmod]; rfl
  have hscr : scrub (filesOf (iS.files ++ encodeDir myParams st')) =
      filesOf (encodeDir myParams st') := by
    rw [hiS]
    exact scrub_filesOf_pqInputs_accept myParams st st' c.cmd c.bundle c.coins c.stdin
      (by rw [hbun]; intro _ h; nomatch h) (by rw [hbun]; intro _ h; nomatch h)
      (sub_of_fst_sub hsub)
  have haft := hafter _ hscr
  exact CliTraces.step hleaks hval hinp hrun (haft.symm ▸ hnext)

private theorem step_recv_prekey_bob {X : UnreachedPqxdhPrimitives} {run : CliRun} (hSpec : CliSpecPqxdh run X myParams)
    {stA stB stB' : PqParty} {sent : List HwBytes}
    {c : CliCall} {m : PreKeyMessageFields} {rc : BitVec 256} {pt : HwBytes}
    {evs : List CliEvent}
    (hwf : PqxdhPartyInSpecDomain myParams stB) (hpty : stB.party = Party.B)
    (hp : c.party = "bob") (hcmd : c.cmd = .recv (peerOf r0 "bob"))
    (hbun : c.bundle = []) (hstdin : c.stdin = wirePrekey :: m.bytes)
    (hcoins : CryptoGames.HMAC.keyToBytes32 rc = c.coins)
    (hco_len : c.coins.length = 32) (hsb_in : StdinBounded c)
    (hin_len : m.inner.length + 2048 < 2 ^ 32 ∧
      (wirePrekey :: m.bytes).length ≤ CryptoVerification.SignalSession.stdinCapBytes)
    (hmatch : ∀ x g, stB.session = some (x, g) → PqSessionMatches x g m)
    (hfrom : ∀ q, parsePreKeyWire c.stdin = some q → PqFromHonest sent q.message)
    (hmod : CryptoVerification.SignalSession.pqRecvPrekeyModel X myParams stB m rc =
      some (some (stB', pt)))
    (hnm : ¬ PreKeyNoMatch r0 (mkTurn stA stB sent) c)
    (hload_enc : ∀ p ∈ (encodeDir myParams stB).map Prod.fst,
      (Arm64.hasLeadingSlash p || Arm64.hasDotDot p) = false)
    (hsub : ∀ p ∈ (encodeDir myParams stB).map Prod.fst, p ∈ (encodeDir myParams stB').map Prod.fst)
    (hnext : CliTraces (runFnToRelation run) myInterp r0 (mkTurn stA stB' sent) evs) :
    CliTraces (runFnToRelation run) myInterp r0 (mkTurn stA stB sent)
      (.run (runEventOf c (some (0, pt))) :: evs) := by
  let iR := pqRecvInputs myParams stB (wirePrekey :: m.bytes) rc
  have hiR : iR = pqInputs myParams stB c.cmd c.bundle c.coins c.stdin := by
    unfold iR pqRecvInputs
    have hpe : partyAddress stB.party.other = peerOf r0 "bob" := by rw [hpty]; rfl
    rw [hpe, ← hcmd, hbun, hcoins, ← hstdin]
  have hne : ("bob" : String) ≠ "alice" := by decide
  have hval : ValidCall myInterp r0 (mkTurn stA stB sent) c := by
    refine ⟨by rw [hcmd]; exact hco_len, hsb_in,
      by simpa [mkTurn, hp, hne] using filesBounded_of_wfPq hwf, (fun h => nomatch h), ?_⟩
    rw [hcmd]
    refine ⟨Or.inr hp, by rw [hp], hbun, Or.inr ⟨hp, Or.inl ?_, hfrom⟩⟩
    rw [hstdin, List.head?_cons]; decide
  have hinp : InputsFor c ((mkTurn stA stB sent).dirs c.party) iR := by
    rw [hiR, hp]
    simp only [mkTurn, hne, ↓reduceIte]
    exact inputsFor_pqInputs hwf hload_enc
      (by rw [hbun]; intro _ h; nomatch h) (by rw [hbun]; intro _ h; nomatch h) (by omega)
  have hrun : runFnToRelation run iR
      (some (.exited 0 pt (filesOf (iR.files ++ encodeDir myParams stB')))) := by
    have hsc : ¬ (wirePrekey :: m.bytes).length > CryptoVerification.SignalSession.stdinCapBytes :=
      Nat.not_lt.mpr hin_len.2
    show run iR = _; rw [(hSpec stB hwf).2.2.2.1 m rc hin_len.1 hmatch, ite_eq_right hsc, hmod]; rfl
  have hscr : scrub (filesOf (iR.files ++ encodeDir myParams stB')) =
      filesOf (encodeDir myParams stB') := by
    rw [hiR]
    exact scrub_filesOf_pqInputs_accept myParams stB stB' c.cmd c.bundle c.coins c.stdin
      (by rw [hbun]; intro _ h; nomatch h) (by rw [hbun]; intro _ h; nomatch h)
      (sub_of_fst_sub hsub)
  have haft := after_bob (stA := stA) (stB := stB) (stB' := stB')
    (sent := sent) (sent' := sent) (c := c) (out := pt) hp hnm hscr (by simp [hcmd])
  exact CliTraces.step (leaks := []) (fun _ h => nomatch h) hval hinp hrun (haft.symm ▸ hnext)

private theorem step_recv_whisper {X : UnreachedPqxdhPrimitives} {run : CliRun} (hSpec : CliSpecPqxdh run X myParams)
    {stA stB st st' stA' stB' : PqParty} {x : RecordExtras} {g : GhostState HwBytes}
    {sent : List HwBytes} {c : CliCall} {body : HwBytes} {rc : BitVec 256} {pt : HwBytes}
    {evs : List CliEvent}
    (hwf : PqxdhPartyInSpecDomain myParams st) (hsess : st.session = some (x, g))
    (hsig : st.signed.length ≤ 1) (hot : st.oneTime.length ≤ 1)
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort.length ≤ 1)
    (hp_or : c.party = r0.alice ∨ c.party = r0.bob)
    (hdir : (mkTurn stA stB sent).dirs c.party = filesOf (encodeDir myParams st))
    (hpe : partyAddress st.party.other = peerOf r0 c.party)
    (hpath : sessionPathOf r0 c.party = sessionFile (partyAddress st.party.other))
    (hcmd : c.cmd = .recv (peerOf r0 c.party)) (hbun : c.bundle = [])
    (hstdin : c.stdin = wireWhisper :: body)
    (hcoins : CryptoGames.HMAC.keyToBytes32 rc = c.coins)
    (hco_len : c.coins.length = 32) (hsb_in : StdinBounded c)
    (hbody_len : (wireWhisper :: body).length ≤ CryptoVerification.SignalSession.stdinCapBytes)
    (hmem : body ∈ sent)
    (hmod : CryptoVerification.SignalSession.pqRecvWhisperModel myParams st body rc =
      some (some (st', pt)))
    (hload_enc : ∀ p ∈ (encodeDir myParams st).map Prod.fst,
      (Arm64.hasLeadingSlash p || Arm64.hasDotDot p) = false)
    (hsub : ∀ p ∈ (encodeDir myParams st).map Prod.fst, p ∈ (encodeDir myParams st').map Prod.fst)
    (hafter : ∀ files, scrub files = filesOf (encodeDir myParams st') →
      (mkTurn stA stB sent).after r0 c 0 pt files = mkTurn stA' stB' sent)
    (hnext : CliTraces (runFnToRelation run) myInterp r0 (mkTurn stA' stB' sent) evs) :
    CliTraces (runFnToRelation run) myInterp r0 (mkTurn stA stB sent)
      (.run (runEventOf c (some (0, pt))) :: evs) := by
  let iR := pqRecvInputs myParams st (wireWhisper :: body) rc
  have hiR : iR = pqInputs myParams st c.cmd c.bundle c.coins c.stdin := by
    unfold iR pqRecvInputs; rw [hpe, ← hcmd, hbun, hcoins, ← hstdin]
  have hrec : (mkTurn stA stB sent).records r0 c.party ≠ none := by
    rw [records_some_of_session hdir hsess hpath hsig hot hkot hklr]; simp
  have hval : ValidCall myInterp r0 (mkTurn stA stB sent) c := by
    refine ⟨by rw [hcmd]; exact hco_len, hsb_in,
      hdir ▸ filesBounded_of_wfPq hwf, (fun h => nomatch h), ?_⟩
    rw [hcmd]
    exact ⟨hp_or, rfl, hbun, Or.inl ⟨hrec, body, hstdin, pqFromHonest_of_mem hmem⟩⟩
  have hinp : InputsFor c ((mkTurn stA stB sent).dirs c.party) iR := by
    rw [hiR, hdir]
    exact inputsFor_pqInputs hwf hload_enc
      (by rw [hbun]; intro _ h; nomatch h) (by rw [hbun]; intro _ h; nomatch h) (by omega)
  have hrun : runFnToRelation run iR
      (some (.exited 0 pt (filesOf (iR.files ++ encodeDir myParams st')))) := by
    have hblt : body.length < 2 ^ 32 :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_succ _) hbody_len) (by decide)
    have hsc : ¬ (wireWhisper :: body).length > CryptoVerification.SignalSession.stdinCapBytes :=
      Nat.not_lt.mpr hbody_len
    show run iR = _; rw [(hSpec st hwf).2.2.1 body rc hblt, ite_eq_right hsc, hmod]; rfl
  have hscr : scrub (filesOf (iR.files ++ encodeDir myParams st')) =
      filesOf (encodeDir myParams st') := by
    rw [hiR]
    exact scrub_filesOf_pqInputs_accept myParams st st' c.cmd c.bundle c.coins c.stdin
      (by rw [hbun]; intro _ h; nomatch h) (by rw [hbun]; intro _ h; nomatch h)
      (sub_of_fst_sub hsub)
  have haft := hafter _ hscr
  exact CliTraces.step (leaks := []) (fun _ h => nomatch h) hval hinp hrun (haft.symm ▸ hnext)

/-! ## Assembled `CliTraces` Theorems for `evsHonest` and `evsExposed` -/

private theorem cliTraces_prefix06 (X : UnreachedPqxdhPrimitives) (run : CliRun) (hSpec : CliSpecPqxdh run X myParams)
    {evs : List CliEvent}
    (htail : CliTraces (runFnToRelation run) myInterp r0
      (mkTurn stA4_cli stB3_cli [pkMsg0.inner, pkMsg1.inner, bodyReply0]) evs) :
    CliTraces (runFnToRelation run) myInterp r0
      (CliTurn.init (initDirs myInterp r0)) (evsHonest ++ evs) := by
  have hne : ("bob" : String) ≠ "alice" := by decide
  rw [initTurn_eq]
  unfold evsHonest
  simp only [List.cons_append, List.nil_append]
  refine step_call0 hSpec ?_
  refine step_send hSpec wfPq_stA1 rfl (by decide) (by decide) rfl (by decide)
    (c := call1) (coinsVec := cSend0Vec) (body := pkMsg0.inner) (leaks := [])
    (Or.inl rfl) (by simp [mkTurn, call1]) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    call1_model
    (by dsimp only [encodeDir, stA1_cli, List.map, List.flatten]; decide)
    (by dsimp only [encodeDir, stA1_cli, stA2_cli, List.map, List.flatten]; decide)
    (fun _ hscr => after_alice rfl hscr (by simp [call1, sentBody_wire0]))
    (fun _ h => nomatch h) ?_
  refine step_send hSpec wfPq_stA2 rfl (by decide) (by decide) rfl (by decide)
    (c := call2) (coinsVec := cSend1Vec) (body := pkMsg1.inner) (leaks := [])
    (Or.inl rfl) (by simp [mkTurn, call2]) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    call2_model
    (by dsimp only [encodeDir, stA2_cli, List.map, List.flatten]; decide)
    (by dsimp only [encodeDir, stA2_cli, stA3_cli, List.map, List.flatten]; decide)
    (fun _ hscr => after_alice rfl hscr (by simp [call2, sentBody_wire1]))
    (fun _ h => nomatch h) ?_
  refine step_recv_prekey_bob hSpec wfPq_stB0 rfl
    (c := call3) rfl rfl rfl wire0_eq keyToBytes32_rc3 (by decide)
    (stdinBounded_recv_of_len rfl (by decide +kernel) (by decide +kernel)) (by decide +kernel)
    (fun _ _ hs => nomatch hs)
    (fun q hq => pqFromHonest_of_mem (by rw [parsePreKey_wire0_msg hq]; simp))
    (call3_model_X X) not_preKeyNoMatch_call3
    (by dsimp only [encodeDir, stB0_cli, List.map, List.flatten]; decide)
    (by dsimp only [encodeDir, stB0_cli, stB1_cli, List.map, List.flatten]; decide) ?_
  refine step_recv_prekey_bob hSpec wfPq_stB1 rfl
    (c := call4) rfl rfl rfl wire1_eq keyToBytes32_rc4 (by decide)
    (stdinBounded_recv_of_len rfl (by decide +kernel) (by decide +kernel)) (by decide +kernel)
    call4_sessionMatches
    (fun q hq => pqFromHonest_of_mem (by rw [parsePreKey_wire1_msg hq]; simp))
    (call4_model_X X) not_preKeyNoMatch_call4
    (by dsimp only [encodeDir, stB1_cli, List.map, List.flatten]; decide)
    (by dsimp only [encodeDir, stB1_cli, stB2_cli, List.map, List.flatten]; decide) ?_
  refine step_send hSpec wfPq_stB2 rfl (by decide) (by decide) rfl (by decide)
    (c := call5) (coinsVec := cSendReply0Vec) (body := bodyReply0) (leaks := [])
    (Or.inr rfl) (by simp [mkTurn, call5, hne]) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    call5_model
    (by dsimp only [encodeDir, stB2_cli, List.map, List.flatten]; decide)
    (by dsimp only [encodeDir, stB2_cli, stB3_cli, List.map, List.flatten]; decide)
    (fun _ hscr => after_bob rfl (by rintro ⟨_, ⟨_, h⟩, _⟩; cases h) hscr
      (by simp [call5, wireReply0_eq, sentBody_wireWhisper]))
    (fun _ h => nomatch h) ?_
  exact step_recv_whisper hSpec wfPq_stA3 rfl (by decide) (by decide) rfl (by decide)
    (c := call6) (Or.inl rfl) (by simp [mkTurn, call6]) rfl rfl rfl rfl wireReply0_eq
    keyToBytes32_rc6 (by decide) (stdinBounded_recv_of_len rfl (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp) call6_model
    (by dsimp only [encodeDir, stA3_cli, List.map, List.flatten]; decide)
    (by dsimp only [encodeDir, stA3_cli, stA4_cli, List.map, List.flatten]; decide)
    (fun _ hscr => after_alice rfl hscr rfl) htail

theorem cliTraces_honest (X : UnreachedPqxdhPrimitives) (run : CliRun) (hSpec : CliSpecPqxdh run X myParams) :
    CliTraces (runFnToRelation run) myInterp r0
      (CliTurn.init (initDirs myInterp r0)) evsHonest := by
  simpa using cliTraces_prefix06 X run hSpec (CliTraces.done _)

theorem cliTraces_exposed (X : UnreachedPqxdhPrimitives) (run : CliRun) (hSpec : CliSpecPqxdh run X myParams) :
    CliTraces (runFnToRelation run) myInterp r0
      (CliTurn.init (initDirs myInterp r0)) evsExposed := by
  have hne : ("bob" : String) ≠ "alice" := by decide
  change CliTraces (runFnToRelation run) myInterp r0
    (CliTurn.init (initDirs myInterp r0))
    (evsHonest ++ (evLeaks ++ .run runEv7 :: [.run runEv8]))
  refine cliTraces_prefix06 X run hSpec ?_
  refine step_send hSpec wfPq_stA4 rfl (by decide) (by decide) rfl (by decide)
    (c := call7) (coinsVec := cSend2Vec) (body := body2) (leaks := evLeaks)
    (Or.inl rfl) (by simp [mkTurn, call7]) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    call7_model
    (by dsimp only [encodeDir, stA4_cli, List.map, List.flatten]; decide)
    (by dsimp only [encodeDir, stA4_cli, stA5_cli, List.map, List.flatten]; decide)
    (fun _ hscr => after_alice rfl hscr (by simp [call7, wire2_eq, sentBody_wireWhisper]))
    leaksFrom_evLeaks ?_
  exact step_recv_whisper hSpec wfPq_stB3 rfl (by decide) (by decide) rfl (by decide)
    (c := call8) (Or.inr rfl) (by simp [mkTurn, call8, hne]) rfl rfl rfl rfl wire2_eq
    keyToBytes32_rc8 (by decide) (stdinBounded_recv_of_len rfl (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by simp) call8_model
    (by dsimp only [encodeDir, stB3_cli, List.map, List.flatten]; decide)
    (by dsimp only [encodeDir, stB3_cli, stB4_cli, List.map, List.flatten]; decide)
    (fun _ hscr => after_bob rfl (not_preKeyNoMatch_whisper wire2_eq) hscr rfl)
    (CliTraces.done _)

theorem evsHonest_all_exit0 : ∀ ev : RunEvent, .run ev ∈ evsHonest → ∃ out, ev.exit = some (0, out) := by
  intro ev h
  simp only [evsHonest, List.mem_cons, List.not_mem_nil, or_false, CliEvent.run.injEq] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem evsExposed_all_exit0 : ∀ ev : RunEvent, .run ev ∈ evsExposed → ∃ out, ev.exit = some (0, out) := by
  intro ev h
  simp only [evsExposed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or,
    CliEvent.run.injEq, reduceCtorEq] at h
  rcases h with h | rfl | rfl
  · exact evsHonest_all_exit0 ev h
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem invertsGuarded_honest : InvertsGuarded myInterp r0 evsHonest :=
  invertsGuarded_of_noInverts rfl

theorem invertsGuarded_exposed : InvertsGuarded myInterp r0 evsExposed :=
  invertsGuarded_of_noInverts rfl

theorem coinsFresh_honest : CoinsFresh r0 evsHonest := by
  unfold CoinsFresh DY.Libsignal.Composed.Refinement.Cli.setupDHSecrets
    DY.Libsignal.Composed.Refinement.secretBytes
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq _ (by decide +kernel)]
  decide +kernel

theorem coinsFresh_exposed : CoinsFresh r0 evsExposed := by
  unfold CoinsFresh DY.Libsignal.Composed.Refinement.Cli.setupDHSecrets
    DY.Libsignal.Composed.Refinement.secretBytes
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq _ (by decide +kernel)]
  decide +kernel

end Symbolic.Proofs.Tests.CliNonvacuity.SessionTraces
