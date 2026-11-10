/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel
import all Init.Data.Repr
import all Init.Data.String.Defs
import Symbolic.Proofs.Swarm.CREF.Cli.DirCodecBridge

/-!
# Concrete 3-Call CLI Trace (`CliTraces`) for Handshake Non-Vacuity

Constructs the concrete 3-event `CliTraces` derivation (`cliTraces_handshake`) from `initDirs`
for the 3-call CLI execution (`init` on Alice, `send` on Alice, `recv` on Bob) against `CliSpecPqxdh`
for every `X : UnreachedPqxdhPrimitives` and both `withOpk = false` and `withOpk = true`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCliTraces

set_option maxRecDepth 200000

open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ecKey secretBytes setupPublic parsePreKeyWire preKeyWire sentBody)
open DY.Libsignal.Composed.Refinement.Cli
  (CliCall CliTurn initDirs commonFiles bobPreKeyFiles peerOf sessionPathOf
   bundleBlob ValidCall StdinBounded BobCallAllowed InputsFor PreKeyNoMatch
   runInput runEventOf CliTraces runFnToRelation scrub SamePath
   HonestBundleDir)
open Arm64 (normalizePath)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives initiateTapeLen wirePrekey encodeRecordUnderExtras)
open CryptoVerification.SignalSession
  (CliRun CliSpecPqxdh PqSessionMatches publicBundleOf
   pqInputs pqInitInputs pqSendInputs pqRecvInputs pqxdhExpectedOutcome pqSendModel
   filesOf encodeDir stdioPaths sessionFile partyAddress
   coinsFile bundleDir partyDirs)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myParams myInterp myHooks_agree pt0 myKyberSecField mkRecords mkRecords_wf mkRecords_opaqueBytes_6)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel
  (tapeInitBytes tapeInit cSend0 cSend0Vec rcBytes rcVal keyToBytes32_rcVal
   idPubA_vec spkPubB_vec opkPubB_vec myKyberPub1568 myKyberSec3168
   stA0_cli stB0_cli bE_cli bytesToVec_toList_of_len
   mkRecords_opaque5 mkRecords_opaque7 pubBytes_idA pubBytes_spkB pubBytes_opkB
   x_A g_A1 stA1_cli stA2_cli pkMsg0 wire0 stB1_cli wire0_eq
   initStep_eq_any sendStep_eq recvStep_eq_any
   wfPq_stA0 wfPq_stB0 wfPq_stA1)
open Symbolic.Proofs.Tests.Refinement.Cli
  (CliFilePath cliEvalAt cliStepAt cliFilesOf_eq_evalAt cliEvalAt_idle filesOf_append_or
   filesBounded_of_cliFilePaths bundleFiles_cliFilePath extra_cliFilePath
   inputsFor_of_cliFilePaths initDirs_alice_no_session
   pqFromHonest_of_mem honestBundleDir_to_flat_and_honest)
open Symbolic.Swarm.CREF.Cli (bundleTyped_iff_exists_bundleE)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

def call0 (withOpk : Bool) : CliCall where
  party := "alice"
  cmd := .init (peerOf (mkRecords withOpk) "alice") bundleDir
  bundle := (publicBundleOf (bE_cli withOpk)).files bundleDir
  stdin := []
  coins := tapeInitBytes withOpk

def call1 (withOpk : Bool) : CliCall where
  party := "alice"
  cmd := .send (peerOf (mkRecords withOpk) "alice")
  bundle := []
  stdin := pt0
  coins := cSend0

def call2 (withOpk : Bool) : CliCall where
  party := "bob"
  cmd := .recv (peerOf (mkRecords withOpk) "bob")
  bundle := []
  stdin := wire0 withOpk
  coins := rcBytes withOpk

def ev0 (withOpk : Bool) : RunEvent := runEventOf (call0 withOpk) (some (0, []))
def ev1 (withOpk : Bool) : RunEvent := runEventOf (call1 withOpk) (some (0, wire0 withOpk))
def ev2 (withOpk : Bool) : RunEvent := runEventOf (call2 withOpk) (some (0, pt0))

def evsOf (withOpk : Bool) : List CliEvent :=
  [.run (ev0 withOpk), .run (ev1 withOpk), .run (ev2 withOpk)]

theorem call0_runInput (withOpk : Bool) :
    runInput (call0 withOpk) = bundleBlob (publicBundleOf (bE_cli withOpk)) := by
  cases withOpk <;> decide +kernel

private theorem tapeInit_toList (withOpk : Bool) :
    (tapeInit withOpk).toList = tapeInitBytes withOpk := by
  unfold tapeInit
  cases withOpk
  · exact bytesToVec_toList_of_len (n := initiateTapeLen) (bs := tapeInitBytes false) (by decide)
  · exact bytesToVec_toList_of_len (n := initiateTapeLen) (bs := tapeInitBytes true) (by decide)

private theorem mkRecords_secretBytes_eq (withOpk : Bool) (k : Nat) :
    secretBytes (mkRecords withOpk) k =
      ((([(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] ++
        if (mkRecords withOpk).withOpk then [(22, 32)] else [])[k]?).map fun p =>
          (mkRecords withOpk).fresh p.1 p.2).getD [] := by
  unfold secretBytes
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq (mkRecords withOpk) (mkRecords_wf withOpk).1]

private theorem mkRecords_sec0 (withOpk : Bool) :
    secretBytes (mkRecords withOpk) 0 = List.replicate 32 1#8 := by
  rw [mkRecords_secretBytes_eq]; cases withOpk <;> rfl

private theorem mkRecords_sec1 (withOpk : Bool) :
    secretBytes (mkRecords withOpk) 1 = List.replicate 32 6#8 := by
  rw [mkRecords_secretBytes_eq]; cases withOpk <;> rfl

private theorem mkRecords_sec2 (withOpk : Bool) :
    secretBytes (mkRecords withOpk) 2 = List.replicate 32 11#8 := by
  rw [mkRecords_secretBytes_eq]; cases withOpk <;> rfl

private theorem mkRecords_sec6 :
    secretBytes (mkRecords true) 6 = List.replicate 32 23#8 := by
  rw [mkRecords_secretBytes_eq]; rfl

theorem honestBundleDir_bE_cli (withOpk : Bool) :
    HonestBundleDir myInterp (mkRecords withOpk) (publicBundleOf (bE_cli withOpk)) := by
  refine ⟨(bundleTyped_iff_exists_bundleE _).mpr ⟨bE_cli withOpk, rfl⟩, fun _ => ?_⟩
  dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecBytes,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]
  rw [mkRecords_sec1, mkRecords_sec2, mkRecords_opaque5, mkRecords_opaqueBytes_6, mkRecords_opaque7]
  cases withOpk <;>
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel⟩

private theorem encodeDir_stA0_cliFilePath (withOpk : Bool) :
    ∀ x ∈ encodeDir myParams (stA0_cli withOpk), CliFilePath x.1 := by
  intro x hx
  have hall : ((encodeDir myParams (stA0_cli withOpk)).all fun x => decide (CliFilePath x.1)) = true := by
    cases withOpk <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

private theorem encodeDir_stA1_cliFilePath (withOpk : Bool) :
    ∀ x ∈ encodeDir myParams (stA1_cli withOpk), CliFilePath x.1 := by
  intro x hx
  have hall : ((encodeDir myParams (stA1_cli withOpk)).all fun x => decide (CliFilePath x.1)) = true := by
    cases withOpk <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

private theorem encodeDir_stB0_cliFilePath (withOpk : Bool) :
    ∀ x ∈ encodeDir myParams (stB0_cli withOpk), CliFilePath x.1 := by
  intro x hx
  have hall : ((encodeDir myParams (stB0_cli withOpk)).all fun x => decide (CliFilePath x.1)) = true := by
    cases withOpk <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

theorem commonFiles_alice_eq_encodeDir (withOpk : Bool) :
    commonFiles myInterp (mkRecords withOpk) "alice" =
      encodeDir myParams (stA0_cli withOpk) := by
  have ha : ("alice" : String) = (mkRecords withOpk).alice := by cases withOpk <;> rfl
  unfold commonFiles DY.Libsignal.Composed.Refinement.Cli.idSecret
    DY.Libsignal.Composed.Refinement.Cli.peerIdSecret
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes
  simp only [ha, ↓reduceIte, mkRecords_sec0, mkRecords_sec1]
  cases withOpk <;> decide +kernel

private def commonFilesBobClosed (withOpk : Bool) : List (String × HwBytes) :=
  [(CryptoVerification.SignalSession.addressFile,
      DY.Libsignal.Composed.Refinement.Cli.textBytes
        (DY.Libsignal.Composed.Refinement.Cli.addrOf (mkRecords withOpk) "bob").text),
   (CryptoVerification.SignalSession.identityKeyPairFile,
     CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
       ⟨ecKey (DY.Libsignal.Composed.Refinement.pubBytes myInterp (List.replicate 32 6#8)),
        List.replicate 32 6#8⟩),
   (CryptoVerification.SignalSession.registrationIdFile,
     CryptoVerification.SignalSession.le32
       (DY.Libsignal.Composed.Refinement.Cli.regIdOf (mkRecords withOpk) "bob")),
   (CryptoVerification.SignalSession.identityFile
      (DY.Libsignal.Composed.Refinement.Cli.peerNameOf (mkRecords withOpk) "bob"),
     ecKey (DY.Libsignal.Composed.Refinement.pubBytes myInterp (List.replicate 32 1#8)))]

private theorem commonFiles_bob_eq_closed (withOpk : Bool) :
    commonFiles myInterp (mkRecords withOpk) "bob" = commonFilesBobClosed withOpk := by
  have hne : ("bob" : String) ≠ (mkRecords withOpk).alice := by
    cases withOpk <;> (show "bob" ≠ "alice"; decide)
  unfold commonFiles commonFilesBobClosed
    DY.Libsignal.Composed.Refinement.Cli.idSecret
    DY.Libsignal.Composed.Refinement.Cli.peerIdSecret
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes
  simp only [hne, ↓reduceIte, mkRecords_sec0, mkRecords_sec1]

theorem initDirs_alice_eq (withOpk : Bool) :
    initDirs myInterp (mkRecords withOpk) "alice" =
      filesOf (encodeDir myParams (stA0_cli withOpk)) := by
  have ha : ("alice" : String) = (mkRecords withOpk).alice := by cases withOpk <;> rfl
  simp only [initDirs, ha, ↓reduceIte]
  rw [← ha, commonFiles_alice_eq_encodeDir]

theorem initDirs_bob_eq (withOpk : Bool) :
    initDirs myInterp (mkRecords withOpk) "bob" =
      filesOf (encodeDir myParams (stB0_cli withOpk)) := by
  have hne : ("bob" : String) ≠ (mkRecords withOpk).alice := by
    cases withOpk <;> (show "bob" ≠ "alice"; decide)
  have hb : (("bob" : String) = (mkRecords withOpk).bob) = True :=
    eq_true (by cases withOpk <;> rfl)
  unfold initDirs bobPreKeyFiles
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecBytes
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.opkSecBytes
  simp only [hne, hb, ↓reduceIte]
  rw [commonFiles_bob_eq_closed, mkRecords_sec2,
      mkRecords_opaque5, mkRecords_opaqueBytes_6, mkRecords_opaque7]
  cases withOpk
  · simp only [show (mkRecords false).withOpk = false from rfl, Bool.false_eq_true, ↓reduceIte]
    congr 1
  · rw [mkRecords_sec6]
    let l1 := commonFilesBobClosed true ++
      ([("signed-pre-keys/" ++ toString (mkRecords true).spkId.toNat,
          CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
            ⟨(mkRecords true).spkId,
             ecKey (DY.Libsignal.Composed.Refinement.pubBytes myInterp (List.replicate 32 11#8)),
             List.replicate 32 11#8, List.replicate 64 0#8, 0⟩),
        ("last-resort-kyber-pre-keys/" ++ toString (mkRecords true).kpkId.toNat,
          CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
            ⟨(mkRecords true).kpkId,
             DY.Libsignal.Composed.Refinement.kyberKey Witness.myKyberPubBytes,
             DY.Libsignal.Composed.Refinement.kyberKey ((mkRecords true).kyberSecB.drop 1),
             List.replicate 64 0#8, 0⟩),
        ("last-resort-kyber-pre-keys/" ++ toString (mkRecords true).kpkId.toNat ++ ".base-keys", [])] ++
       if (mkRecords true).withOpk then
         [("one-time-pre-keys/" ++ toString (mkRecords true).opkId.toNat,
            CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode
              ⟨(mkRecords true).opkId,
               ecKey (DY.Libsignal.Composed.Refinement.pubBytes myInterp (List.replicate 32 23#8)),
               List.replicate 32 23#8⟩)]
       else [])
    let l2 := encodeDir myParams (stB0_cli true)
    change filesOf l1 = filesOf l2
    have hc1 : ∀ x ∈ l1, CliFilePath x.1 := fun x hx =>
      of_decide_eq_true (List.all_eq_true.mp (by decide +kernel :
        (l1.all fun x => decide (CliFilePath x.1)) = true) x hx)
    have hc2 := encodeDir_stB0_cliFilePath true
    funext p
    rw [cliFilesOf_eq_evalAt hc1, cliFilesOf_eq_evalAt hc2]
    split
    · rfl
    · split
      · rfl
      · let ks := l2.map fun x => normalizePath x.1
        by_cases hmem : normalizePath p ∈ ks
        · exact eq_of_beq (List.all_eq_true.mp (by decide +kernel :
            (ks.all fun fp => cliEvalAt fp none l1 == cliEvalAt fp none l2) = true) _ hmem)
        · have hsub : ∀ x ∈ l1, normalizePath x.1 ∈ ks := fun x hx =>
            of_decide_eq_true (List.all_eq_true.mp (by decide +kernel :
              (l1.all fun x => decide (normalizePath x.1 ∈ ks)) = true) x hx)
          rw [cliEvalAt_idle (fun x hx h => hmem (by rw [← h]; exact hsub x hx)),
              cliEvalAt_idle (fun x hx h => hmem (by rw [← h]; exact List.mem_map_of_mem hx))]

private theorem scrub_after_init_eq (withOpk : Bool) :
    scrub (filesOf ((pqInitInputs myParams (stA0_cli withOpk) (bE_cli withOpk)
        (tapeInit withOpk)).files ++ encodeDir myParams (stA1_cli withOpk))) =
      filesOf (encodeDir myParams (stA1_cli withOpk)) := by
  let base0 := encodeDir myParams (stA0_cli withOpk)
  let ext0 := (call0 withOpk).extra
  let next1 := encodeDir myParams (stA1_cli withOpk)
  have hfiles : (pqInitInputs myParams (stA0_cli withOpk) (bE_cli withOpk)
      (tapeInit withOpk)).files = base0 ++ ext0 := by
    unfold pqInitInputs pqInputs
    rw [tapeInit_toList]
    cases withOpk <;> simp [base0, ext0, call0, CliCall.extra, List.append_assoc]
  rw [hfiles]
  have hb0 := encodeDir_stA0_cliFilePath withOpk
  have he0 : ∀ x ∈ ext0, CliFilePath x.1 :=
    extra_cliFilePath (call0 withOpk) (bundleFiles_cliFilePath _)
  have hn1 := encodeDir_stA1_cliFilePath withOpk
  have hall0 : ∀ x ∈ base0 ++ ext0, CliFilePath x.1 := fun x hx =>
    (List.mem_append.mp hx).elim (hb0 x) (he0 x)
  have hcoins : normalizePath coinsFile = [coinsFile] := by decide
  have hno1 : ∀ x ∈ next1, normalizePath x.1 ≠ [coinsFile] ∧
      (normalizePath x.1).head? ≠ some bundleDir := by
    intro x hx
    have hall : (next1.all fun x =>
        decide (normalizePath x.1 ≠ [coinsFile] ∧ (normalizePath x.1).head? ≠ some bundleDir)) = true := by
      cases withOpk <;> decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
  have honly0 : ∀ x ∈ ext0, normalizePath x.1 = [coinsFile] ∨
      (normalizePath x.1).head? = some bundleDir := by
    intro x hx
    have hall : (ext0.all fun x =>
        decide (normalizePath x.1 = [coinsFile] ∨ (normalizePath x.1).head? = some bundleDir)) = true := by
      cases withOpk <;> decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
  have hover : ∀ p, (filesOf next1 p).or (filesOf base0 p) = filesOf next1 p := by
    intro p
    rw [cliFilesOf_eq_evalAt hn1, cliFilesOf_eq_evalAt hb0]
    split
    · rfl
    · split
      · rfl
      · let ks := next1.map fun x => normalizePath x.1
        by_cases hmem : normalizePath p ∈ ks
        · have hall : (ks.all fun fp =>
              (cliEvalAt fp none next1).or (cliEvalAt fp none base0) ==
                cliEvalAt fp none next1) = true := by
            cases withOpk <;> decide +kernel
          exact eq_of_beq (List.all_eq_true.mp hall _ hmem)
        · have hb_sub : ∀ x ∈ base0, normalizePath x.1 ∈ ks := by
            intro x hx
            have hall : (base0.all fun x => decide (normalizePath x.1 ∈ ks)) = true := by
              cases withOpk <;> decide +kernel
            exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
          rw [cliEvalAt_idle (fun x hx h => hmem (by rw [← h]; exact List.mem_map_of_mem hx)),
              cliEvalAt_idle (fun x hx h => hmem (by rw [← h]; exact hb_sub x hx))]
          rfl
  funext p
  unfold scrub
  by_cases hcond : (SamePath p coinsFile || (normalizePath p).head? == some bundleDir) = true
  · simp only [hcond, ↓reduceIte]
    symm
    rw [cliFilesOf_eq_evalAt hn1]
    split
    · rfl
    · split
      · rfl
      · apply cliEvalAt_idle
        intro x hx heq
        simp only [Bool.or_eq_true, SamePath, beq_iff_eq, hcoins] at hcond
        rcases hcond with hp1 | hp2
        · exact (hno1 x hx).1 (heq.trans hp1)
        · exact (hno1 x hx).2 (heq ▸ hp2)
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    rw [filesOf_append_or hall0 hn1 p, filesOf_append_or hb0 he0 p]
    have hex_none : filesOf ext0 p = none := by
      rw [cliFilesOf_eq_evalAt he0]
      split
      · rfl
      · split
        · rfl
        · apply cliEvalAt_idle
          intro x hx heq
          simp only [Bool.or_eq_false_iff, SamePath, beq_eq_false_iff_ne, hcoins] at hcond
          rcases honly0 x hx with hx1 | hx2
          · exact hcond.1 (heq.symm.trans hx1)
          · exact hcond.2 (heq ▸ hx2)
    rw [hex_none, Option.none_or]
    exact hover p

set_option maxRecDepth 400000 in
private theorem stA1_records_ne_none (withOpk : Bool) (t : CliTurn)
    (ht : t.dirs "alice" = filesOf (encodeDir myParams (stA1_cli withOpk))) :
    t.records (mkRecords withOpk) "alice" ≠ none := by
  have hn1 := encodeDir_stA1_cliFilePath withOpk
  have heval : filesOf (encodeDir myParams (stA1_cli withOpk))
      (sessionPathOf (mkRecords withOpk) "alice") =
      some (encodeRecordUnderExtras (fun _ => x_A withOpk) (g_A1 withOpk)) := by
    rw [cliFilesOf_eq_evalAt hn1]
    have hstd : normalizePath (sessionPathOf (mkRecords withOpk) "alice") ∉
        stdioPaths.map normalizePath := by
      cases withOpk <;> decide
    have hemp : (normalizePath (sessionPathOf (mkRecords withOpk) "alice")).isEmpty = false := by
      cases withOpk <;> decide
    simp only [hstd, hemp, ↓reduceIte, Bool.false_eq_true]
    cases withOpk <;> decide +kernel
  have hne : encodeRecordUnderExtras (fun _ => x_A withOpk) (g_A1 withOpk) ≠ [] := by
    cases withOpk <;> decide +kernel
  unfold CliTurn.records
  rw [ht, heval]
  simp [hne]

private theorem parsePreKeyWire_wire0_msg_len (withOpk : Bool) :
    ∀ q, parsePreKeyWire (wire0 withOpk) = some q → q.message.length + 2048 < 2 ^ 32 := by
  intro q hq
  have hm : (parsePreKeyWire (wire0 withOpk)).map (fun x => x.message.length) = some 143 := by
    cases withOpk <;> decide +kernel
  rw [hq] at hm
  dsimp only [Option.map] at hm
  injection hm with hlen
  omega

private theorem msg_len_le_preKeyWire (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32)
    (ik ek ct msg : HwBytes) :
    msg.length ≤ (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length := by
  unfold preKeyWire
    DY.Libsignal.PQXDH.Refinement.PreKeyProto.encode
    CryptoVerification.LibsignalProtoCodec.encodeBytesField
  simp only [List.length_cons, List.length_append]
  omega

theorem cliTraces_handshake (withOpk : Bool) (X : UnreachedPqxdhPrimitives) (run : CliRun)
    (hSpec : CliSpecPqxdh run X myParams) :
    CliTraces (runFnToRelation run) myInterp (mkRecords withOpk)
      (CliTurn.init (initDirs myInterp (mkRecords withOpk)))
      (evsOf withOpk) := by
  let r := mkRecords withOpk
  let t0 := CliTurn.init (initDirs myInterp r)
  let inp0 := pqInitInputs myParams (stA0_cli withOpk) (bE_cli withOpk) (tapeInit withOpk)
  have hdirs0 : t0.dirs "alice" = filesOf (encodeDir myParams (stA0_cli withOpk)) :=
    initDirs_alice_eq withOpk
  have hinp0 : InputsFor (call0 withOpk) (t0.dirs (call0 withOpk).party) inp0 := by
    change InputsFor (call0 withOpk) (t0.dirs "alice") inp0
    rw [hdirs0]
    have hpeq : inp0 =
        { argv := (call0 withOpk).cmd.argv
          dirs := partyDirs ++ [bundleDir]
          files := encodeDir myParams (stA0_cli withOpk) ++ (call0 withOpk).extra
          stdin := (call0 withOpk).stdin } := by
      unfold inp0 pqInitInputs pqInputs
      rw [tapeInit_toList]
      cases withOpk <;> rfl
    rw [hpeq]
    exact inputsFor_of_cliFilePaths (call0 withOpk) _
      (encodeDir_stA0_cliFilePath withOpk) (bundleFiles_cliFilePath _)
      (fun f hf => ((wfPq_stA0 withOpk).2.1 f hf).1)
      (fun x hx => ((honestBundleDir_to_flat_and_honest (honestBundleDir_bE_cli withOpk)).1 x hx).2)
      (by cases withOpk <;> decide +kernel)
  have hval0 : ValidCall myInterp r t0 (call0 withOpk) := by
    dsimp only [ValidCall, StdinBounded, BobCallAllowed, call0]
    refine ⟨by cases withOpk <;> decide, trivial, ?_, (fun h => nomatch h),
      by cases withOpk <;> rfl, by cases withOpk <;> rfl, rfl, rfl,
      initDirs_alice_no_session myInterp r,
      honestBundleDir_to_flat_and_honest (honestBundleDir_bE_cli withOpk)⟩
    rw [hdirs0]
    exact filesBounded_of_cliFilePaths (encodeDir_stA0_cliFilePath withOpk)
      (fun f hf => ((wfPq_stA0 withOpk).2.1 f hf).1)
  have hrun0 : runFnToRelation run inp0
      (some (.exited 0 [] (filesOf (inp0.files ++ encodeDir myParams (stA1_cli withOpk))))) := by
    unfold runFnToRelation
    rw [(hSpec (stA0_cli withOpk) (wfPq_stA0 withOpk)).1 (bE_cli withOpk) (tapeInit withOpk) rfl,
      initStep_eq_any X withOpk]
    rfl
  let files0 := filesOf (inp0.files ++ encodeDir myParams (stA1_cli withOpk))
  let t1 := t0.after r (call0 withOpk) 0 [] files0
  have ht1_alice : t1.dirs "alice" = filesOf (encodeDir myParams (stA1_cli withOpk)) := by
    simp only [t1, CliTurn.after, call0, ↓reduceIte]
    exact scrub_after_init_eq withOpk
  have ht1_bob : t1.dirs "bob" = filesOf (encodeDir myParams (stB0_cli withOpk)) := by
    have hne : ("bob" : String) ≠ "alice" := by decide
    simp only [t1, CliTurn.after, call0, hne, ↓reduceIte]
    exact initDirs_bob_eq withOpk
  have ht1_bobOff : t1.bobOff = false := by
    have hnp : ¬ PreKeyNoMatch r t0 (call0 withOpk) := by
      rintro ⟨hp, _⟩
      have hrb : r.bob = "bob" := by cases withOpk <;> rfl
      have hcp : (call0 withOpk).party = "alice" := rfl
      rw [hcp, hrb] at hp
      exact absurd hp (by decide)
    have h0 : t0.bobOff = false := rfl
    dsimp only [t1, CliTurn.after]
    rw [h0]
    simp [hnp]
  let inp1 := pqSendInputs myParams (stA1_cli withOpk) pt0 cSend0Vec
  have hinp1 : InputsFor (call1 withOpk) (t1.dirs (call1 withOpk).party) inp1 := by
    change InputsFor (call1 withOpk) (t1.dirs "alice") inp1
    rw [ht1_alice]
    have hpeq : inp1 =
        { argv := (call1 withOpk).cmd.argv
          dirs := partyDirs
          files := encodeDir myParams (stA1_cli withOpk) ++ (call1 withOpk).extra
          stdin := (call1 withOpk).stdin } := by
      cases withOpk <;> rfl
    rw [hpeq]
    exact inputsFor_of_cliFilePaths (call1 withOpk) _
      (encodeDir_stA1_cliFilePath withOpk) (fun _ h => nomatch h)
      (fun f hf => ((wfPq_stA1 withOpk).2.1 f hf).1) (fun _ h => nomatch h) (by cases withOpk <;> decide +kernel)
  have ht1_sent : t1.sent = [] := by
    dsimp only [t1, CliTurn.after, t0, CliTurn.init, call0]
    rfl
  have hval1 : ValidCall myInterp r t1 (call1 withOpk) := by
    dsimp only [ValidCall, StdinBounded, BobCallAllowed, call1]
    refine ⟨by cases withOpk <;> decide, by decide, ?_,
      (by rw [ht1_bobOff]; intro h; cases h),
      Or.inl (by cases withOpk <;> rfl), rfl, rfl,
      (by rw [ht1_sent]; decide),
      stA1_records_ne_none withOpk t1 ht1_alice⟩
    rw [ht1_alice]
    exact filesBounded_of_cliFilePaths (encodeDir_stA1_cliFilePath withOpk)
      (fun f hf => ((wfPq_stA1 withOpk).2.1 f hf).1)
  have hrun1 : runFnToRelation run inp1
      (some (.exited 0 (wire0 withOpk)
        (filesOf (inp1.files ++ encodeDir myParams (stA2_cli withOpk))))) := by
    unfold runFnToRelation
    rw [(hSpec (stA1_cli withOpk) (wfPq_stA1 withOpk)).2.1 pt0 cSend0Vec (by decide)]
    change some (pqxdhExpectedOutcome myParams inp1 (pqSendModel myParams (stA1_cli withOpk) pt0 cSend0)) = _
    rw [sendStep_eq withOpk]
    rfl
  let files1 := filesOf (inp1.files ++ encodeDir myParams (stA2_cli withOpk))
  let t2 := t1.after r (call1 withOpk) 0 (wire0 withOpk) files1
  have ht2_bob : t2.dirs "bob" = filesOf (encodeDir myParams (stB0_cli withOpk)) := by
    have hne : ("bob" : String) ≠ "alice" := by decide
    simp only [t2, CliTurn.after, call1, hne, ↓reduceIte]
    exact ht1_bob
  have ht2_bobOff : t2.bobOff = false := by
    have hnp : ¬ PreKeyNoMatch r t1 (call1 withOpk) := by
      rintro ⟨hp, _⟩
      have hrb : r.bob = "bob" := by cases withOpk <;> rfl
      have hcp : (call1 withOpk).party = "alice" := rfl
      rw [hcp, hrb] at hp
      exact absurd hp (by decide)
    dsimp only [t2, CliTurn.after]
    rw [ht1_bobOff]
    simp [hnp]
  let inp2 := pqRecvInputs myParams (stB0_cli withOpk) (wire0 withOpk) (rcVal withOpk)
  have hinp2 : InputsFor (call2 withOpk) (t2.dirs (call2 withOpk).party) inp2 := by
    change InputsFor (call2 withOpk) (t2.dirs "bob") inp2
    rw [ht2_bob]
    have hpeq : inp2 =
        { argv := (call2 withOpk).cmd.argv
          dirs := partyDirs
          files := encodeDir myParams (stB0_cli withOpk) ++ (call2 withOpk).extra
          stdin := (call2 withOpk).stdin } := by
      unfold inp2 pqRecvInputs pqInputs
      rw [keyToBytes32_rcVal]
      cases withOpk <;> rfl
    rw [hpeq]
    exact inputsFor_of_cliFilePaths (call2 withOpk) _
      (encodeDir_stB0_cliFilePath withOpk) (fun _ h => nomatch h)
      (fun f hf => ((wfPq_stB0 withOpk).2.1 f hf).1) (fun _ h => nomatch h) (by cases withOpk <;> decide +kernel)
  have hval2 : ValidCall myInterp r t2 (call2 withOpk) := by
    have hsb2 : StdinBounded (call2 withOpk) := by
      have hwlen : (wire0 withOpk).length + 2048 < 2 ^ 32 := by
        cases withOpk <;> decide +kernel
      dsimp only [StdinBounded, call2]
      refine ⟨?_, fun _ => by omega, parsePreKeyWire_wire0_msg_len withOpk,
        fun preKeyId spkId kpkId regId ik ek ct msg _ _ _ hst => ?_⟩
      · intro body h
        rw [wire0_eq] at h
        injection h with htag _
        exact absurd htag (by decide)
      · have hle := msg_len_le_preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg
        rw [← hst] at hle
        omega
    dsimp only [ValidCall, BobCallAllowed, call2]
    refine ⟨by cases withOpk <;> decide +kernel, hsb2, ?_,
      (by rw [ht2_bobOff]; intro h; cases h),
      Or.inr (by cases withOpk <;> rfl), rfl, rfl, Or.inr ⟨by cases withOpk <;> rfl,
      Or.inl (by cases withOpk <;> decide +kernel), fun q hq => ?_⟩⟩
    · rw [ht2_bob]
      exact filesBounded_of_cliFilePaths (encodeDir_stB0_cliFilePath withOpk)
        (fun f hf => ((wfPq_stB0 withOpk).2.1 f hf).1)
    · apply pqFromHonest_of_mem
      have hsent : t2.sent = (sentBody (wire0 withOpk)).toList := by
        cases withOpk <;> simp [t2, CliTurn.after, call1, ht1_sent]
      have hsb : sentBody (wire0 withOpk) = some q.message := by
        rw [wire0_eq]
        dsimp only [sentBody]
        have htag : wirePrekey ≠ wireWhisperTag := by decide
        simp only [htag, ↓reduceIte, ← wire0_eq, hq]
        rfl
      rw [hsent, hsb]
      exact List.mem_singleton_self _
  have hrun2 : runFnToRelation run inp2
      (some (.exited 0 pt0
        (filesOf (inp2.files ++ encodeDir myParams (stB1_cli withOpk))))) := by
    unfold runFnToRelation
    have hmatch : ∀ x g, (stB0_cli withOpk).session = some (x, g) →
        PqSessionMatches x g (pkMsg0 withOpk) := by
      intro _ _ hs; cases withOpk <;> cases hs
    have hspec2 := (hSpec (stB0_cli withOpk) (wfPq_stB0 withOpk)).2.2.2.1
      (pkMsg0 withOpk) (rcVal withOpk) (by cases withOpk <;> decide +kernel) hmatch
    have hcap2 : ¬ List.length (wire0 withOpk) > CryptoVerification.SignalSession.stdinCapBytes := by
      cases withOpk <;> decide +kernel
    rw [← wire0_eq] at hspec2
    rw [hspec2, ite_eq_right hcap2, recvStep_eq_any X withOpk]
    rfl
  let files2 := filesOf (inp2.files ++ encodeDir myParams (stB1_cli withOpk))
  have hstep2 := CliTraces.step (Rel := runFnToRelation run) (interp := myInterp) (r := r)
    (t := t2) (leaks := []) (c := call2 withOpk) (i := inp2) (code := 0) (out := pt0)
    (files := files2) (fun _ h => nomatch h) hval2 hinp2 hrun2
    (CliTraces.done (t2.after r (call2 withOpk) 0 pt0 files2))
  have hstep1 := CliTraces.step (Rel := runFnToRelation run) (interp := myInterp) (r := r)
    (t := t1) (leaks := []) (c := call1 withOpk) (i := inp1) (code := 0) (out := wire0 withOpk)
    (files := files1) (fun _ h => nomatch h) hval1 hinp1 hrun1 hstep2
  have hstep0 := CliTraces.step (Rel := runFnToRelation run) (interp := myInterp) (r := r)
    (t := t0) (leaks := []) (c := call0 withOpk) (i := inp0) (code := 0) (out := [])
    (files := files0) (fun _ h => nomatch h) hval0 hinp0 hrun0 hstep1
  exact hstep0

end Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCliTraces
