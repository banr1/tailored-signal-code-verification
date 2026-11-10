/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuitySteps34
import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuityDecode

/-!
# Concrete SPQR-ON Non-Vacuity Step 5

Step 5 (`pqRecvWhisperModel` on Alice receiving Bob's V1 SPQR whisper reply) and assembly of the
5-step roundtrip witness `mock_nonvacuous_spqr_on`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers

open DY.Libsignal (HwBytes)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

set_option maxRecDepth 8192

def nvChA1FromPb : CryptoVerification.LibsignalSpqrV1.Chain :=
  match CryptoVerification.LibsignalSpqrV1.Chain.fromPb nvChA1Key.1.intoPb with
  | .ok c => c
  | .error _ => default

def nvChA2Key : CryptoVerification.LibsignalSpqrV1.Chain × HwBytes :=
  stepChainRecv0 (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) nvChA1FromPb

def nvPbA2 : CryptoVerification.LibsignalSpqrV1.PqRatchetStatePB
    CryptoVerification.LibsignalSpqrV1.V1State :=
  { nvPbA1 with versionNegotiation := none, chain := some nvChA2Key.1.intoPb }

def nvPqA2 : HwBytes :=
  (CryptoVerification.LibsignalSpqrV1.spqrDeps nvCrypto.F nvMlKem).encodeState nvPbA2

theorem nvPqA2_ne_nil : nvPqA2 ≠ [] := by
  intro h
  have hhead : nvPqA2.head? = some 0x12#8 := rfl
  rw [h] at hhead
  cases hhead

theorem nv_spqrRecv2 :
    (pqxdhSpqrSession nvW).recv nvPqA1 nvPqMsg2 = .ok (nvPqA2, nvSalt2) ∧
    (pqxdhSpqrSession nvW).recvPanics nvPqA1 nvPqMsg2 = false := by
  let D := CryptoVerification.LibsignalSpqrV1.spqrDeps nvCrypto.F nvMlKem
  let pbInnerA1 : D.V1StatePB :=
    { innerState := some (.keysSampled
        { uc := some { epoch := 1#64, auth := some nvAuth0.intoPb,
                       ek := nvEk1152, dk := nvDk2400 }
          sendingHdr := some (CryptoVerification.LibsignalSpqrV1.protoPolyEncoderToPb
            nvPe1Chunk.1.intoPb) }) }
  let stSampledA1 : D.States :=
    .keysSampled
      { uc := { epoch := 1#64
                auth := (CryptoVerification.LibsignalSpqrV1.spqrAuthApi nvCrypto.F).from_pb
                  nvAuth0.intoPb
                ek := nvEk1152
                dk := nvDk2400 }
        sending_hdr := nvPe1Chunk.1 }
  have hpre : CryptoVerification.LibsignalSpqrV1.msgPreamble nvPqMsg2 =
      .ok { version := 1#8, epoch := 1#64, index := 1#32, remaining := [0#8] } := rfl
  have hdeser : D.msgDeserialize 1#64 [0#8] = .ok { epoch := 1#64, payload := .none } := rfl
  have hpeFrom : CryptoVerification.LibsignalSpqrV1.spqrPolyApi.encoder_from_pb
      (CryptoVerification.LibsignalSpqrV1.protoPolyEncoderToPb nvPe1Chunk.1.intoPb) =
      .ok (.ok nvPe1Chunk.1) := rfl
  have hfromPb : D.statesFromPb pbInnerA1 = .ok stSampledA1 := by
    dsimp only [D, CryptoVerification.LibsignalSpqrV1.spqrDeps,
      CryptoVerification.LibsignalSpqrV1.liftStatesResult,
      CryptoVerification.LibsignalSpqrV1.States.from_pb,
      CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.from_pb,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.from_pb,
      CryptoVerification.LibsignalSpqrV1.encoderFromPbStateDecode,
      Functor.map, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
      pbInnerA1, stSampledA1]
    simp only [nvDk2400_len, nvEk1152_len,
      CryptoVerification.LibsignalSpqrV1.DECAPSULATION_KEY_SIZE,
      CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_KEY_SIZE,
      beq_self_eq_true, Bool.and_self, ↓reduceIte, hpeFrom]
    rfl
  have hrecv2 : D.statesRecv stSampledA1 { epoch := 1#64, payload := .none } =
      .ok (none, stSampledA1) := rfl
  have hchFrom : CryptoVerification.LibsignalSpqrV1.chainFrom
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F)
      (some nvChA1Key.1.intoPb) (some nvVnA) = .ok nvChA1FromPb := rfl
  have hchRecv : nvChA1FromPb.recvKey
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) (1#64 - 1#64) 1#32 =
      .ok (nvChA2Key.1, nvChA2Key.2) := by
    change nvChA1FromPb.recvKey (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F)
      0#64 1#32 = .ok nvChA2Key
    unfold CryptoVerification.LibsignalSpqrV1.Chain.recvKey nvChA2Key stepChainRecv0
    have hep : nvChA1FromPb.epochIdx 0#64 = .ok 0 := rfl
    simp only [show (0#64 == (0#64 : BitVec 64) && 1#32 == (0#32 : BitVec 32)) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure,
      CryptoVerification.LibsignalSpqrV1.ChainResult.ofError, hep]
    have hlinksA : ∃ linkA nextBytesA,
        nvChA1FromPb.links = [linkA] ∧
        linkA.recv = { ctr := 0#32, next := nextBytesA, prev := { data := [] } } ∧
        nextBytesA.length = 32 ∧
        nvChA1FromPb.params = CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb :=
      ⟨_, _, rfl, rfl, rfl, rfl⟩
    obtain ⟨linkA, nextBytesA, hlA, hrA, hnA, hpA⟩ := hlinksA
    simp only [hlA, List.getElem?_cons_zero, List.set, hrA, hpA]
    rw [ced_key_zero_one _ _ hnA]
  have hkeyEq : CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? (some nvChA2Key.2) =
      some nvSalt2 := rfl
  have htop : CryptoVerification.LibsignalSpqrV1.recv D
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) nvPqA1 nvPqMsg2 =
      .ok { state := nvPqA2, key := some nvChA2Key.2 } :=
    spqr_recv_v1_none_key D (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F)
      nvPqA1 nvPqMsg2 [0#8] 1#32 pbInnerA1 (some nvChA1Key.1.intoPb) nvVnA _
      stSampledA1 stSampledA1 nvChA1FromPb nvChA2Key.1 nvChA2Key.2
      hpre nv_decode_nvPbA1 rfl hdeser hfromPb hrecv2 hchFrom hchRecv rfl
  refine ⟨?_, ?_⟩
  · change ((CryptoVerification.LibsignalSpqrV1.spqrV1 nvCrypto.F nvMlKem).recv nvPqA1 nvPqMsg2) = _
    rw [CryptoVerification.LibsignalSpqrV1.spqrV1_eq]
    dsimp only [CryptoVerification.LibsignalSpqrV1.toSpqrModel,
      CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqr]
    rw [htop]
    dsimp only
    rw [hkeyEq]
  · change ((CryptoVerification.LibsignalSpqrV1.spqrV1 nvCrypto.F nvMlKem).recvPanics nvPqA1 nvPqMsg2) = false
    rw [CryptoVerification.LibsignalSpqrV1.spqrV1_eq]
    dsimp only [CryptoVerification.LibsignalSpqrV1.toSpqrModel,
      CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqr,
      CryptoVerification.LibsignalSpqrV1.recvPanicsB,
      CryptoVerification.LibsignalSpqrV1.recvPanicsSaltB]
    rw [htop]

theorem nvSpkB_ne_nvEphB : (⟨nvSpkB.publicKey.bytes⟩ == nvEphB.publicKey) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h0 : nvSpkB.publicKey.bytes.toList.head? = nvEphB.publicKey.bytes.toList.head? :=
    congrArg (fun (k : PublicKey) => k.bytes.toList.head?) h
  dsimp only [nvSpkB, nvEphB] at h0
  (try unfold keyPairOf at h0)
  (try unfold KeyPair.generate at h0)
  (try unfold Ratchet.clampScalar at h0)
  (try unfold List.Vector.set at h0)
  (try unfold List.Vector.get at h0)
  (try unfold List.Vector.replicate at h0)
  dsimp only [nvKeysB, nvW, nvCrypto, Ratchet.keyToBytesVec32, HMAC.keyToBytes32,
    List.Vector.toList] at h0
  cases h0

theorem nv_step5_recvA :
    ∃ sA2,
      pqRecvWhisperModel nvW nvStA2 nvBody2 9#256 =
        some (some ({ nvStA2 with peerId := some ⟨nvIdB.publicKey⟩,
                                  session := some (nvXA, ⟨.A, sA2, 0, [0]⟩) }, nvPt2)) ∧
      sA2.pqRatchetState = nvPqA2 := by
  have htf : SignalMessage.tryFrom protoSignalCodec nvBody2 = .ok nvInnerMsg2 :=
    tryFrom_protoSignalCodec_new_nv nvMk2.macKey none
      nvEphB.publicKey 0#32 0#32 (aesCbcEncrypt nvCrypto.E nvMk2.cipherKey nvMk2.iv nvPt2)
      ⟨nvIdB.publicKey⟩ ⟨nvIdA.publicKey⟩ nvPqMsg2
      (by have hc : (aesCbcEncrypt nvCrypto.E nvMk2.cipherKey nvMk2.iv nvPt2).length = 16 := rfl
          omega)
      (by have hp : nvPqMsg2.length = 4 := rfl
          omega)
      (by intro a ha; cases ha)
  let sBase : SessionState HwBytes :=
    (((SessionState.new currentVersion ⟨nvIdA.publicKey⟩ ⟨nvIdB.publicKey⟩ nvPA.1
        []).addReceiverChain ⟨nvSpkB.publicKey.bytes⟩ ⟨nvKey0, 0#32⟩).setSenderChain
      nvEphA ⟨HKDF.bytesToKey32 (Ratchet.chainHmac nvCrypto.F nvPA.2 Ratchet.chainKeySeed), 1#32⟩
    ).setUnacknowledgedPreKeyMessage
  let rState0 : RatchetState :=
    match (Mut.exec SessionState.takeRatchetState sBase).1 with
    | .ok r => r
    | .error _ => ⟨0, none, [], 0, 0⟩
  have htake : Mut.exec TripleRatchet.fromSessionState nvSA1 =
      (.ok ⟨rState0, nvPqA1, ⟨nvIdA.publicKey⟩, ⟨nvIdB.publicKey⟩⟩,
       { sBase with receiverChains := [], pqRatchetState := [] }) := rfl
  let newSenderKeyA : KeyPair := KeyPair.generate nvW.C 9#256
  let nvPA2 : BitVec 256 × BitVec 256 :=
    Ratchet.rootKdf nvCrypto.F nvPB.1 (List.replicate 32 1#8)
  let ckAfter : ChainKey :=
    ⟨HKDF.bytesToKey32 (Ratchet.chainHmac nvCrypto.F nvPB.2 Ratchet.chainKeySeed), 1#32⟩
  let rStateDh : RatchetState :=
    { rootKey := nvPA2.1
      senderChain := some ⟨newSenderKeyA, ⟨nvPA2.2, 0#32⟩⟩
      receiverChains :=
        [ ⟨⟨nvSpkB.publicKey.bytes⟩, some ⟨nvKey0, 0#32⟩, []⟩
        , ⟨nvEphB.publicKey, some ⟨nvPB.2, 0#32⟩, []⟩ ]
      previousCounter := 0#32
      maxForwardJumps := maxForwardJumps }
  let rState1 : RatchetState :=
    { rootKey := nvPA2.1
      senderChain := some ⟨newSenderKeyA, ⟨nvPA2.2, 0#32⟩⟩
      receiverChains :=
        [ ⟨⟨nvSpkB.publicKey.bytes⟩, some ⟨nvKey0, 0#32⟩, []⟩
        , ⟨nvEphB.publicKey, some ckAfter, []⟩ ]
      previousCounter := 0#32
      maxForwardJumps := maxForwardJumps }
  have hfind0 : rState0.findReceiverChainKey nvInnerMsg2.senderRatchetKey = .ok none := by
    have hsrk : nvInnerMsg2.senderRatchetKey = nvEphB.publicKey := rfl
    rw [hsrk]
    have hidx0 : rState0.findReceiverChainIndex nvEphB.publicKey = none := by
      change List.findIdx? (fun (c : ReceiverChain) => c.senderRatchetKey == nvEphB.publicKey)
        [⟨⟨nvSpkB.publicKey.bytes⟩, some ⟨nvKey0, 0#32⟩, []⟩] = none
      unfold List.findIdx? List.findIdx?.go
      dsimp only
      rw [nvSpkB_ne_nvEphB]
      rfl
    unfold RatchetState.findReceiverChainKey
    rw [hidx0]
  have hdhStep : Mut.exec (RatchetState.dhRatchetStep nvW.C nvInnerMsg2.senderRatchetKey 9#256)
      rState0 = (.ok ⟨nvPB.2, 0#32⟩, rStateDh) := rfl
  have hens : Mut.exec (RatchetState.ensureReceiverChain nvW.C nvInnerMsg2.senderRatchetKey 9#256)
      rState0 = (.ok ⟨nvPB.2, 0#32⟩, rStateDh) := by
    unfold RatchetState.ensureReceiverChain
    rw [mut_exec_bind, mut_exec_get]
    dsimp only
    rw [mut_exec_bind, mut_exec_liftE, hfind0]
    exact hdhStep
  have hidx1 : rStateDh.findReceiverChainIndex nvEphB.publicKey = some 1 := by
    change List.findIdx? (fun (c : ReceiverChain) => c.senderRatchetKey == nvEphB.publicKey)
      [⟨⟨nvSpkB.publicKey.bytes⟩, some ⟨nvKey0, 0#32⟩, []⟩,
       ⟨nvEphB.publicKey, some ⟨nvPB.2, 0#32⟩, []⟩] = some 1
    simp only [List.findIdx?, List.findIdx?.go, nvSpkB_ne_nvEphB, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte]
  have hset1 : Mut.exec (RatchetState.setReceiverChainKey nvEphB.publicKey ckAfter) rStateDh =
      (.ok (), rState1) := by
    unfold RatchetState.setReceiverChainKey
    rw [mut_exec_bind, mut_exec_get]
    dsimp only
    rw [hidx1]; rfl
  have hcons1 : Mut.exec (RatchetState.consumeMessageKey nvCrypto.F nvInnerMsg2.senderRatchetKey
      ⟨nvPB.2, 0#32⟩ nvInnerMsg2.counter .whisper) rStateDh =
      (.ok (ChainKey.messageKeys nvCrypto.F ⟨nvPB.2, 0#32⟩), rState1) := by
    have hsrk : nvInnerMsg2.senderRatchetKey = nvEphB.publicKey := rfl
    have hctr : nvInnerMsg2.counter = 0#32 := rfl
    have hnck : (⟨nvPB.2, 0#32⟩ : ChainKey).nextChainKey nvCrypto.F = .ok ckAfter := rfl
    rw [hsrk, hctr]
    unfold RatchetState.consumeMessageKey
    have hlt0 : ¬ ((0#32 : BitVec 32) < 0#32) := fun h => nomatch h
    simp only [hlt0, ↓reduceIte]
    rw [mut_exec_bind, mut_exec_get]
    dsimp only
    have hgt0 : ¬ (rStateDh.maxForwardJumps < (0#32 - 0#32 : BitVec 32).toNat) :=
      fun h => nomatch h
    simp only [hgt0, ↓reduceIte]
    have hadv0 : Mut.exec (RatchetState.advanceChain nvCrypto.F nvEphB.publicKey 0#32
        (0#32 - 0#32 : BitVec 32).toNat ⟨nvPB.2, 0#32⟩) rStateDh =
        (.ok ⟨nvPB.2, 0#32⟩, rStateDh) := rfl
    rw [mut_exec_bind, hadv0]
    dsimp only
    rw [mut_exec_bind, mut_exec_liftE, hnck]
    dsimp only
    rw [mut_exec_bind, hset1]; rfl
  have hstepR2 :
      (ChainKey.messageKeys nvCrypto.F ⟨nvPB.2, 0#32⟩).generateKeys nvCrypto.F nvSalt2 = nvMk2 :=
    rfl
  have hmac : nvInnerMsg2.verifyMacWithAddresses nvCrypto.F
      ((pqxdhSessionParams nvW).expectedAddrs .A) ⟨nvIdB.publicKey⟩ ⟨nvIdA.publicKey⟩ nvMk2.macKey = true :=
    verifyMacWithAddresses_new_nv _ _ _ _ _ _ _ _ _ _ rfl
  have hcbc : aesCbcDecrypt nvCrypto.D nvMk2.cipherKey nvMk2.iv nvInnerMsg2.ciphertext =
      some nvPt2 := rfl
  let sEmpty : SessionState HwBytes :=
    { sBase with receiverChains := [], pqRatchetState := [] }
  let sRestored : SessionState HwBytes :=
    { sEmpty with rootKey := rState1.rootKey
                  previousCounter := rState1.previousCounter
                  senderChain := rState1.senderChain
                  receiverChains := rState1.receiverChains
                  pqRatchetState := nvPqA2
                  pendingPreKey := false }
  refine ⟨sRestored, ?_, rfl⟩
  unfold pqRecvWhisperModel
  dsimp only [nvStA2]
  rw [htf]
  unfold pqxdhSessionDecryptModel SessionState.tryDecryptFromRecord
  have hver : ¬ (nvSA1.version.toNat ≠ nvInnerMsg2.messageVersion.toNat) := fun h => h rfl
  simp only [hver, ↓reduceIte]
  have htrDecA := mut_exec_decrypt_ok nvW.C (pqxdhSpqrSession nvW) ((pqxdhSessionParams nvW).expectedAddrs .A)
    nvInnerMsg2 .whisper 9#256 rState0 rStateDh rState1 nvPqA1 nvPqA2
    ⟨nvIdA.publicKey⟩ ⟨nvIdB.publicKey⟩ ⟨nvPB.2, 0#32⟩
    (ChainKey.messageKeys nvCrypto.F ⟨nvPB.2, 0#32⟩) nvSalt2 nvMk2 nvPt2
    hens hcons1 nv_spqrRecv2.2 nv_spqrRecv2.1 hstepR2 hmac hcbc
  have hwsA := mut_exec_tryDecryptWithState_ok nvW.C (pqxdhSpqrSession nvW)
    ((pqxdhSessionParams nvW).expectedAddrs .A) nvInnerMsg2 .whisper 9#256 nvSA1 sEmpty _ _ nvPt2
    htake htrDecA
  rw [hwsA]
  dsimp only
  have hrem2 : sRestored.remoteIdentity = some ⟨nvIdB.publicKey⟩ := rfl
  have htr2 : nvStA2.trusts ⟨nvIdB.publicKey⟩ = true := rfl
  change (match sRestored.remoteIdentity with
    | none => some none
    | some k => if !nvStA2.trusts k then some none else _) = _
  rw [hrem2]
  dsimp only
  rw [htr2]
  rfl

theorem mock_nonvacuous_spqr_on :
    nvStA0.session = none ∧
    nvStB0.session = none ∧
    ∃ (stA1 stA2 stB1 stB2 stA3 : PqParty) (m1 : PreKeyMessageFields) (wire1 wire2 body2 : HwBytes),
      pqInitModel nvX nvW nvStA0 nvBundleB nvTapeA =
        some (some (stA1, [])) ∧
      pqSendModel nvW stA1 nvPt1 nvCoins64A =
        some (some (stA2, wire1)) ∧
      wire1 = wirePrekey :: m1.bytes ∧
      pqRecvPrekeyModel nvX nvW nvStB0 m1 8#256 =
        some (some (stB1, nvPt1)) ∧
      pqSendModel nvW stB1 nvPt2 nvCoins64B =
        some (some (stB2, wire2)) ∧
      wire2 = wireWhisper :: body2 ∧
      pqRecvWhisperModel nvW stA2 body2 9#256 =
        some (some (stA3, nvPt2)) ∧
      ∃ x3 g3, stA3.session = some (x3, g3) ∧ g3.session.pqRatchetState ≠ [] := by
  refine ⟨rfl, rfl, ?_⟩
  obtain ⟨sA2, hstep5, hsA2pq⟩ := nv_step5_recvA
  refine ⟨nvStA1, nvStA2, nvStB1, nvStB2,
    { nvStA2 with peerId := some ⟨nvIdB.publicKey⟩, session := some (nvXA, ⟨.A, sA2, 0, [0]⟩) },
    nvM1, nvWire1, nvWire2, nvBody2,
    nv_step1_init, nv_step2_sendA, rfl, nv_step3_recvB, nv_step4_sendB, rfl, hstep5,
    nvXA, ⟨.A, sA2, 0, [0]⟩, rfl, ?_⟩
  rw [hsA2pq]
  exact nvPqA2_ne_nil

end Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
