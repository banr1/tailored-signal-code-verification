/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuityBase

/-!
# Concrete SPQR-ON Non-Vacuity Steps 1-2

Step 1 (`pqInitModel` on Alice) and Step 2 (`pqSendModel` first prekey message on Alice with
SPQR V1 key sampling and header chunk encoding) for the SPQR-ON roundtrip witness.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers

open DY.Libsignal (HwBytes)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

set_option maxRecDepth 8192

/-! ## Step 1: Handshake and `pqInitModel` on Alice -/

def nvIdA : KeyPair := keyPairOf nvW.C nvStA0.me.idPriv
def nvIdB : KeyPair := keyPairOf nvW.C nvStB0.me.idPriv
def nvSpkB : KeyPair := keyPairOf nvW.C nvKeysB.spkPriv
def nvBaseA : KeyPair := keyPairOf nvW.C (List.Vector.replicate 32 5#8)
def nvEphA : KeyPair := KeyPair.generate nvW.C (HKDF.bytesToKey32 (List.replicate 32 5#8))
def nvKey0 : BitVec 256 := HKDF.bytesToKey32 (ofU8 SignalPqxdh.sha256InitState)
def nvPA : BitVec 256 × BitVec 256 :=
  Ratchet.rootKdf nvCrypto.F nvKey0 (List.replicate 32 1#8)

def nvHdr : SignalPqxdh.HandshakeHdr :=
  { ikAPk := vecU8 nvIdA.publicKey.bytes
    ekAPk := vecU8 nvBaseA.publicKey.bytes
    spkId := u32 1#32
    opkId? := none
    pqspkId := u32 2#32
    kemCt := vecU8 nvVec1568 }

theorem nv_initiateKeys :
    SignalPqxdh.Model.initiateKeys (modelPrims nvX nvW)
      (initiateInput nvW nvStA0.me nvBundleB nvTapeA) =
    some (nvDk, nvHdr) := by
  have hikB : (vecU8 nvIdB.publicKey.bytes).length = 32 := vecU8_length _
  have hsig1 := sigVerify_nv_zero64 (vecU8 nvIdB.publicKey.bytes)
    (SignalPqxdh.encodeEC (vecU8 nvSpkB.publicKey.bytes)) hikB
  have hsig2 := sigVerify_nv_zero64 (vecU8 nvIdB.publicKey.bytes)
    (SignalPqxdh.encodeKEM (vecU8 nvVec1568)) hikB
  have hkem : (modelPrims nvX nvW).kemEncaps (vecU8 nvVec1568)
      (vecU8 (initiateKemCoins nvTapeA)) =
      some (vecU8 (List.Vector.replicate 32 1#8), vecU8 nvVec1568) := by
    have hpkLen : ((vecU8 nvVec1568).length == SignalPqxdh.kyberPkLen) = true := by
      rw [vecU8_length]; rfl
    dsimp only [modelPrims, blockLevelPrims, nvW]
    simp only [hpkLen, ↓reduceIte]
    rw [nvVec1568_eq]
  have hxBne : ∀ a b, ((modelPrims nvX nvW).x25519 a b != List.replicate 32 0) = true :=
    fun _ _ => rfl
  have hbase : (modelPrims nvX nvW).x25519Base (toU8 (nvTapeA.toList.take 32)) =
      vecU8 nvBaseA.publicKey.bytes := rfl
  have hinp : initiateInput nvW nvStA0.me nvBundleB nvTapeA =
      { ikASk := vecU8 nvIdA.privateKey.bytes
        ikAPk := vecU8 nvIdA.publicKey.bytes
        ekASk := toU8 (nvTapeA.toList.take 32)
        kemCoins := vecU8 (initiateKemCoins nvTapeA)
        trustedPeer := true
        bundle :=
          { ikB := vecU8 nvIdB.publicKey.bytes
            spkId := u32 1#32
            spkB := vecU8 nvSpkB.publicKey.bytes
            spkSig := vecU8 (List.Vector.replicate 64 0#8)
            opkB? := none
            pqspkId := u32 2#32
            pqspkB := vecU8 nvVec1568
            pqspkSig := vecU8 (List.Vector.replicate 64 0#8) } } := by
    dsimp only [initiateInput, nvBundleB, honestBundle, nvKeysB, nvIdA, nvIdB, nvSpkB]
    rw [nvVec1568_eq]
    rfl
  rw [hinp]
  unfold SignalPqxdh.Model.initiateKeys
  simp only [«guard», bind, Bind.bind, Option.bind, pure, Pure.pure, Option.map, ↓reduceIte,
    hsig1, hsig2, hkem, hxBne, SignalPqxdh.dhOptNonZero, hkdfDerive96_nv, hbase]
  rfl

def nvPqA0 : HwBytes := (pqxdhSpqrSession nvW).init .a2b nvKey0
def nvPqB0 : HwBytes := (pqxdhSpqrSession nvW).init .b2a nvKey0

def nvSA0 : SessionState HwBytes :=
  (((SessionState.new currentVersion ⟨nvIdA.publicKey⟩ ⟨nvIdB.publicKey⟩ nvPA.1
      nvPqA0).addReceiverChain ⟨nvSpkB.publicKey.bytes⟩ ⟨nvKey0, 0#32⟩).setSenderChain
    nvEphA ⟨nvPA.2, 0#32⟩).setUnacknowledgedPreKeyMessage

def nvXA : RecordExtras :=
  initiatorRecordExtras nvStA0.me nvBundleB nvBaseA.publicKey nvVec1568

def nvStA1 : PqParty :=
  { nvStA0 with peerId := some ⟨nvIdB.publicKey⟩, session := some (nvXA, ⟨.A, nvSA0, 0, [0]⟩) }

theorem nv_step1_init :
    pqInitModel nvX nvW nvStA0 nvBundleB nvTapeA = some (some (nvStA1, [])) := by
  unfold pqInitModel initiateState
  have htrust : nvStA0.trusts ⟨⟨nvBundleB.idPub⟩⟩ = true := rfl
  rw [htrust]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [show nvStA0.party = .A from rfl, nv_initiateKeys]
  dsimp only
  have hcoinsA : (nvTapeA.toList.drop 160).take 32 = List.replicate 32 5#8 := rfl
  rw [hcoinsA]
  have hinitSess :
      initializeInitiatorSession nvW.C (pqxdhSpqrSession nvW)
        ⟨(keyPairOf nvW.C nvStA0.me.idPriv).publicKey⟩ ⟨⟨nvBundleB.idPub⟩⟩ ⟨nvBundleB.spkPub⟩
        nvKey0 nvKey0 nvKey0 (HKDF.bytesToKey32 (List.replicate 32 5#8)) =
      .ok (((SessionState.new currentVersion ⟨nvIdA.publicKey⟩ ⟨nvIdB.publicKey⟩ nvPA.1
          nvPqA0).addReceiverChain ⟨nvSpkB.publicKey.bytes⟩ ⟨nvKey0, 0#32⟩).setSenderChain
        nvEphA ⟨nvPA.2, 0#32⟩) := rfl
  change (match initializeInitiatorSession nvW.C (pqxdhSpqrSession nvW)
      ⟨(keyPairOf nvW.C nvStA0.me.idPriv).publicKey⟩ ⟨⟨nvBundleB.idPub⟩⟩ ⟨nvBundleB.spkPub⟩
      nvKey0 nvKey0 nvKey0 (HKDF.bytesToKey32 (List.replicate 32 5#8)) with
    | .error _ => none
    | .ok st => _) = _
  rw [hinitSess]
  dsimp only [nvHdr]
  rw [u8Vec_vecU8, u8Vec_vecU8]
  rfl

/-! ## Step 2: SPQR V1 First Send and `pqSendModel` on Alice -/

def nvAuth0 : CryptoVerification.LibsignalSpqrV1.Authenticator :=
  CryptoVerification.LibsignalSpqrV1.Authenticator.new nvCrypto.F (HMAC.keyToBytes32 nvKey0) 1#64

def nvVnA : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB :=
  { authKey := HMAC.keyToBytes32 nvKey0
    direction := 0#32
    minVersion := 1#32
    chainParams := some CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb }

def nvHdrMac : HwBytes :=
  nvAuth0.macHdrUnchecked nvCrypto.F 1#64 (List.replicate 64 0#8)

def nvPe0 : CryptoVerification.LibsignalSpqrV1.PolyEncoder :=
  match CryptoVerification.LibsignalSpqrV1.PolyEncoder.encodeBytes
      (List.replicate 64 0#8 ++ nvHdrMac) with
  | .ok (.ok enc) => enc
  | _ => default

def nvPe1Chunk : CryptoVerification.LibsignalSpqrV1.PolyEncoder ×
    CryptoVerification.LibsignalSpqrV1.Chunk :=
  match nvPe0.nextChunk with
  | .ok p => p
  | .error _ => (default, default)

def nvChA0 : CryptoVerification.LibsignalSpqrV1.Chain :=
  match CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) nvVnA with
  | .ok c => c
  | .error _ => default

def nvChA1Key : CryptoVerification.LibsignalSpqrV1.Chain × (BitVec 32 × HwBytes) :=
  match nvChA0.sendKey (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) 0#64 with
  | .ok res => res
  | .error _ => (default, (0#32, []))

def nvPbA1 : CryptoVerification.LibsignalSpqrV1.PqRatchetStatePB
    CryptoVerification.LibsignalSpqrV1.V1State :=
  { inner := some { innerState := some (.keysSampled
      { uc := some { epoch := 1#64, auth := some nvAuth0.intoPb, ek := nvEk1152, dk := nvDk2400 }
        sendingHdr := some (CryptoVerification.LibsignalSpqrV1.protoPolyEncoderToPb
          nvPe1Chunk.1.intoPb) }) }
    versionNegotiation := some nvVnA
    chain := some nvChA1Key.1.intoPb }

def nvPqA1 : HwBytes :=
  (CryptoVerification.LibsignalSpqrV1.spqrDeps nvCrypto.F nvMlKem).encodeState nvPbA1

def nvSalt1 : Option (List.Vector (BitVec 8) 32) :=
  match CryptoVerification.LibsignalSpqrV1.messageKeyToSalt? (some nvChA1Key.2.2) with
  | some s => s
  | none => none

theorem replicate32_zero_len : (List.replicate 32 (0#8)).length = 32 := rfl

def nvChunk0 : CryptoVerification.LibsignalSpqrV1.Chunk :=
  { index := 0#16, data := ⟨List.replicate 32 0#8, replicate32_zero_len⟩ }

def nvPqMsg1 : HwBytes :=
  (CryptoVerification.LibsignalSpqrV1.spqrDeps nvCrypto.F nvMlKem).msgSerialize
    { epoch := 1#64, payload := .hdr nvChunk0 } nvChA1Key.2.1

theorem spqr_send_v1
    (D : CryptoVerification.LibsignalSpqrV1.SpqrApiDeps)
    (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    (stateBytes tape tape' msgTail : HwBytes)
    (pb : D.V1StatePB)
    (vn : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB)
    (st0 st1 : D.States)
    (msg : D.MessageV1)
    (ch0 ch2 : CryptoVerification.LibsignalSpqrV1.Chain)
    (idx : BitVec 32)
    (msgKey : HwBytes)
    (hdec : CryptoVerification.LibsignalSpqrV1.decodeState D stateBytes =
      .ok { inner := some pb, chain := none, versionNegotiation := some vn })
    (hfrom : D.statesFromPb pb = .ok st0)
    (hsend : D.statesSend st0 tape = (.ok (msg, none, st1), tape'))
    (hvn : vn.minVersion = 1#32)
    (hch : CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation hkdf vn = .ok ch0)
    (hep : D.msgEpoch msg = 1#64)
    (hsk : ch0.sendKey hkdf (1#64 - 1#64) = .ok (ch2, (idx, msgKey)))
    (hser : D.msgSerialize msg idx = 1#8 :: msgTail)
    (hne : msgKey.isEmpty = false) :
    (CryptoVerification.LibsignalSpqrV1.send D hkdf stateBytes tape).1 =
      .ok { state := D.encodeState
              { inner := some (D.statesIntoPb st1)
                versionNegotiation := some vn
                chain := some ch2.intoPb }
            msg := 1#8 :: msgTail
            key := some msgKey } := by
  cases D
  cases vn
  dsimp only at *
  subst hvn
  unfold CryptoVerification.LibsignalSpqrV1.send
  simp only [hdec, hfrom, hsend,
    CryptoVerification.LibsignalSpqrV1.sendAfterStates,
    CryptoVerification.LibsignalSpqrV1.Version.toI32,
    CryptoVerification.LibsignalSpqrV1.Version.toU8,
    CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
    CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    show BitVec.slt (0#32 : BitVec 32) 1#32 = true from rfl,
    hch, hep,
    show ((1#64 : BitVec 64) == 0#64) = false from rfl,
    hsk, hser,
    show ((1#8 : BitVec 8) != 1#8) = false from rfl,
    hne, Bool.false_eq_true, ↓reduceIte]

theorem nv_spqrSend1 :
    (pqxdhSpqrSession nvW).send nvPqA0 nvCoins64A = some (nvPqA1, nvSalt1, nvPqMsg1) ∧
    (pqxdhSpqrSession nvW).sendPanics nvPqA0 nvCoins64A = false := by
  let D := CryptoVerification.LibsignalSpqrV1.spqrDeps nvCrypto.F nvMlKem
  let pb0A : D.V1StatePB :=
    { innerState := some (.keysUnsampled
        { uc := some { epoch := 1#64, auth := some nvAuth0.intoPb } }) }
  let st0A : D.States :=
    .keysUnsampled { uc := { epoch := 1#64, auth := nvAuth0 } }
  let st1 : D.States :=
    .keysSampled
      { uc := { epoch := 1#64, auth := nvAuth0, ek := nvEk1152, dk := nvDk2400 }
        sending_hdr := nvPe1Chunk.1 }
  have hdec0 : CryptoVerification.LibsignalSpqrV1.decodeState D nvPqA0 =
      .ok { inner := some pb0A, chain := none, versionNegotiation := some nvVnA } := rfl
  have hgen : CryptoVerification.LibsignalSpqrV1.generate nvMlKem nvCoins64A =
      .ok ({ ek := nvEk1152, dk := nvDk2400, hdr := List.replicate 64 0#8 }, []) := by
    have hg0 : CryptoVerification.LibsignalSpqrV1.generate nvMlKem nvCoins64A =
        .ok ({ ek := (nvMlKem.fromSeed nvSeedA).2.1.toList
               dk := (nvMlKem.fromSeed nvSeedA).2.2.toList
               hdr := (nvMlKem.fromSeed nvSeedA).1.toList }, []) := rfl
    rw [hg0, nvEk1152_def, nvDk2400_def, nvMlKem_fromSeed_hdr]
  have hpe0 : CryptoVerification.LibsignalSpqrV1.spqrPolyApi.encode_bytes
      (List.replicate 64 0#8 ++ nvHdrMac) = .ok (.ok nvPe0) := rfl
  have hpe1 : CryptoVerification.LibsignalSpqrV1.spqrPolyApi.next_chunk nvPe0 =
      .ok (nvPe1Chunk.1, nvChunk0) := by
    have hp : CryptoVerification.LibsignalSpqrV1.spqrPolyApi.next_chunk nvPe0 =
        .ok nvPe1Chunk := rfl
    have hvec : nvPe1Chunk.2.data =
        (0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ
         0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ
         0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ
         0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ 0#8 ::ᵥ
         List.Vector.nil) := rfl
    rw [hp]
    apply congrArg Except.ok
    apply Prod.ext
    · rfl
    · cases hchunk : nvPe1Chunk.2 with | mk idx d =>
      have hidx : idx = 0#16 := by
        have h0 : nvPe1Chunk.2.index = 0#16 := rfl
        rw [hchunk] at h0
        exact h0
      subst hidx
      have hd : d = nvPe1Chunk.2.data := by rw [hchunk]
      rw [hd, hvec]
      dsimp only [nvChunk0]
      congr 1
  have hfrom0 : D.statesFromPb pb0A = .ok st0A := by
    dsimp only [D, pb0A, st0A, CryptoVerification.LibsignalSpqrV1.spqrDeps,
      CryptoVerification.LibsignalSpqrV1.liftStatesResult,
      CryptoVerification.LibsignalSpqrV1.States.from_pb,
      CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.from_pb,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.from_pb,
      Functor.map, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [show (CryptoVerification.LibsignalSpqrV1.spqrAuthApi nvCrypto.F).from_pb
          nvAuth0.intoPb = nvAuth0 from
        CryptoVerification.LibsignalSpqrV1.Authenticator.fromPb_intoPb nvAuth0]
  have hmac0 : (CryptoVerification.LibsignalSpqrV1.spqrAuthApi nvCrypto.F).mac_hdr
      nvAuth0 1#64 (List.replicate 64 0#8) = .ok nvHdrMac := rfl
  have hstatesSend :
      D.statesSend st0A nvCoins64A =
      (.ok ({ epoch := 1#64, payload := .hdr nvChunk0 }, none, st1), []) := by
    dsimp only [D, st0A, st1, CryptoVerification.LibsignalSpqrV1.spqrDeps,
      CryptoVerification.LibsignalSpqrV1.States.send,
      CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.send_hdr_chunk,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.send_header,
      CryptoVerification.LibsignalSpqrV1.expectEncodeBytes,
      CryptoVerification.LibsignalSpqrV1.StatesResult.ofPanic,
      CryptoVerification.LibsignalSpqrV1.liftSpqrPanic,
      liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [hgen]
    dsimp only
    rw [hmac0]
    dsimp only
    rw [hpe0]
    dsimp only
    conv => lhs; rw [hpe1]
    rfl
  have hchA0 : CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) nvVnA = .ok nvChA0 := rfl
  have hskA0 : nvChA0.sendKey
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) (1#64 - 1#64) =
      .ok (nvChA1Key.1, (nvChA1Key.2.1, nvChA1Key.2.2)) := rfl
  have hser1 : ∃ msgTail,
      D.msgSerialize { epoch := 1#64, payload := .hdr nvChunk0 } nvChA1Key.2.1 =
        1#8 :: msgTail ∧
      1#8 :: msgTail = nvPqMsg1 := ⟨_, rfl, rfl⟩
  obtain ⟨msgTail, hserD, hserEq⟩ := hser1
  have hkeyEq : CryptoVerification.LibsignalSpqrV1.messageKeyToSalt? (some nvChA1Key.2.2) =
      some nvSalt1 := rfl
  have htop : (CryptoVerification.LibsignalSpqrV1.send D
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) nvPqA0 nvCoins64A).1 =
      .ok { state := nvPqA1, msg := nvPqMsg1, key := some nvChA1Key.2.2 } := by
    rw [← hserEq]
    exact spqr_send_v1 D (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F)
      nvPqA0 nvCoins64A [] msgTail pb0A nvVnA st0A st1 _ nvChA0 nvChA1Key.1
      nvChA1Key.2.1 nvChA1Key.2.2 hdec0 hfrom0 hstatesSend rfl hchA0 rfl hskA0 hserD rfl
  refine ⟨?_, ?_⟩
  · change ((CryptoVerification.LibsignalSpqrV1.spqrV1 nvCrypto.F nvMlKem).send nvPqA0 nvCoins64A) = _
    rw [CryptoVerification.LibsignalSpqrV1.spqrV1_eq]
    dsimp only [CryptoVerification.LibsignalSpqrV1.toSpqrModel,
      CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqr]
    rw [htop]
    dsimp only
    rw [hkeyEq]
  · change ((CryptoVerification.LibsignalSpqrV1.spqrV1 nvCrypto.F nvMlKem).sendPanics nvPqA0 nvCoins64A) = false
    rw [CryptoVerification.LibsignalSpqrV1.spqrV1_eq]
    dsimp only [CryptoVerification.LibsignalSpqrV1.toSpqrModel,
      CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqr,
      CryptoVerification.LibsignalSpqrV1.sendPanicsPureB]
    rw [htop]

def nvMk1 : MessageKeys :=
  ((⟨nvPA.2, 0#32⟩ : ChainKey).messageKeys nvCrypto.F).generateKeys nvCrypto.F nvSalt1

def nvInnerMsg1 : SignalMessage :=
  SignalMessage.new nvCrypto.F protoSignalCodec currentVersion nvMk1.macKey
    ((pqxdhSessionParams nvW).sendAddrs .A) nvEphA.publicKey 0#32 0#32
    (aesCbcEncrypt nvCrypto.E nvMk1.cipherKey nvMk1.iv nvPt1)
    ⟨nvIdA.publicKey⟩ ⟨nvIdB.publicKey⟩ nvPqMsg1

def nvSA1 : SessionState HwBytes :=
  { (((SessionState.new currentVersion ⟨nvIdA.publicKey⟩ ⟨nvIdB.publicKey⟩ nvPA.1
        nvPqA0).addReceiverChain ⟨nvSpkB.publicKey.bytes⟩ ⟨nvKey0, 0#32⟩).setSenderChain
      nvEphA ⟨HKDF.bytesToKey32 (Ratchet.chainHmac nvCrypto.F nvPA.2 Ratchet.chainKeySeed), 1#32⟩
    ).setUnacknowledgedPreKeyMessage with pqRatchetState := nvPqA1 }

def nvM1 : PreKeyMessageFields :=
  { regId := 10#32
    opkId := none
    spkId := 1#32
    kpkId := 2#32
    kyberCt := List.Vector.replicate 1568 0#8
    baseKey := nvBaseA.publicKey.bytes
    idPub := nvIdA.publicKey.bytes
    inner := nvInnerMsg1.serialized }

def nvWire1 : HwBytes := wirePrekey :: nvM1.bytes

def nvStA2 : PqParty :=
  { nvStA1 with peerId := some ⟨nvIdB.publicKey⟩, session := some (nvXA, ⟨.A, nvSA1, 0, [0]⟩) }

theorem nv_msgEncrypt1 :
    SessionState.messageEncrypt nvW.C protoSignalCodec (pqxdhSpqrSession nvW)
      ((pqxdhSessionParams nvW).sendAddrs .A) nvPt1 nvCoins64A nvSA0 =
    (.ok nvInnerMsg1, nvSA1) := by
  have hFrom : Mut.exec OutgoingTripleRatchet.fromSessionState nvSA0 =
      (.ok ⟨nvEphA, ⟨nvPA.2, 0#32⟩, 0, nvPqA0, currentVersion, ⟨nvIdA.publicKey⟩, ⟨nvIdB.publicKey⟩⟩,
       { nvSA0 with pqRatchetState := [] }) := rfl
  unfold SessionState.messageEncrypt
  rw [hFrom]
  dsimp only [OutgoingTripleRatchet.encrypt,
    Mut.exec, ExceptT.run, StateT.run, Id.run,
    monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
    ExceptT.lift, Functor.map, StateT.map,
    bind, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    pure, Pure.pure, ExceptT.pure, StateT.bind, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get]
  rw [nv_spqrSend1.2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [nv_spqrSend1.1]
  rfl

theorem nv_step2_sendA :
    pqSendModel nvW nvStA1 nvPt1 nvCoins64A = some (some (nvStA2, nvWire1)) := by
  unfold pqSendModel
  have hrem : nvSA0.remoteIdentity = some ⟨nvIdB.publicKey⟩ := rfl
  have hpend : nvSA0.pendingPreKey = true := rfl
  have hbody : firstMessageBody nvXA nvSA0 nvInnerMsg1 = nvM1.bytes := by
    dsimp only [firstMessageBody, nvXA, initiatorRecordExtras, nvBundleB, honestBundle, nvKeysB,
      PreKeyMessageFields.bytes, nvM1, nvStA0]
    rw [← nvVec1568_eq]
    rfl
  simp only [nvStA1, nv_msgEncrypt1, hrem, PqParty.trusts, nvStA0, hpend, hbody, ↓reduceIte]
  rfl

end Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
