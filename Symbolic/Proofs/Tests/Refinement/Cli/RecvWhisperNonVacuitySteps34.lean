/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuitySteps12

/-!
# Concrete SPQR-ON Non-Vacuity Steps 3-4

Step 3 (`pqRecvPrekeyModel` on Bob with SPQR V1 header chunk reception) and Step 4
(`pqSendModel` whisper reply on Bob) for the SPQR-ON roundtrip witness.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers

open DY.Libsignal (HwBytes)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

set_option maxRecDepth 8192

/-! ## Step 3: `pqRecvPrekeyModel` on Bob -/

theorem nv_acceptKeys :
    SignalPqxdh.Model.acceptKeys (modelPrims nvX nvW)
      (acceptInput nvW nvStB0.me nvKeysB nvM1) = some nvDk := by
  have hikAlen : (vecU8 nvIdA.publicKey.bytes).length = 32 := vecU8_length _
  have hekAlen : (vecU8 nvBaseA.publicKey.bytes).length = 32 := vecU8_length _
  have hctlen : (vecU8 nvVec1568).length = SignalPqxdh.kyberCtLen := vecU8_length _
  have hcanon : (modelPrims nvX nvW).isCanonical (vecU8 nvBaseA.publicKey.bytes) = true := rfl
  have hkem : (modelPrims nvX nvW).kemDecaps (vecU8 nvVec3168) (vecU8 nvVec1568) =
      some (vecU8 (List.Vector.replicate 32 1#8)) := by
    have hctb : ((vecU8 nvVec1568).length == SignalPqxdh.kyberCtLen) = true := by
      rw [vecU8_length]; rfl
    dsimp only [modelPrims, blockLevelPrims, nvW]
    simp only [hctb, ↓reduceIte]
  have hxBne : ∀ a b, ((modelPrims nvX nvW).x25519 a b != List.replicate 32 0) = true :=
    fun _ _ => rfl
  have hinp : acceptInput nvW nvStB0.me nvKeysB nvM1 =
      { ikBSk := vecU8 nvIdB.privateKey.bytes
        ikBPk := vecU8 nvIdB.publicKey.bytes
        spkBSk := vecU8 nvSpkB.privateKey.bytes
        spkBPk := vecU8 nvSpkB.publicKey.bytes
        opkBSk? := none
        pqspkBSk := vecU8 nvVec3168
        pqspkBPk := vecU8 nvVec1568
        trustedPeer := true
        replayOk := true
        hdr := nvHdr } := by
    dsimp only [acceptInput, Option.map, nvKeysB, nvM1, nvIdB, nvSpkB, nvHdr]
    rw [nvVec1568_eq, nvVec3168_eq]
  rw [hinp]
  unfold SignalPqxdh.Model.acceptKeys
  simp only [«guard», bind, Bind.bind, Option.bind, pure, Pure.pure, ↓reduceIte,
    nvHdr, hikAlen, hekAlen, hctlen, beq_self_eq_true, hcanon, hkem, hxBne,
    SignalPqxdh.dhOptNonZero, hkdfDerive96_nv]

def nvDec0 : CryptoVerification.LibsignalSpqrV1.PolyDecoder :=
  { ptsNeeded := 48
    pts := List.replicate 16 CryptoVerification.LibsignalSpqrV1.SortedSetPt.new
    isComplete := false }

def nvDec1 : CryptoVerification.LibsignalSpqrV1.PolyDecoder :=
  { ptsNeeded := 48
    pts := List.replicate 16
      ((CryptoVerification.LibsignalSpqrV1.SortedSetPt.new.push
        { x := CryptoVerification.LibsignalSpqrV1.GF16.new 0
          y := CryptoVerification.LibsignalSpqrV1.GF16.new 0 }).1)
    isComplete := false }

theorem nvChunk0_get (idx : Fin 32) : nvChunk0.data.get idx = 0#8 := by
  unfold List.Vector.get
  dsimp only [nvChunk0]
  exact List.getElem_replicate _

theorem nv_addChunk0 :
    CryptoVerification.LibsignalSpqrV1.PolyDecoder.addChunk nvDec0 nvChunk0 = .ok nvDec1 := by
  unfold CryptoVerification.LibsignalSpqrV1.PolyDecoder.addChunk
  dsimp only [nvDec0, CryptoVerification.LibsignalSpqrV1.PolyDecoder.addChunkLoop]
  simp only [nvChunk0_get]
  rfl

def stepCedNext (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    (ced : CryptoVerification.LibsignalSpqrV1.ChainEpochDirection) :
    CryptoVerification.LibsignalSpqrV1.ChainEpochDirection × HwBytes :=
  match ced.nextKey hkdf with
  | .ok (ced', (_, out)) => (ced', out)
  | .error _ => (default, [])

theorem ced_key_zero_one (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    (nextBytes : HwBytes) (hnext : nextBytes.length = 32) :
    CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.key hkdf
      { ctr := 0#32, next := nextBytes, prev := { data := [] } } 1#32
      CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb =
    .ok (stepCedNext hkdf { ctr := 0#32, next := nextBytes, prev := { data := [] } }) := by
  have hadv : CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.keyAdvanceLoop hkdf
      { ctr := 0#32, next := nextBytes, prev := { data := [] } } 1#32
      CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb =
      .ok { ctr := 0#32, next := nextBytes, prev := { data := [] } } := by
    unfold CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.keyAdvanceLoop
    simp
  have hlt0 : ¬ ((1#32 : BitVec 32) < 0#32) := fun h => nomatch h
  have hjmp : ¬ ((1#32 - 0#32 : BitVec 32) >
      CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb.maxJumpOrDefault) :=
    fun h => nomatch h
  have hooo1 : ¬ ((0#32 : BitVec 32).toNat +
      CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb.maxOooKeysOrDefault.toNat ≥
      2 ^ 32) :=
    fun h => nomatch h
  have hooo2 : ¬ ((1#32 : BitVec 32) > 0#32 +
      CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb.maxOooKeysOrDefault) :=
    fun h => nomatch h
  unfold CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.key stepCedNext
    CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.nextKey
  simp only [hlt0, show ((1#32 : BitVec 32) == 0#32) = false from rfl,
    hjmp, hooo1, hooo2, Bool.false_eq_true, ↓reduceIte,
    Bind.bind, Except.bind, Pure.pure, Except.pure, hadv]
  have hgc : CryptoVerification.LibsignalSpqrV1.KeyHistory.gc { data := [] } 0#32
      CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb = .ok { data := [] } := rfl
  rw [hgc]
  dsimp only [CryptoVerification.LibsignalSpqrV1.ChainResult.ofPanic,
    CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.nextKeyInternal]
  simp only [hnext, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    show ((0#32 : BitVec 32) == 0xffffffff#32) = false from rfl]

def stepChainRecv0 (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    (c : CryptoVerification.LibsignalSpqrV1.Chain) :
    CryptoVerification.LibsignalSpqrV1.Chain × HwBytes :=
  match c.links with
  | [link] =>
    let (recv', out) := stepCedNext hkdf link.recv
    ({ c with links := [{ link with recv := recv' }] }, out)
  | _ => (default, [])

def nvVnB : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB :=
  { authKey := HMAC.keyToBytes32 nvKey0
    direction := 1#32
    minVersion := 1#32
    chainParams := some CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb }

def nvChB0 : CryptoVerification.LibsignalSpqrV1.Chain :=
  match CryptoVerification.LibsignalSpqrV1.chainFrom
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) none (some nvVnB) with
  | .ok c => c
  | .error _ => default

def nvChB1Key : CryptoVerification.LibsignalSpqrV1.Chain × HwBytes :=
  stepChainRecv0 (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) nvChB0

def nvPbB1 : CryptoVerification.LibsignalSpqrV1.PqRatchetStatePB
    CryptoVerification.LibsignalSpqrV1.V1State :=
  { inner := some { innerState := some (.noHeaderReceived
      { uc := some { epoch := 1#64, auth := some nvAuth0.intoPb }
        receivingHdr := some (CryptoVerification.LibsignalSpqrV1.protoPolyDecoderToPb
          nvDec1.intoPb) }) }
    versionNegotiation := none
    chain := some nvChB1Key.1.intoPb }

def nvPqB1 : HwBytes :=
  (CryptoVerification.LibsignalSpqrV1.spqrDeps nvCrypto.F nvMlKem).encodeState nvPbB1

theorem spqr_recv_v1_none_key
    (D : CryptoVerification.LibsignalSpqrV1.SpqrApiDeps)
    (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    (stateBytes msgBytes rem : HwBytes)
    (idx : BitVec 32)
    (pb : D.V1StatePB)
    (optChain : Option CryptoVerification.LibsignalSpqrV1.ChainPB)
    (vn : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB)
    (sckaMsg : D.MessageV1)
    (st0 st1 : D.States)
    (ch0 ch2 : CryptoVerification.LibsignalSpqrV1.Chain)
    (msgKey : HwBytes)
    (hpre : CryptoVerification.LibsignalSpqrV1.msgPreamble msgBytes =
      .ok { version := 1#8, epoch := 1#64, index := idx, remaining := rem })
    (hdec : CryptoVerification.LibsignalSpqrV1.decodeState D stateBytes =
      .ok { inner := some pb, versionNegotiation := some vn, chain := optChain })
    (hvn : vn.minVersion = 1#32)
    (hdeser : D.msgDeserialize 1#64 rem = .ok sckaMsg)
    (hfrom : D.statesFromPb pb = .ok st0)
    (hrecv : D.statesRecv st0 sckaMsg = .ok (none, st1))
    (hchFrom : CryptoVerification.LibsignalSpqrV1.chainFrom hkdf optChain (some vn) = .ok ch0)
    (hchRecv : ch0.recvKey hkdf (1#64 - 1#64) idx = .ok (ch2, msgKey))
    (hne : msgKey.isEmpty = false) :
    CryptoVerification.LibsignalSpqrV1.recv D hkdf stateBytes msgBytes =
      .ok { state := D.encodeState
              { inner := some (D.statesIntoPb st1)
                versionNegotiation := none
                chain := some ch2.intoPb }
            key := some msgKey } := by
  cases D
  cases vn
  dsimp only at *
  subst hvn
  unfold CryptoVerification.LibsignalSpqrV1.recv
  rw [hpre]
  simp only [CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
    CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    hdec,
    CryptoVerification.LibsignalSpqrV1.stateVersion,
    CryptoVerification.LibsignalSpqrV1.Version.toU8,
    show ¬ ((1#8 : BitVec 8) < (1#32 : BitVec 32).truncate 8) from (fun h => nomatch h),
    show (((1#8 : BitVec 8) != 1#8) && !true) = false from rfl,
    show ((1#8 : BitVec 8) == 0#8) = false from rfl,
    show ¬ ((1#8 : BitVec 8) > 1#8) from (fun h => nomatch h),
    show ((1#8 : BitVec 8) == 1#8) = true from rfl,
    hdeser, hfrom, hrecv,
    show ((1#64 : BitVec 64) == 0#64) = false from rfl,
    hchFrom, hchRecv, hne,
    Bool.false_eq_true, ↓reduceIte]

theorem nv_spqrRecv1_B :
    (pqxdhSpqrSession nvW).recv nvPqB0 nvPqMsg1 = .ok (nvPqB1, nvSalt1) ∧
    (pqxdhSpqrSession nvW).recvPanics nvPqB0 nvPqMsg1 = false := by
  let D := CryptoVerification.LibsignalSpqrV1.spqrDeps nvCrypto.F nvMlKem
  let pb0B : D.V1StatePB :=
    { innerState := some (.noHeaderReceived
        { uc := some { epoch := 1#64, auth := some nvAuth0.intoPb }
          receivingHdr := some (CryptoVerification.LibsignalSpqrV1.protoPolyDecoderToPb
            nvDec0.intoPb) }) }
  let st0B : D.States :=
    .noHeaderReceived
      { uc := { epoch := 1#64
                auth := (CryptoVerification.LibsignalSpqrV1.spqrAuthApi nvCrypto.F).from_pb
                  nvAuth0.intoPb }
        receiving_hdr := nvDec0 }
  let st1B : D.States :=
    .noHeaderReceived
      { uc := { epoch := 1#64
                auth := (CryptoVerification.LibsignalSpqrV1.spqrAuthApi nvCrypto.F).from_pb
                  nvAuth0.intoPb }
        receiving_hdr := nvDec1 }
  have hpre : CryptoVerification.LibsignalSpqrV1.msgPreamble nvPqMsg1 =
      .ok { version := 1#8, epoch := 1#64, index := nvChA1Key.2.1,
            remaining := 0x01#8 :: 0x00#8 :: List.replicate 32 0#8 } := rfl
  have hdec0 : CryptoVerification.LibsignalSpqrV1.decodeState D nvPqB0 =
      .ok { inner := some pb0B, chain := none, versionNegotiation := some nvVnB } := rfl
  have hdeser : D.msgDeserialize 1#64 (0x01#8 :: 0x00#8 :: List.replicate 32 0#8) =
      .ok { epoch := 1#64, payload := .hdr nvChunk0 } := by
    have hd0 : D.msgDeserialize 1#64 (0x01#8 :: 0x00#8 :: List.replicate 32 0#8) =
        .ok { epoch := 1#64, payload := .hdr { index := 0#16, data := ⟨List.replicate 32 0#8, rfl⟩ } } :=
      rfl
    exact hd0
  have hfrom0 : D.statesFromPb pb0B = .ok st0B := rfl
  have hrecv1 : D.statesRecv st0B { epoch := 1#64, payload := .hdr nvChunk0 } =
      .ok (none, st1B) := rfl
  have hchFrom : CryptoVerification.LibsignalSpqrV1.chainFrom
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) none (some nvVnB) =
      .ok nvChB0 := rfl
  have hchRecv : nvChB0.recvKey
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) (1#64 - 1#64) nvChA1Key.2.1 =
      .ok (nvChB1Key.1, nvChB1Key.2) := by
    change nvChB0.recvKey (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) 0#64 1#32 =
      .ok nvChB1Key
    unfold CryptoVerification.LibsignalSpqrV1.Chain.recvKey nvChB1Key stepChainRecv0
    have hep : nvChB0.epochIdx 0#64 = .ok 0 := rfl
    simp only [show (0#64 == (0#64 : BitVec 64) && 1#32 == (0#32 : BitVec 32)) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure,
      CryptoVerification.LibsignalSpqrV1.ChainResult.ofError, hep]
    have hlinksB : ∃ linkB nextBytesB,
        nvChB0.links = [linkB] ∧
        linkB.recv = { ctr := 0#32, next := nextBytesB, prev := { data := [] } } ∧
        nextBytesB.length = 32 ∧
        nvChB0.params = CryptoVerification.LibsignalSpqrV1.ChainParams.default.intoPb :=
      ⟨_, _, rfl, rfl, rfl, rfl⟩
    obtain ⟨linkB, nextBytesB, hlB, hrB, hnB, hpB⟩ := hlinksB
    simp only [hlB, List.getElem?_cons_zero, List.set, hrB, hpB]
    rw [ced_key_zero_one _ _ hnB]
  have hkeyEq : CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? (some nvChB1Key.2) =
      some nvSalt1 := rfl
  have htop : CryptoVerification.LibsignalSpqrV1.recv D
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F) nvPqB0 nvPqMsg1 =
      .ok { state := nvPqB1, key := some nvChB1Key.2 } :=
    spqr_recv_v1_none_key D (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith nvCrypto.F)
      nvPqB0 nvPqMsg1 _ nvChA1Key.2.1 pb0B none nvVnB _ st0B st1B nvChB0 nvChB1Key.1 nvChB1Key.2
      hpre hdec0 rfl hdeser hfrom0 hrecv1 hchFrom hchRecv rfl
  refine ⟨?_, ?_⟩
  · change ((CryptoVerification.LibsignalSpqrV1.spqrV1 nvCrypto.F nvMlKem).recv nvPqB0 nvPqMsg1) = _
    rw [CryptoVerification.LibsignalSpqrV1.spqrV1_eq]
    dsimp only [CryptoVerification.LibsignalSpqrV1.toSpqrModel,
      CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqr]
    rw [htop]
    dsimp only
    rw [hkeyEq]
  · change ((CryptoVerification.LibsignalSpqrV1.spqrV1 nvCrypto.F nvMlKem).recvPanics nvPqB0 nvPqMsg1) = false
    rw [CryptoVerification.LibsignalSpqrV1.spqrV1_eq]
    dsimp only [CryptoVerification.LibsignalSpqrV1.toSpqrModel,
      CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqr,
      CryptoVerification.LibsignalSpqrV1.recvPanicsB,
      CryptoVerification.LibsignalSpqrV1.recvPanicsSaltB]
    rw [htop]

def nvEphB : KeyPair := KeyPair.generate nvW.C 8#256
def nvPB : BitVec 256 × BitVec 256 :=
  Ratchet.rootKdf nvCrypto.F nvPA.1 (List.replicate 32 1#8)

def nvSB0 : SessionState HwBytes :=
  initializeRecipientSession (pqxdhSpqrSession nvW) ⟨nvIdB.publicKey⟩ ⟨nvIdA.publicKey⟩
    nvSpkB nvKey0 nvKey0 nvKey0

def nvRatchetB0 : RatchetState :=
  { rootKey := nvKey0
    senderChain := some ⟨nvSpkB, ⟨nvKey0, 0#32⟩⟩
    receiverChains := []
    previousCounter := 0#32
    maxForwardJumps := maxForwardJumps }

def nvRatchetB1 : RatchetState :=
  { rootKey := nvPB.1
    senderChain := some ⟨nvEphB, ⟨nvPB.2, 0#32⟩⟩
    receiverChains :=
      [ ⟨nvEphA.publicKey,
         some ⟨HKDF.bytesToKey32 (Ratchet.chainHmac nvCrypto.F nvPA.2 Ratchet.chainKeySeed), 1#32⟩,
         []⟩ ]
    previousCounter := 0#32
    maxForwardJumps := maxForwardJumps }

def nvSB1 : SessionState HwBytes :=
  { nvSB0 with rootKey := nvRatchetB1.rootKey
               previousCounter := nvRatchetB1.previousCounter
               senderChain := nvRatchetB1.senderChain
               receiverChains := nvRatchetB1.receiverChains
               pqRatchetState := nvPqB1
               pendingPreKey := false }

def nvXB : RecordExtras := responderRecordExtras nvStB0.me nvM1

def nvStB1 : PqParty :=
  { party := .B
    me := nvStB0.me
    peerId := some ⟨nvIdA.publicKey⟩
    session := some (nvXB, ⟨.B, nvSB1, 1, [1]⟩)
    signed := nvStB0.signed
    oneTime := []
    kyberOneTime := [(2#32, none)]
    kyberLastResort := [] }

theorem nv_step3_recvB :
    pqRecvPrekeyModel nvX nvW nvStB0 nvM1 8#256 = some (some (nvStB1, nvPt1)) := by
  have htf : SignalMessage.tryFrom protoSignalCodec nvM1.inner = .ok nvInnerMsg1 :=
    tryFrom_protoSignalCodec_new_nv nvMk1.macKey ((pqxdhSessionParams nvW).sendAddrs .A)
      nvEphA.publicKey 0#32 0#32 (aesCbcEncrypt nvCrypto.E nvMk1.cipherKey nvMk1.iv nvPt1)
      ⟨nvIdA.publicKey⟩ ⟨nvIdB.publicKey⟩ nvPqMsg1
      (by have hc : (aesCbcEncrypt nvCrypto.E nvMk1.cipherKey nvMk1.iv nvPt1).length = 16 := rfl
          omega)
      (by have hp : nvPqMsg1.length = 37 := rfl
          omega)
      (addrsE_len_lt _ .A .B)
  have hkeys : preKeysNamedBy nvStB0 nvM1 = some nvKeysB := rfl
  have hmark : markKyberUsed nvStB0 nvM1 =
      some { nvStB0 with kyberOneTime := [(2#32, none)] } := rfl
  have hdec : SessionState.tryDecryptFromRecord nvW.C (pqxdhSpqrSession nvW)
      ((pqxdhSessionParams nvW).expectedAddrs .B) nvInnerMsg1 .preKey 8#256 nvSB0 =
      (.ok nvPt1, nvSB1) := by
    unfold SessionState.tryDecryptFromRecord
    have hver : ¬ (nvSB0.version.toNat ≠ nvInnerMsg1.messageVersion.toNat) := fun h => h rfl
    simp only [hver, ↓reduceIte]
    have htakeB : Mut.exec TripleRatchet.fromSessionState nvSB0 =
        (.ok ⟨nvRatchetB0, nvPqB0, ⟨nvIdB.publicKey⟩, ⟨nvIdA.publicKey⟩⟩,
         { nvSB0 with receiverChains := [], pqRatchetState := [] }) := rfl
    let rMidB : RatchetState :=
      { rootKey := nvPB.1
        senderChain := some ⟨nvEphB, ⟨nvPB.2, 0#32⟩⟩
        receiverChains := [⟨nvEphA.publicKey, some ⟨nvPA.2, 0#32⟩, []⟩]
        previousCounter := 0#32
        maxForwardJumps := maxForwardJumps }
    let ckAfterB : ChainKey :=
      ⟨HKDF.bytesToKey32 (Ratchet.chainHmac nvCrypto.F nvPA.2 Ratchet.chainKeySeed), 1#32⟩
    have hdhStepB : Mut.exec
        (RatchetState.dhRatchetStep nvW.C nvInnerMsg1.senderRatchetKey 8#256) nvRatchetB0 =
        (.ok ⟨nvPA.2, 0#32⟩, rMidB) := rfl
    have hensB : Mut.exec
        (RatchetState.ensureReceiverChain nvW.C nvInnerMsg1.senderRatchetKey 8#256) nvRatchetB0 =
        (.ok ⟨nvPA.2, 0#32⟩, rMidB) := by
      unfold RatchetState.ensureReceiverChain
      rw [mut_exec_bind, mut_exec_get]
      dsimp only
      have hf0 : nvRatchetB0.findReceiverChainKey nvInnerMsg1.senderRatchetKey = .ok none := rfl
      rw [mut_exec_bind, mut_exec_liftE, hf0]
      exact hdhStepB
    have hidxB : rMidB.findReceiverChainIndex nvEphA.publicKey = some 0 := by
      change List.findIdx? (fun (c : ReceiverChain) => c.senderRatchetKey == nvEphA.publicKey)
        [⟨nvEphA.publicKey, some ⟨nvPA.2, 0#32⟩, []⟩] = some 0
      simp only [List.findIdx?, List.findIdx?.go, beq_self_eq_true, ↓reduceIte]
    have hsetB : Mut.exec (RatchetState.setReceiverChainKey nvEphA.publicKey ckAfterB) rMidB =
        (.ok (), nvRatchetB1) := by
      unfold RatchetState.setReceiverChainKey
      rw [mut_exec_bind, mut_exec_get]
      dsimp only
      rw [hidxB]; rfl
    have hconsB : Mut.exec
        (RatchetState.consumeMessageKey nvCrypto.F nvInnerMsg1.senderRatchetKey
          ⟨nvPA.2, 0#32⟩ nvInnerMsg1.counter .preKey) rMidB =
        (.ok (ChainKey.messageKeys nvCrypto.F ⟨nvPA.2, 0#32⟩), nvRatchetB1) := by
      have hsrk : nvInnerMsg1.senderRatchetKey = nvEphA.publicKey := rfl
      have hctr : nvInnerMsg1.counter = 0#32 := rfl
      have hnck : (⟨nvPA.2, 0#32⟩ : ChainKey).nextChainKey nvCrypto.F = .ok ckAfterB := rfl
      rw [hsrk, hctr]
      unfold RatchetState.consumeMessageKey
      have hlt0 : ¬ ((0#32 : BitVec 32) < 0#32) := fun h => nomatch h
      simp only [hlt0, ↓reduceIte]
      rw [mut_exec_bind, mut_exec_get]
      dsimp only
      have hgt0 : ¬ (rMidB.maxForwardJumps < (0#32 - 0#32 : BitVec 32).toNat) :=
        fun h => nomatch h
      simp only [hgt0, ↓reduceIte]
      have hadv0 : Mut.exec (RatchetState.advanceChain nvCrypto.F nvEphA.publicKey 0#32
          (0#32 - 0#32 : BitVec 32).toNat ⟨nvPA.2, 0#32⟩) rMidB =
          (.ok ⟨nvPA.2, 0#32⟩, rMidB) := rfl
      rw [mut_exec_bind, hadv0]
      dsimp only
      rw [mut_exec_bind, mut_exec_liftE, hnck]
      dsimp only
      rw [mut_exec_bind, hsetB]; rfl
    have hgenB :
        (ChainKey.messageKeys nvCrypto.F ⟨nvPA.2, 0#32⟩).generateKeys nvCrypto.F nvSalt1 = nvMk1 :=
      rfl
    have hmacB : nvInnerMsg1.verifyMacWithAddresses nvCrypto.F
        ((pqxdhSessionParams nvW).expectedAddrs .B) ⟨nvIdA.publicKey⟩ ⟨nvIdB.publicKey⟩ nvMk1.macKey = true :=
      verifyMacWithAddresses_new_nv _ _ _ _ _ _ _ _ _ _ (by
        have heq : ((pqxdhSessionParams nvW).expectedAddrs .B) = ((pqxdhSessionParams nvW).sendAddrs .A) := rfl
        rw [heq]
        cases ((pqxdhSessionParams nvW).sendAddrs .A) <;> simp [LibsignalAead.addressCheckPasses])
    have hcbcB : aesCbcDecrypt nvCrypto.D nvMk1.cipherKey nvMk1.iv nvInnerMsg1.ciphertext =
        some nvPt1 := rfl
    have htrDecB := mut_exec_decrypt_ok nvW.C (pqxdhSpqrSession nvW) ((pqxdhSessionParams nvW).expectedAddrs .B)
      nvInnerMsg1 .preKey 8#256 nvRatchetB0 rMidB nvRatchetB1 nvPqB0 nvPqB1
      ⟨nvIdB.publicKey⟩ ⟨nvIdA.publicKey⟩ ⟨nvPA.2, 0#32⟩
      (ChainKey.messageKeys nvCrypto.F ⟨nvPA.2, 0#32⟩) nvSalt1 nvMk1 nvPt1
      hensB hconsB nv_spqrRecv1_B.2 nv_spqrRecv1_B.1 hgenB hmacB hcbcB
    have hwsB := mut_exec_tryDecryptWithState_ok nvW.C (pqxdhSpqrSession nvW)
      ((pqxdhSessionParams nvW).expectedAddrs .B) nvInnerMsg1 .preKey 8#256 nvSB0
      { nvSB0 with receiverChains := [], pqRatchetState := [] } _ _ nvPt1 htakeB htrDecB
    conv => lhs; rw [hwsB]
    rfl
  unfold pqRecvPrekeyModel
  rw [htf]
  dsimp only
  have htrB : nvStB0.trusts ⟨⟨nvM1.idPub⟩⟩ = true := rfl
  rw [htrB]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hkeys]
  dsimp only
  have hsB0 : nvStB0.session = none := rfl
  rw [hsB0]
  dsimp only
  unfold recvPrekeyState
  rw [htf]
  have hids : ¬ (nvM1.spkId ≠ nvKeysB.spkId ∨ nvM1.kpkId ≠ nvKeysB.kpkId) := by
    rintro (h | h) <;> exact h rfl
  simp only [hids, ↓reduceIte]
  rw [nv_acceptKeys]
  dsimp only
  have hinitRec :
      initializeRecipientSession (pqxdhSpqrSession nvW)
        ⟨(keyPairOf nvW.C nvStB0.me.idPriv).publicKey⟩ ⟨⟨nvM1.idPub⟩⟩
        (keyPairOf nvW.C nvKeysB.spkPriv)
        (HKDF.bytesToKey32 (ofU8 nvDk.rootKey))
        (HKDF.bytesToKey32 (ofU8 nvDk.chainKey))
        (HKDF.bytesToKey32 (ofU8 nvDk.pqrKey)) = nvSB0 := rfl
  have hpB : nvStB0.party = .B := rfl
  rw [hpB, hinitRec, hdec]
  dsimp only
  rw [hmark]
  rfl

/-! ## Step 4: `pqSendModel` Whisper on Bob -/

def nvSpqrSend2Res : HwBytes × Option (List.Vector (BitVec 8) 32) × HwBytes :=
  match (pqxdhSpqrSession nvW).send nvPqB1 nvCoins64B with
  | some r => r
  | none => ([], none, [])

def nvPqB2 : HwBytes := nvSpqrSend2Res.1
def nvSalt2 : Option (List.Vector (BitVec 8) 32) := nvSpqrSend2Res.2.1
def nvPqMsg2 : HwBytes := nvSpqrSend2Res.2.2

def nvMk2 : MessageKeys :=
  ((⟨nvPB.2, 0#32⟩ : ChainKey).messageKeys nvCrypto.F).generateKeys nvCrypto.F nvSalt2

def nvInnerMsg2 : SignalMessage :=
  SignalMessage.new nvCrypto.F protoSignalCodec currentVersion nvMk2.macKey
    none nvEphB.publicKey 0#32 0#32
    (aesCbcEncrypt nvCrypto.E nvMk2.cipherKey nvMk2.iv nvPt2)
    ⟨nvIdB.publicKey⟩ ⟨nvIdA.publicKey⟩ nvPqMsg2

def nvBody2 : HwBytes := nvInnerMsg2.serialized
def nvWire2 : HwBytes := wireWhisper :: nvBody2

def nvSB2 : SessionState HwBytes :=
  match SessionState.messageEncrypt nvW.C protoSignalCodec (pqxdhSpqrSession nvW)
      ((pqxdhSessionParams nvW).sendAddrs .B) nvPt2 nvCoins64B nvSB1 with
  | (.ok _, s) => s
  | (.error _, s) => s

def nvStB2 : PqParty :=
  { nvStB1 with peerId := some ⟨nvIdA.publicKey⟩, session := some (nvXB, ⟨.B, nvSB2, 1, [1]⟩) }

theorem nv_step4_sendB :
    pqSendModel nvW nvStB1 nvPt2 nvCoins64B = some (some (nvStB2, nvWire2)) := rfl

end Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
