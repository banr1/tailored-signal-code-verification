/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink

/-!
# Bridge Between `Initiator` Protocol Model and `SignalPqxdh` Specifications

Equivalences and type conversions connecting the `Initiator.*` protocol model (`HandshakeDerive`)
under `ResponderCore.ofSignalPqxdhPrimitives` with `SignalPqxdh.*`:
- Lifts `SignalPqxdh.WellFormedPrimitives` to `Initiator.StructuralPrims` and discharges
  `StructuralPrims (initiatorModelPrims X W)` unconditionally.
- Establishes definitional and extensional agreement of the reference primitives and `Model.initiate*`
  / `Model.accept*` transitions.
- Proves `WellSized*` preservation and unconditional well-sizedness of `initiateInput` and
  `acceptInput`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.Initiator

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderCore

/-! ## 1. Pure Byte & Encoding Definitional Equalities (`Initiator.* = SignalPqxdh.*`) -/

@[simp] theorem INFO_PQXDH_eq : INFO_PQXDH = SignalPqxdh.INFO_PQXDH := rfl
@[simp] theorem INFO_RATCHET_eq : INFO_RATCHET = SignalPqxdh.INFO_RATCHET := rfl
@[simp] theorem INFO_MSG_KEYS_eq : INFO_MSG_KEYS = SignalPqxdh.INFO_MSG_KEYS := rfl
@[simp] theorem F_X25519_eq : F_X25519 = SignalPqxdh.F_X25519 := rfl

@[simp] theorem encodeEC_eq (pk32 : Bytes) : encodeEC pk32 = SignalPqxdh.encodeEC pk32 := rfl
@[simp] theorem encodeKEM_eq (pk1568 : Bytes) :
    encodeKEM pk1568 = SignalPqxdh.encodeKEM pk1568 := rfl
@[simp] theorem decodeEC_eq (bs : Bytes) : decodeEC bs = SignalPqxdh.decodeEC bs := rfl
@[simp] theorem decodeKEM_eq (bs : Bytes) : decodeKEM bs = SignalPqxdh.decodeKEM bs := rfl

@[simp] theorem buildSecrets_eq (dh1 dh2 dh3 : Bytes) (dh4? : Option Bytes) (ss : Bytes) :
    buildSecrets dh1 dh2 dh3 dh4? ss = SignalPqxdh.buildSecrets dh1 dh2 dh3 dh4? ss := rfl

@[simp] theorem firstMsgAD_eq (ikA ikB ephAPk pqRatchetMsg : Bytes) :
    firstMsgAD ikA ikB ephAPk pqRatchetMsg =
      SignalPqxdh.firstMsgAD ikA ikB ephAPk pqRatchetMsg := rfl

@[simp] theorem dhOptNonZero_eq (dh? : Option Bytes) :
    dhOptNonZero dh? = SignalPqxdh.dhOptNonZero dh? := rfl

@[simp] theorem scalarIsInRange_eq (pk : Bytes) :
    scalarIsInRange pk = SignalPqxdh.scalarIsInRange pk := rfl

@[simp] theorem fitBytesRef_eq (n : Nat) (bs : Bytes) :
    fitBytesRef n bs = SignalPqxdh.fitBytesRef n bs := rfl

@[simp] theorem fitBytes_eq (n : Nat) (bs : Bytes) :
    fitBytes n bs = SignalPqxdh.fitBytes n bs := rfl

@[simp] theorem clampScalar25519_eq (sk : Bytes) :
    clampScalar25519 sk = SignalPqxdh.clampScalar25519 sk := rfl

@[simp] theorem sha256InitState_eq : sha256InitState = SignalPqxdh.sha256InitState := rfl
@[simp] theorem sha512InitState_eq : sha512InitState = SignalPqxdh.sha512InitState := rfl

@[simp] theorem encodeBitLen64BE_eq (byteLen : Nat) :
    encodeBitLen64BE byteLen = SignalPqxdh.encodeBitLen64BE byteLen := rfl

@[simp] theorem encodeBitLen128BE_eq (byteLen : Nat) :
    encodeBitLen128BE byteLen = SignalPqxdh.encodeBitLen128BE byteLen := rfl

@[simp] theorem sha256Pad_eq (msg : Bytes) : sha256Pad msg = SignalPqxdh.sha256Pad msg := rfl
@[simp] theorem sha512Pad_eq (msg : Bytes) : sha512Pad msg = SignalPqxdh.sha512Pad msg := rfl

@[simp] theorem chunkBlocks_eq (blockSize : Nat) (bs : Bytes) :
    chunkBlocks blockSize bs = SignalPqxdh.chunkBlocks blockSize bs := rfl

@[simp] theorem xorBytes_eq (a b : Bytes) : xorBytes a b = SignalPqxdh.xorBytes a b := rfl
@[simp] theorem pkcs7Pad16_eq (pt : Bytes) : pkcs7Pad16 pt = SignalPqxdh.pkcs7Pad16 pt := rfl
@[simp] theorem pkcs7Unpad16_eq (padded : Bytes) :
    pkcs7Unpad16 padded = SignalPqxdh.pkcs7Unpad16 padded := rfl

@[simp] theorem toBlocks16_eq (bs : Bytes) : toBlocks16 bs = SignalPqxdh.toBlocks16 bs := by
  induction bs using toBlocks16.induct with
  | case1 bs hge ih =>
    rw [toBlocks16, SignalPqxdh.toBlocks16]
    simp [hge, ih]
  | case2 bs hlt =>
    rw [toBlocks16, SignalPqxdh.toBlocks16]
    simp [hlt]

@[simp] theorem fromBlocks16_eq (blks : List Bytes) :
    fromBlocks16 blks = SignalPqxdh.fromBlocks16 blks := rfl

@[simp] theorem cbcEncBlocksWith_eq (aesEnc : Bytes → Bytes → Bytes) (key iv : Bytes)
    (blks : List Bytes) :
    cbcEncBlocksWith aesEnc key iv blks = SignalPqxdh.cbcEncBlocksWith aesEnc key iv blks := by
  induction blks generalizing iv with
  | nil => rfl
  | cons ptBlk rest ih =>
    simp only [cbcEncBlocksWith, SignalPqxdh.cbcEncBlocksWith, fitBytesRef_eq, xorBytes_eq, ih]

@[simp] theorem cbcDecBlocksWith_eq (aesDec : Bytes → Bytes → Bytes) (key iv : Bytes)
    (blks : List Bytes) :
    cbcDecBlocksWith aesDec key iv blks = SignalPqxdh.cbcDecBlocksWith aesDec key iv blks := by
  induction blks generalizing iv with
  | nil => rfl
  | cons ctBlk rest ih =>
    simp only [cbcDecBlocksWith, SignalPqxdh.cbcDecBlocksWith, fitBytesRef_eq, xorBytes_eq, ih]

/-! ## 2. Structure Conversions (`Initiator.* ↔ SignalPqxdh.*`) -/

def ofSignalPqxdhDRKey (dk : SignalPqxdh.DRKey) : DRKey :=
  ⟨dk.rootKey, dk.chainKey, dk.pqrKey⟩

def toSignalPqxdhDRKey (dk : DRKey) : SignalPqxdh.DRKey :=
  ⟨dk.rootKey, dk.chainKey, dk.pqrKey⟩

@[simp] theorem toSignalPqxdhDRKey_ofSignalPqxdhDRKey (dk : SignalPqxdh.DRKey) :
    toSignalPqxdhDRKey (ofSignalPqxdhDRKey dk) = dk := by
  cases dk; rfl

@[simp] theorem ofSignalPqxdhDRKey_toSignalPqxdhDRKey (dk : DRKey) :
    ofSignalPqxdhDRKey (toSignalPqxdhDRKey dk) = dk := by
  cases dk; rfl

@[simp] theorem ofSignalPqxdhDRKey_toBytes96 (dk : SignalPqxdh.DRKey) :
    DRKey.toBytes96 (ofSignalPqxdhDRKey dk) = dk.toBytes96 := rfl

def ofSignalPqxdhMessageKeys (mk : SignalPqxdh.MessageKeys) : MessageKeys :=
  ⟨mk.cipherKey, mk.macKey, mk.iv⟩

def toSignalPqxdhMessageKeys (mk : MessageKeys) : SignalPqxdh.MessageKeys :=
  ⟨mk.cipherKey, mk.macKey, mk.iv⟩

@[simp] theorem toSignalPqxdhMessageKeys_ofSignalPqxdhMessageKeys (mk : SignalPqxdh.MessageKeys) :
    toSignalPqxdhMessageKeys (ofSignalPqxdhMessageKeys mk) = mk := by
  cases mk; rfl

@[simp] theorem ofSignalPqxdhMessageKeys_toSignalPqxdhMessageKeys (mk : MessageKeys) :
    ofSignalPqxdhMessageKeys (toSignalPqxdhMessageKeys mk) = mk := by
  cases mk; rfl

def ofSignalPqxdhBundle (b : SignalPqxdh.PreKeyBundleInput) : PreKeyBundleInput where
  ikB      := b.ikB
  spkId    := b.spkId
  spkB     := b.spkB
  spkSig   := b.spkSig
  opkB?    := b.opkB?
  pqspkId  := b.pqspkId
  pqspkB   := b.pqspkB
  pqspkSig := b.pqspkSig

def toSignalPqxdhBundle (b : PreKeyBundleInput) : SignalPqxdh.PreKeyBundleInput where
  ikB      := b.ikB
  spkId    := b.spkId
  spkB     := b.spkB
  spkSig   := b.spkSig
  opkB?    := b.opkB?
  pqspkId  := b.pqspkId
  pqspkB   := b.pqspkB
  pqspkSig := b.pqspkSig

@[simp] theorem toSignalPqxdhBundle_ofSignalPqxdhBundle (b : SignalPqxdh.PreKeyBundleInput) :
    toSignalPqxdhBundle (ofSignalPqxdhBundle b) = b := by
  cases b; rfl

@[simp] theorem ofSignalPqxdhBundle_toSignalPqxdhBundle (b : PreKeyBundleInput) :
    ofSignalPqxdhBundle (toSignalPqxdhBundle b) = b := by
  cases b; rfl

def ofSignalPqxdhHdr (h : SignalPqxdh.HandshakeHdr) : HandshakeHdr where
  ikAPk   := h.ikAPk
  ekAPk   := h.ekAPk
  spkId   := h.spkId
  opkId?  := h.opkId?
  pqspkId := h.pqspkId
  kemCt   := h.kemCt

def toSignalPqxdhHdr (h : HandshakeHdr) : SignalPqxdh.HandshakeHdr where
  ikAPk   := h.ikAPk
  ekAPk   := h.ekAPk
  spkId   := h.spkId
  opkId?  := h.opkId?
  pqspkId := h.pqspkId
  kemCt   := h.kemCt

@[simp] theorem toSignalPqxdhHdr_ofSignalPqxdhHdr (h : SignalPqxdh.HandshakeHdr) :
    toSignalPqxdhHdr (ofSignalPqxdhHdr h) = h := by
  cases h; rfl

@[simp] theorem ofSignalPqxdhHdr_toSignalPqxdhHdr (h : HandshakeHdr) :
    ofSignalPqxdhHdr (toSignalPqxdhHdr h) = h := by
  cases h; rfl

def ofSignalPqxdhPreKeyMsg (m : SignalPqxdh.PreKeyMsg) : PreKeyMsg where
  hdr          := ofSignalPqxdhHdr m.hdr
  ephAPk       := m.ephAPk
  pqRatchetMsg := m.pqRatchetMsg
  aeadCt       := m.aeadCt

def toSignalPqxdhPreKeyMsg (m : PreKeyMsg) : SignalPqxdh.PreKeyMsg where
  hdr          := toSignalPqxdhHdr m.hdr
  ephAPk       := m.ephAPk
  pqRatchetMsg := m.pqRatchetMsg
  aeadCt       := m.aeadCt

@[simp] theorem toSignalPqxdhPreKeyMsg_ofSignalPqxdhPreKeyMsg (m : SignalPqxdh.PreKeyMsg) :
    toSignalPqxdhPreKeyMsg (ofSignalPqxdhPreKeyMsg m) = m := by
  cases m; simp [toSignalPqxdhPreKeyMsg, ofSignalPqxdhPreKeyMsg]

@[simp] theorem ofSignalPqxdhPreKeyMsg_toSignalPqxdhPreKeyMsg (m : PreKeyMsg) :
    ofSignalPqxdhPreKeyMsg (toSignalPqxdhPreKeyMsg m) = m := by
  cases m; simp [toSignalPqxdhPreKeyMsg, ofSignalPqxdhPreKeyMsg]

def ofSignalPqxdhInitiateKeysInput (inp : SignalPqxdh.InitiateKeysInput) : InitiateKeysInput where
  ikASk       := inp.ikASk
  ikAPk       := inp.ikAPk
  ekASk       := inp.ekASk
  kemCoins    := inp.kemCoins
  trustedPeer := inp.trustedPeer
  bundle      := ofSignalPqxdhBundle inp.bundle

def toSignalPqxdhInitiateKeysInput (inp : InitiateKeysInput) : SignalPqxdh.InitiateKeysInput where
  ikASk       := inp.ikASk
  ikAPk       := inp.ikAPk
  ekASk       := inp.ekASk
  kemCoins    := inp.kemCoins
  trustedPeer := inp.trustedPeer
  bundle      := toSignalPqxdhBundle inp.bundle

@[simp] theorem toSignalPqxdhInitiateKeysInput_ofSignalPqxdhInitiateKeysInput
    (inp : SignalPqxdh.InitiateKeysInput) :
    toSignalPqxdhInitiateKeysInput (ofSignalPqxdhInitiateKeysInput inp) = inp := by
  cases inp; simp [toSignalPqxdhInitiateKeysInput, ofSignalPqxdhInitiateKeysInput]

@[simp] theorem ofSignalPqxdhInitiateKeysInput_toSignalPqxdhInitiateKeysInput
    (inp : InitiateKeysInput) :
    ofSignalPqxdhInitiateKeysInput (toSignalPqxdhInitiateKeysInput inp) = inp := by
  cases inp; simp [toSignalPqxdhInitiateKeysInput, ofSignalPqxdhInitiateKeysInput]

def ofSignalPqxdhInitiateInput (inp : SignalPqxdh.InitiateInput) : InitiateInput where
  toInitiateKeysInput := ofSignalPqxdhInitiateKeysInput inp.toInitiateKeysInput
  ephASk              := inp.ephASk
  spqrCoins           := inp.spqrCoins
  plaintext           := inp.plaintext

def toSignalPqxdhInitiateInput (inp : InitiateInput) : SignalPqxdh.InitiateInput where
  toInitiateKeysInput := toSignalPqxdhInitiateKeysInput inp.toInitiateKeysInput
  ephASk              := inp.ephASk
  spqrCoins           := inp.spqrCoins
  plaintext           := inp.plaintext

@[simp] theorem toSignalPqxdhInitiateInput_ofSignalPqxdhInitiateInput
    (inp : SignalPqxdh.InitiateInput) :
    toSignalPqxdhInitiateInput (ofSignalPqxdhInitiateInput inp) = inp := by
  cases inp; simp [toSignalPqxdhInitiateInput, ofSignalPqxdhInitiateInput]

@[simp] theorem ofSignalPqxdhInitiateInput_toSignalPqxdhInitiateInput
    (inp : InitiateInput) :
    ofSignalPqxdhInitiateInput (toSignalPqxdhInitiateInput inp) = inp := by
  cases inp; simp [toSignalPqxdhInitiateInput, ofSignalPqxdhInitiateInput]

def ofSignalPqxdhAcceptKeysInput (inp : SignalPqxdh.AcceptKeysInput) : AcceptKeysInput where
  ikBSk       := inp.ikBSk
  ikBPk       := inp.ikBPk
  spkBSk      := inp.spkBSk
  spkBPk      := inp.spkBPk
  opkBSk?     := inp.opkBSk?
  pqspkBSk    := inp.pqspkBSk
  pqspkBPk    := inp.pqspkBPk
  trustedPeer := inp.trustedPeer
  replayOk    := inp.replayOk
  hdr         := ofSignalPqxdhHdr inp.hdr

def toSignalPqxdhAcceptKeysInput (inp : AcceptKeysInput) : SignalPqxdh.AcceptKeysInput where
  ikBSk       := inp.ikBSk
  ikBPk       := inp.ikBPk
  spkBSk      := inp.spkBSk
  spkBPk      := inp.spkBPk
  opkBSk?     := inp.opkBSk?
  pqspkBSk    := inp.pqspkBSk
  pqspkBPk    := inp.pqspkBPk
  trustedPeer := inp.trustedPeer
  replayOk    := inp.replayOk
  hdr         := toSignalPqxdhHdr inp.hdr

@[simp] theorem toSignalPqxdhAcceptKeysInput_ofSignalPqxdhAcceptKeysInput
    (inp : SignalPqxdh.AcceptKeysInput) :
    toSignalPqxdhAcceptKeysInput (ofSignalPqxdhAcceptKeysInput inp) = inp := by
  cases inp; simp [toSignalPqxdhAcceptKeysInput, ofSignalPqxdhAcceptKeysInput]

@[simp] theorem ofSignalPqxdhAcceptKeysInput_toSignalPqxdhAcceptKeysInput
    (inp : AcceptKeysInput) :
    ofSignalPqxdhAcceptKeysInput (toSignalPqxdhAcceptKeysInput inp) = inp := by
  cases inp; simp [toSignalPqxdhAcceptKeysInput, ofSignalPqxdhAcceptKeysInput]

def ofSignalPqxdhAcceptInput (inp : SignalPqxdh.AcceptInput) : AcceptInput where
  keysInp := ofSignalPqxdhAcceptKeysInput inp.keysInp
  msg     := ofSignalPqxdhPreKeyMsg inp.msg

def toSignalPqxdhAcceptInput (inp : AcceptInput) : SignalPqxdh.AcceptInput where
  keysInp := toSignalPqxdhAcceptKeysInput inp.keysInp
  msg     := toSignalPqxdhPreKeyMsg inp.msg

@[simp] theorem toSignalPqxdhAcceptInput_ofSignalPqxdhAcceptInput
    (inp : SignalPqxdh.AcceptInput) :
    toSignalPqxdhAcceptInput (ofSignalPqxdhAcceptInput inp) = inp := by
  cases inp; simp [toSignalPqxdhAcceptInput, ofSignalPqxdhAcceptInput]

@[simp] theorem ofSignalPqxdhAcceptInput_toSignalPqxdhAcceptInput
    (inp : AcceptInput) :
    ofSignalPqxdhAcceptInput (toSignalPqxdhAcceptInput inp) = inp := by
  cases inp; simp [toSignalPqxdhAcceptInput, ofSignalPqxdhAcceptInput]

/-! ## 3. Reference & Primitive Function Bridges (`ofSignalPqxdhPrimitives P`) -/

@[simp] theorem sha256Step_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) :
    sha256Step (ofSignalPqxdhPrimitives P) = SignalPqxdh.sha256Step P := rfl

@[simp] theorem sha512Step_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) :
    sha512Step (ofSignalPqxdhPrimitives P) = SignalPqxdh.sha512Step P := rfl

@[simp] theorem sha256Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (msg : Bytes) :
    sha256Ref (ofSignalPqxdhPrimitives P) msg = SignalPqxdh.sha256Ref P msg := rfl

@[simp] theorem sha512Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (msg : Bytes) :
    sha512Ref (ofSignalPqxdhPrimitives P) msg = SignalPqxdh.sha512Ref P msg := rfl

@[simp] theorem hmacSha256Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key msg : Bytes) :
    hmacSha256Ref (ofSignalPqxdhPrimitives P) key msg =
      SignalPqxdh.hmacSha256Ref P key msg := rfl

@[simp] theorem hkdfExtractRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (salt? : Option Bytes) (ikm : Bytes) :
    hkdfExtractRef (ofSignalPqxdhPrimitives P) salt? ikm =
      SignalPqxdh.hkdfExtractRef P salt? ikm := rfl

@[simp] theorem hkdfExpand96Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (prk info : Bytes) :
    hkdfExpand96Ref (ofSignalPqxdhPrimitives P) prk info =
      ofSignalPqxdhDRKey (SignalPqxdh.hkdfExpand96Ref P prk info) := rfl

@[simp] theorem hkdfDerive96Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (secrets : Bytes) :
    hkdfDerive96Ref (ofSignalPqxdhPrimitives P) secrets =
      ofSignalPqxdhDRKey (SignalPqxdh.hkdfDerive96Ref P secrets) := rfl

@[simp] theorem hkdfDerive96_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (secrets : Bytes) :
    (ofSignalPqxdhPrimitives P).hkdfDerive96 secrets =
      ofSignalPqxdhDRKey (P.hkdfDerive96 secrets) := rfl

@[simp] theorem rootCreateChainRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (rk dhRatchet : Bytes) :
    rootCreateChainRef (ofSignalPqxdhPrimitives P) rk dhRatchet =
      SignalPqxdh.rootCreateChainRef P rk dhRatchet := rfl

@[simp] theorem rootCreateChain_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (rk dhRatchet : Bytes) :
    (ofSignalPqxdhPrimitives P).rootCreateChain rk dhRatchet =
      P.rootCreateChain rk dhRatchet := rfl

@[simp] theorem chainKdfSeedRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (ck : Bytes) :
    chainKdfSeedRef (ofSignalPqxdhPrimitives P) ck = SignalPqxdh.chainKdfSeedRef P ck := rfl

@[simp] theorem chainKdfSeed_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (ck : Bytes) :
    (ofSignalPqxdhPrimitives P).chainKdfSeed ck = P.chainKdfSeed ck := rfl

@[simp] theorem chainKdfNextRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (ck : Bytes) :
    chainKdfNextRef (ofSignalPqxdhPrimitives P) ck = SignalPqxdh.chainKdfNextRef P ck := rfl

@[simp] theorem chainKdfNext_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (ck : Bytes) :
    (ofSignalPqxdhPrimitives P).chainKdfNext ck = P.chainKdfNext ck := rfl

@[simp] theorem deriveMsgKeysRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mkSeed : Bytes) (spqrSalt? : Option Bytes) :
    deriveMsgKeysRef (ofSignalPqxdhPrimitives P) mkSeed spqrSalt? =
      ofSignalPqxdhMessageKeys (SignalPqxdh.deriveMsgKeysRef P mkSeed spqrSalt?) := rfl

@[simp] theorem deriveMsgKeys_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mkSeed : Bytes) (spqrSalt? : Option Bytes) :
    (ofSignalPqxdhPrimitives P).deriveMsgKeys mkSeed spqrSalt? =
      ofSignalPqxdhMessageKeys (P.deriveMsgKeys mkSeed spqrSalt?) := rfl

@[simp] theorem cbcEncBlocks_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key iv : Bytes) (blks : List Bytes) :
    cbcEncBlocks (ofSignalPqxdhPrimitives P) key iv blks =
      SignalPqxdh.cbcEncBlocks P key iv blks :=
  cbcEncBlocksWith_eq P.aesEncBlock key iv blks

@[simp] theorem cbcDecBlocks_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key iv : Bytes) (blks : List Bytes) :
    cbcDecBlocks (ofSignalPqxdhPrimitives P) key iv blks =
      SignalPqxdh.cbcDecBlocks P key iv blks :=
  cbcDecBlocksWith_eq P.aesDecBlock key iv blks

@[simp] theorem aes256CbcEncRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key iv pt : Bytes) :
    aes256CbcEncRef (ofSignalPqxdhPrimitives P) key iv pt =
      SignalPqxdh.aes256CbcEncRef P key iv pt := by
  simp [aes256CbcEncRef, SignalPqxdh.aes256CbcEncRef, cbcEncBlocks, SignalPqxdh.cbcEncBlocks,
    ofSignalPqxdhPrimitives]

@[simp] theorem aes256CbcDecRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key iv ct : Bytes) :
    aes256CbcDecRef (ofSignalPqxdhPrimitives P) key iv ct =
      SignalPqxdh.aes256CbcDecRef P key iv ct := by
  simp [aes256CbcDecRef, SignalPqxdh.aes256CbcDecRef, cbcDecBlocks, SignalPqxdh.cbcDecBlocks,
    ofSignalPqxdhPrimitives]

@[simp] theorem aes256CbcHmacEncRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mk : MessageKeys) (ad pt : Bytes) :
    aes256CbcHmacEncRef (ofSignalPqxdhPrimitives P) mk ad pt =
      SignalPqxdh.aes256CbcHmacEncRef P (toSignalPqxdhMessageKeys mk) ad pt := by
  simp [aes256CbcHmacEncRef, SignalPqxdh.aes256CbcHmacEncRef, toSignalPqxdhMessageKeys]

@[simp] theorem aes256CbcHmacDecRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mk : MessageKeys) (ad ctAndTag : Bytes) :
    aes256CbcHmacDecRef (ofSignalPqxdhPrimitives P) mk ad ctAndTag =
      SignalPqxdh.aes256CbcHmacDecRef P (toSignalPqxdhMessageKeys mk) ad ctAndTag := by
  simp [aes256CbcHmacDecRef, SignalPqxdh.aes256CbcHmacDecRef, toSignalPqxdhMessageKeys]

@[simp] theorem aeadEnc_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mk : MessageKeys) (ad pt : Bytes) :
    (ofSignalPqxdhPrimitives P).aeadEnc mk ad pt =
      P.aeadEnc (toSignalPqxdhMessageKeys mk) ad pt := rfl

@[simp] theorem aeadDec_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mk : MessageKeys) (ad ct : Bytes) :
    (ofSignalPqxdhPrimitives P).aeadDec mk ad ct =
      P.aeadDec (toSignalPqxdhMessageKeys mk) ad ct := rfl

@[simp] theorem xeddsaVerifyRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (pk m sig : Bytes) :
    xeddsaVerifyRef (ofSignalPqxdhPrimitives P) pk m sig =
      SignalPqxdh.xeddsaVerifyRef P pk m sig := rfl

@[simp] theorem isCanonicalRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (pk : Bytes) :
    isCanonicalRef (ofSignalPqxdhPrimitives P) pk =
      SignalPqxdh.isCanonicalRef P pk := rfl

/-! ## 4. Protocol Model Function Bridges (`Model.initiateKeys`, `Model.acceptKeys`,
  `Model.initiate`, `Model.accept`) -/

@[simp] private theorem option_map_bind' {α β γ : Type _}
    (x : Option α) (g : α → Option β) (f : β → γ) :
    Option.map f (x >>= g) = x >>= (fun a => Option.map f (g a)) := by
  cases x <;> rfl

@[simp] private theorem option_map_option_bind {α β γ : Type _}
    (x : Option α) (g : α → Option β) (f : β → γ) :
    Option.map f (Option.bind x g) = Option.bind x (fun a => Option.map f (g a)) := by
  cases x <;> rfl

theorem Model.initiateKeys_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (inp : SignalPqxdh.InitiateKeysInput) :
    Model.initiateKeys (ofSignalPqxdhPrimitives P) (ofSignalPqxdhInitiateKeysInput inp) =
      (SignalPqxdh.Model.initiateKeys P inp).map
        (fun (dk, hdr) => (ofSignalPqxdhDRKey dk, ofSignalPqxdhHdr hdr)) := by
  unfold Model.initiateKeys SignalPqxdh.Model.initiateKeys
  dsimp only [ofSignalPqxdhPrimitives, ofSignalPqxdhInitiateKeysInput, ofSignalPqxdhBundle,
    encodeEC_eq, encodeKEM_eq, dhOptNonZero_eq, buildSecrets_eq]
  rcases hkem : P.kemEncaps inp.bundle.pqspkB inp.kemCoins with _ | ⟨ss, kemCt⟩ <;>
    (simp [hkem, «guard», _root_.guard, bind, Function.comp_def, ofSignalPqxdhDRKey,
      ofSignalPqxdhHdr]; try rfl)

theorem Model.initiateKeys_toSignalPqxdhInitiateKeysInput (P : SignalPqxdh.Primitives)
    (inp : InitiateKeysInput) :
    Model.initiateKeys (ofSignalPqxdhPrimitives P) inp =
      (SignalPqxdh.Model.initiateKeys P (toSignalPqxdhInitiateKeysInput inp)).map
        (fun (dk, hdr) => (ofSignalPqxdhDRKey dk, ofSignalPqxdhHdr hdr)) := by
  have h := Model.initiateKeys_ofSignalPqxdhPrimitives P (toSignalPqxdhInitiateKeysInput inp)
  rwa [ofSignalPqxdhInitiateKeysInput_toSignalPqxdhInitiateKeysInput] at h

/-- Typeclass witnessing that `P.kemDecaps` returns `none` outside `kyberCtLen` or `inp.hdr.kemCt`
    already has length `kyberCtLen` (satisfied automatically at `modelPrims X W` and at
    `acceptInput W me k m`). -/
class AcceptKeysGuard (P : SignalPqxdh.Primitives) (inp : SignalPqxdh.AcceptKeysInput) : Prop where
  guard_ok : inp.hdr.kemCt.length = SignalPqxdh.kyberCtLen ∨
    P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = none

instance acceptKeysGuard_modelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (inp : SignalPqxdh.AcceptKeysInput) :
    AcceptKeysGuard (modelPrims X W) inp where
  guard_ok := by
    by_cases h : inp.hdr.kemCt.length = SignalPqxdh.kyberCtLen
    · exact Or.inl h
    · exact Or.inr (by simp [modelPrims, blockLevelPrims, h])

instance acceptKeysGuard_acceptInput (P : SignalPqxdh.Primitives)
    (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) :
    AcceptKeysGuard P (CryptoVerification.E2E.acceptInput W me k m) where
  guard_ok := Or.inl (by
    simp [CryptoVerification.E2E.acceptInput, e2e_vecU8_length, SignalPqxdh.kyberCtLen])

theorem Model.acceptKeys_ofSignalPqxdhPrimitives_of_guard (P : SignalPqxdh.Primitives)
    (inp : SignalPqxdh.AcceptKeysInput)
    (hg : inp.hdr.kemCt.length = SignalPqxdh.kyberCtLen ∨
      P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = none) :
    Model.acceptKeys (ofSignalPqxdhPrimitives P) (ofSignalPqxdhAcceptKeysInput inp) =
      (SignalPqxdh.Model.acceptKeys P inp).map ofSignalPqxdhDRKey := by
  unfold Model.acceptKeys SignalPqxdh.Model.acceptKeys
  dsimp only [ofSignalPqxdhPrimitives, ofSignalPqxdhAcceptKeysInput, ofSignalPqxdhHdr,
    dhOptNonZero_eq, buildSecrets_eq]
  rcases hg with hlen | hnone
  · have hbeq : (inp.hdr.kemCt.length == SignalPqxdh.kyberCtLen) = true := beq_iff_eq.mpr hlen
    rcases inp.hdr.opkId? with _ | opkId <;>
      rcases inp.opkBSk? with _ | opkSk <;>
      rcases P.kemDecaps inp.pqspkBSk inp.hdr.kemCt with _ | ss <;>
      (simp [hbeq, «guard», _root_.guard, bind, Function.comp_def, ofSignalPqxdhDRKey]; try rfl)
  · by_cases hlen : inp.hdr.kemCt.length = SignalPqxdh.kyberCtLen
    · have hbeq : (inp.hdr.kemCt.length == SignalPqxdh.kyberCtLen) = true := beq_iff_eq.mpr hlen
      rcases inp.hdr.opkId? with _ | opkId <;>
        rcases inp.opkBSk? with _ | opkSk <;>
        (simp [hbeq, hnone, «guard», _root_.guard, bind, Function.comp_def, ofSignalPqxdhDRKey]; try rfl)
    · have hbeq : (inp.hdr.kemCt.length == SignalPqxdh.kyberCtLen) = false :=
        beq_eq_false_iff_ne.mpr hlen
      rcases inp.hdr.opkId? with _ | opkId <;>
        rcases inp.opkBSk? with _ | opkSk <;>
        (simp [hbeq, hnone, «guard», _root_.guard, bind, Function.comp_def, ofSignalPqxdhDRKey]; try rfl)

theorem Model.acceptKeys_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (inp : SignalPqxdh.AcceptKeysInput) [hG : AcceptKeysGuard P inp] :
    Model.acceptKeys (ofSignalPqxdhPrimitives P) (ofSignalPqxdhAcceptKeysInput inp) =
      (SignalPqxdh.Model.acceptKeys P inp).map ofSignalPqxdhDRKey :=
  Model.acceptKeys_ofSignalPqxdhPrimitives_of_guard P inp hG.guard_ok

theorem Model.acceptKeys_toSignalPqxdhAcceptKeysInput (P : SignalPqxdh.Primitives)
    (inp : AcceptKeysInput) [AcceptKeysGuard P (toSignalPqxdhAcceptKeysInput inp)] :
    Model.acceptKeys (ofSignalPqxdhPrimitives P) inp =
      (SignalPqxdh.Model.acceptKeys P (toSignalPqxdhAcceptKeysInput inp)).map
        ofSignalPqxdhDRKey := by
  have h := Model.acceptKeys_ofSignalPqxdhPrimitives P (toSignalPqxdhAcceptKeysInput inp)
  rwa [ofSignalPqxdhAcceptKeysInput_toSignalPqxdhAcceptKeysInput] at h

theorem Model.initiate_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (inp : SignalPqxdh.InitiateInput) :
    Model.initiate (ofSignalPqxdhPrimitives P) (ofSignalPqxdhInitiateInput inp) =
      (SignalPqxdh.Model.initiate P inp).map
        (fun (dk, rk1, ck1_1, msg) =>
          (ofSignalPqxdhDRKey dk, rk1, ck1_1, ofSignalPqxdhPreKeyMsg msg)) := by
  unfold Model.initiate SignalPqxdh.Model.initiate
  dsimp only [ofSignalPqxdhInitiateInput]
  rw [Model.initiateKeys_ofSignalPqxdhPrimitives]
  rcases SignalPqxdh.Model.initiateKeys P inp.toInitiateKeysInput with _ | ⟨⟨rk, ck, pqr⟩, hdr⟩ <;>
    simp [bind, ofSignalPqxdhPrimitives, ofSignalPqxdhInitiateKeysInput, ofSignalPqxdhBundle,
      ofSignalPqxdhDRKey, ofSignalPqxdhPreKeyMsg, ofSignalPqxdhMessageKeys,
      toSignalPqxdhMessageKeys,
      firstMsgAD_eq]

theorem Model.accept_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (inp : SignalPqxdh.AcceptInput) [AcceptKeysGuard P inp.keysInp] :
    Model.accept (ofSignalPqxdhPrimitives P) (ofSignalPqxdhAcceptInput inp) =
      (SignalPqxdh.Model.accept P inp).map
        (fun (dk, rk1, ck1_1, pt) => (ofSignalPqxdhDRKey dk, rk1, ck1_1, pt)) := by
  unfold Model.accept SignalPqxdh.Model.accept
  have hhdr : (ofSignalPqxdhHdr inp.keysInp.hdr == ofSignalPqxdhHdr inp.msg.hdr) =
      (inp.keysInp.hdr == inp.msg.hdr) := by
    by_cases h : inp.keysInp.hdr = inp.msg.hdr
    · rw [h]; simp
    · have hne : ofSignalPqxdhHdr inp.keysInp.hdr ≠ ofSignalPqxdhHdr inp.msg.hdr := by
        intro heq
        apply h
        have := congrArg toSignalPqxdhHdr heq
        simpa using this
      simp [h, hne]
  by_cases h1 : (inp.keysInp.hdr == inp.msg.hdr) = true <;>
    simp [ofSignalPqxdhAcceptInput, ofSignalPqxdhAcceptKeysInput, ofSignalPqxdhPreKeyMsg,
      hhdr, h1, «guard», _root_.guard]
  rw [← show ofSignalPqxdhAcceptKeysInput inp.keysInp =
      { ikBSk := inp.keysInp.ikBSk, ikBPk := inp.keysInp.ikBPk,
        spkBSk := inp.keysInp.spkBSk, spkBPk := inp.keysInp.spkBPk,
        opkBSk? := inp.keysInp.opkBSk?, pqspkBSk := inp.keysInp.pqspkBSk,
        pqspkBPk := inp.keysInp.pqspkBPk, trustedPeer := inp.keysInp.trustedPeer,
        replayOk := inp.keysInp.replayOk, hdr := ofSignalPqxdhHdr inp.keysInp.hdr } from rfl,
    Model.acceptKeys_ofSignalPqxdhPrimitives]
  rcases SignalPqxdh.Model.acceptKeys P inp.keysInp with _ | ⟨rk, ck, pqr⟩ <;>
    simp [bind, Option.bind, ofSignalPqxdhPrimitives, ofSignalPqxdhHdr, ofSignalPqxdhDRKey,
      ofSignalPqxdhMessageKeys, toSignalPqxdhMessageKeys, firstMsgAD_eq]
  rcases P.spqrInitRecv pqr inp.msg.pqRatchetMsg with _ | ⟨pqrStB, spqrSalt?⟩ <;>
    simp <;> rfl

/-! ## 5. `StructuralPrims` Bridge and Unconditional `initiatorModelPrims` Properties -/

/-- Lift `SignalPqxdh.WellFormedPrimitives P` across `ofSignalPqxdhPrimitives P`. -/
theorem structuralPrims_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (hWF : SignalPqxdh.WellFormedPrimitives P) :
    StructuralPrims (ofSignalPqxdhPrimitives P) :=
  Shared.structuralPrims_of_wellFormedPrimitives hWF

/-- `initiatorModelPrims X W = ofSignalPqxdhPrimitives (modelPrims X W)` unconditionally satisfies
    all 28 structural/reference properties of `StructuralPrims` for all `X` and `W`. -/
private theorem flatMap_toBEBytes_length {w : Nat} (n : Nat) :
    ∀ l : List (BitVec w), (l.flatMap (HMAC.toBEBytes n)).length = n * l.length
  | [] => by simp
  | x :: xs => by
    have hx : (HMAC.toBEBytes n x).length = n := by simp [HMAC.toBEBytes]
    simp only [List.flatMap_cons, List.length_append, hx, flatMap_toBEBytes_length n xs,
      List.length_cons, Nat.mul_succ]; omega

theorem structuralPrims_initiatorModelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    StructuralPrims (initiatorModelPrims X W) where
  sha256Compress_len st blk := by
    change (CryptoVerification.E2E.toU8 _).length = 32
    rw [CryptoVerification.E2E.toU8, List.length_map, flatMap_toBEBytes_length 4,
      List.Vector.toList_length]
  sha512Compress_len st blk := by
    change (CryptoVerification.E2E.toU8 _).length = 64
    rw [CryptoVerification.E2E.toU8, List.length_map, flatMap_toBEBytes_length 8,
      List.Vector.toList_length]
  aesEncBlock_len k blk := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.toU8,
      CryptoVerification.LibsignalAesCbc.blockToBytes, CryptoVerification.LibsignalAesCbc.toLEBytes]
  aesDecBlock_len k blk := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.toU8,
      CryptoVerification.LibsignalAesCbc.blockToBytes, CryptoVerification.LibsignalAesCbc.toLEBytes]
  sha512_eq_ref := modelPrims_sha512_eq_ref X W
  hkdfDerive96_eq_ref := fun s => by
    have h := modelPrims_hkdfDerive96_eq_ref X W s
    change (initiatorModelPrims X W).hkdfDerive96 s = _
    dsimp only [initiatorModelPrims, ofSignalPqxdhPrimitives]
    rw [h]
  rootCreateChain_eq_ref := modelPrims_rootCreateChain_eq_ref X W
  chainKdfSeed_eq_ref := modelPrims_chainKdfSeed_eq_ref X W
  chainKdfNext_eq_ref := modelPrims_chainKdfNext_eq_ref X W
  deriveMsgKeys_eq_ref := fun s salt => by
    have h := modelPrims_deriveMsgKeys_eq_ref X W s salt
    change (initiatorModelPrims X W).deriveMsgKeys s salt = _
    dsimp only [initiatorModelPrims, ofSignalPqxdhPrimitives]
    rw [h]
  aeadEnc_eq_ref := fun mk ad pt =>
    modelPrims_aeadEnc_eq_ref X W ⟨mk.cipherKey, mk.macKey, mk.iv⟩ ad pt
  aeadDec_eq_ref := fun mk ad ct =>
    modelPrims_aeadDec_eq_ref X W ⟨mk.cipherKey, mk.macKey, mk.iv⟩ ad ct
  sigVerify_eq_xeddsaVerifyRef := modelPrims_sigVerify_eq_ref X W
  isCanonical_eq_isCanonicalRef := modelPrims_isCanonical_eq_ref X W
  x25519_len k p := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  x25519Base_len k := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  sha512_len m := sha512Ref_length (initiatorModelPrims X W) m
  scalarFromBytesModOrder_len b := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  scalarFromWide_len b := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  montToEd_len u s pt h := by
    change (modelPrims X W).montToEd u s = some pt at h
    dsimp only [modelPrims, blockLevelPrims] at h
    rcases h1 : W.Q.montToEd (CryptoVerification.E2E.u8Vec 32 u) s.toBitVec with _ | v <;>
      simp [h1] at h
    subst h; simp [CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  edNeg_len pt := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  doubleScalarMulBasepoint_len h a s := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  compress_len pt := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  kemEncaps_isSome pk r hpk _ := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      SignalPqxdh.kyberPkLen, hpk]
  kemEncaps_len pk r ss ct h := by
    change (modelPrims X W).kemEncaps pk r = some (ss, ct) at h
    dsimp only [modelPrims, blockLevelPrims] at h
    split at h <;> [skip; simp at h]
    injection h with hpair; injection hpair with hss hct; subst hss hct
    simp [CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  kemDecaps_isSome sk ct _ hct := by
    simp [initiatorModelPrims, ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
      SignalPqxdh.kyberCtLen, hct]
  kemDecaps_len sk ct ss h := by
    change (modelPrims X W).kemDecaps sk ct = some ss at h
    dsimp only [modelPrims, blockLevelPrims] at h
    split at h <;> [skip; simp at h]
    injection h with hss; subst hss
    simp [CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]
  spqrInitSend_some k r := rfl

/-! ## 6. `WellSized*` Bridges and Unconditional Proofs for `initiateInput` / `acceptInput` -/

/-- Well-sizedness predicate for `InitiateKeysInput` (the handshake-only subset of
`WellSizedInitiateInput`). -/
def WellSizedInitiateKeysInput (inp : InitiateKeysInput) : Prop :=
  inp.ikASk.length = 32 ∧
  inp.ikAPk.length = 32 ∧
  inp.ekASk.length = 32 ∧
  inp.kemCoins.length = 32 ∧
  inp.bundle.ikB.length = 32 ∧
  inp.bundle.spkB.length = 32 ∧
  inp.bundle.spkSig.length = 64 ∧
  (∀ id pk, inp.bundle.opkB? = some (id, pk) → pk.length = 32) ∧
  inp.bundle.pqspkB.length = 1568 ∧
  inp.bundle.pqspkSig.length = 64

/-- Extend `InitiateKeysInput` to `InitiateInput` with Epoch-1 ratchet scalar `ephASk` (and dummy
    32-byte `spqrCoins` + empty `plaintext`, since `initialize_alice_session` only uses
    `ephASk`). -/
def InitiateKeysInput.withEphASk (inp : InitiateKeysInput) (ephASk : Bytes)
    (spqrCoins : Bytes := List.replicate 32 0) (plaintext : Bytes := []) : InitiateInput where
  toInitiateKeysInput := inp
  ephASk              := ephASk
  spqrCoins           := spqrCoins
  plaintext           := plaintext

theorem wellSizedInitiateInput_withEphASk {inp : InitiateKeysInput} {ephASk : Bytes}
    (h : WellSizedInitiateKeysInput inp) (heph : ephASk.length = 32) :
    WellSizedInitiateInput (inp.withEphASk ephASk) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h1, h2, h3, h4, heph, by simp [InitiateKeysInput.withEphASk], h5, h6, h7, h8, h9, h10⟩

/-- `ofSignalPqxdhInitiateKeysInput (CryptoVerification.E2E.initiateInput W me b t)` is
    unconditionally `WellSizedInitiateKeysInput` for every `W`, `me`, `b`, `t`. -/
theorem wellSizedInitiateKeysInput_initiateInput (W : PEParams) (me : LocalIdentity) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    WellSizedInitiateKeysInput
      (ofSignalPqxdhInitiateKeysInput (CryptoVerification.E2E.initiateInput W me b t)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e2e_vecU8_length _
  · exact e2e_vecU8_length _
  · simp [ofSignalPqxdhInitiateKeysInput, CryptoVerification.E2E.initiateInput,
      e2e_toU8_length, List.length_take, t.toList_length, initiateTapeLen]
  · exact e2e_vecU8_length _
  · exact e2e_vecU8_length _
  · exact e2e_vecU8_length _
  · exact e2e_vecU8_length _
  · intro id pk hopk
    dsimp only [ofSignalPqxdhInitiateKeysInput, ofSignalPqxdhBundle,
      CryptoVerification.E2E.initiateInput] at hopk
    rcases hb : b.opk with _ | ⟨i, k⟩
    · simp [hb] at hopk
    · simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hopk
      rcases hopk with ⟨_, rfl⟩
      exact e2e_vecU8_length k
  · exact e2e_vecU8_length _
  · exact e2e_vecU8_length _

/-- `ofSignalPqxdhAcceptKeysInput (CryptoVerification.E2E.acceptInput W me k m)` is
    unconditionally `WellSizedAcceptKeysInput` for every `W`, `me`, `k`, `m`. -/
theorem wellSizedAcceptKeysInput_acceptInput (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) :
    WellSizedAcceptKeysInput
      (ofSignalPqxdhAcceptKeysInput (CryptoVerification.E2E.acceptInput W me k m)) := by
  refine ⟨e2e_vecU8_length _, e2e_vecU8_length _, e2e_vecU8_length _, e2e_vecU8_length _, ?_,
    e2e_vecU8_length _, e2e_vecU8_length _, e2e_vecU8_length _, e2e_vecU8_length _,
    e2e_vecU8_length _⟩
  intro sk hsk
  dsimp only [ofSignalPqxdhAcceptKeysInput, CryptoVerification.E2E.acceptInput] at hsk
  rcases h1 : k.opk with _ | ⟨i, opkSk⟩ <;> rcases h2 : m.opkId with _ | j
  · simp [h1, h2] at hsk
  · simp [h1, h2] at hsk
  · simp [h1, h2] at hsk
  · simp only [h1, h2] at hsk
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte, Option.some.injEq] at hsk
      subst hsk
      exact e2e_vecU8_length _
    · simp [hij] at hsk

end CryptoVerification.E2E.Pqxdh.Initiator
