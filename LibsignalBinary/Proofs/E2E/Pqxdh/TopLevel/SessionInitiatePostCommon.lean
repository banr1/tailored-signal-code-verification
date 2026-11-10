/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionInitiateACommon
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.E2E.Bin.Record
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh.TopLevel
open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoGames
open CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.Initiator

def durationSinceZeroTsAllocSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗
      memRegion p 16 ∗ memRegion ret 24 ∗ stackAt s.sp allocHookStack
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion p 16 ∗
      ((∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
        (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2))) ∗
      stackAt s0.sp allocHookStack

def setUnackPreKeyMsgExactStackSpec (A : RustAlloc) (img : Obj.Image) :
    Spec SetUnackExactGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.statePtr ∧
      (s.readReg64 .x1).setWidth 32 = g.optOpkTag ∧
      (s.readReg64 .x2).setWidth 32 = g.optOpkVal ∧
      (s.readReg64 .x3).setWidth 32 = g.spkId ∧
      s.readReg64 .x4 = g.baseKeyPtr ∧
      g.baseKeyBytes.length = 32⌝ ∗
    (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKeyBytes) ∗
    ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (g.statePtr + 0x100#64) 40 ∗
    stackAt (s.sp - 144#64) (allocHookStack + 32) ∗
    cells (s.sp - 144#64) 18 ∗
    A.pool
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKeyBytes) ∗
    Initiator.vecU8 A (g.statePtr + 0xf8#64) (bytesToBv8 (encodeEC g.baseKeyBytes)) ∗
    ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
    ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
    ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
    ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
    memRegion (g.statePtr + 0x124#64) 4 ∗
    stackAt (s0.sp - 144#64) (allocHookStack + 32) ∗
    cells (s0.sp - 144#64) 18 ∗
    A.pool
  onPanic := rustPanicOnOom img

/-- 16-KiB (`extHookStack + 32`) stack generalization of `setUnackPreKeyMsgExactStackSpec`
for contract-backed `CliExt.durationSinceEpochSpec` (`extHookStack = 16384`). -/
def setUnackPreKeyMsgExtStackSpec (A : RustAlloc) (img : Obj.Image) :
    Spec SetUnackExactGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.statePtr ∧
      (s.readReg64 .x1).setWidth 32 = g.optOpkTag ∧
      (s.readReg64 .x2).setWidth 32 = g.optOpkVal ∧
      (s.readReg64 .x3).setWidth 32 = g.spkId ∧
      s.readReg64 .x4 = g.baseKeyPtr ∧
      g.baseKeyBytes.length = 32⌝ ∗
    (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKeyBytes) ∗
    ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (g.statePtr + 0x100#64) 40 ∗
    stackAt (s.sp - 144#64) (extHookStack + 32) ∗
    cells (s.sp - 144#64) 18 ∗
    A.pool
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKeyBytes) ∗
    Initiator.vecU8 A (g.statePtr + 0xf8#64) (bytesToBv8 (encodeEC g.baseKeyBytes)) ∗
    ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
    ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
    ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
    ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
    memRegion (g.statePtr + 0x124#64) 4 ∗
    stackAt (s0.sp - 144#64) (extHookStack + 32) ∗
    cells (s0.sp - 144#64) 18 ∗
    A.pool
  onPanic := rustPanicOnOom img


/-! ## Initiated `SessionState`, `Session`, and `SessionGhost` -/

/-- Abstract `SessionState` constructed by `initialize_alice_session` +
`set_unacknowledged_pre_key_message`
on the accept path of `session_initiate`. -/
def aliceInitiatedState (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : KeyPair) (ck1 : ChainKey)
    (pq : List (BitVec 8)) : SessionState (List (BitVec 8)) :=
  { sessionVersion := 4#32
    localIdentity := ourIdentity
    remoteIdentity := some theirIdentity
    rootKey := rk1
    previousCounter := 0#32
    senderChain := some ⟨sendingKeyPair, ck1⟩
    receiverChains := [⟨theirRatchetKey, some ⟨ck0, 0#32⟩, []⟩]
    pendingPreKey := true
    pqRatchetState := pq }

def aliceInitiatedSession (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey baseKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : KeyPair) (ck1 : ChainKey) (opkId? : Option (BitVec 32))
    (spkId kyberPreKeyId remoteRegId localRegId : BitVec 32)
    (kemCtSer pq : List (BitVec 8)) : Session (List (BitVec 8)) :=
  { state :=
      aliceInitiatedState ourIdentity theirIdentity theirRatchetKey rk1 ck0 sendingKeyPair ck1 pq
    pendingPreKey := some
      { preKeyId := opkId?
        signedPreKeyId := spkId
        baseKey := baseKey
        timestamp := 0#64 }
    pendingKyberPreKey := some
      { preKeyId := kyberPreKeyId
        ciphertext := kemCtSer }
    localRegistrationId := localRegId
    remoteRegistrationId := remoteRegId
    aliceBaseKey := baseKey.serialize }

def aliceInitiatedGhost
    (ourIdentity theirIdentity : IdentityKey) (theirRatchetKey baseKey : PublicKey)
    (sendingKeyPair : KeyPair)
    (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
     spqrCap spqrBufPtr
     receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
     senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
     pendingPtr kemCtSerPtr : BitVec 64)
    (opkTag opkId spkId pad_124 kyberPreKeyId pad_144 remoteRegId localRegId : BitVec 32)
    (kemCtSer : List (BitVec 8)) : SessionGhost :=
  { localIk := ⟨33#64, localIkBoxPtr, ourIdentity.publicKey.serialize⟩
    remoteIk := ⟨33#64, remoteIkBoxPtr, theirIdentity.publicKey.serialize⟩
    root := ⟨32#64, rootKeyBoxPtr⟩
    chainsCap := 4#64
    chainsPtr := chainBufPtr
    chains := [⟨⟨33#64, receiverRatchetPubBoxPtr, theirRatchetKey.serialize⟩,
                ⟨0#64, 1#64, []⟩, 0#64, 8#64, [], ⟨32#64, receiverChainKeyBoxPtr⟩⟩]
    alice := ⟨33#64, baseKeyBoxPtr, baseKey.serialize⟩
    pq := ⟨spqrCap, spqrBufPtr⟩
    sender := some ⟨⟨33#64, senderRatchetPubBoxPtr, sendingKeyPair.publicKey.serialize⟩,
                    ⟨32#64, senderRatchetPrivBoxPtr, sendingKeyPair.privateKey.bytes.toList⟩,
                    0#64, 8#64, ⟨32#64, senderChainKeyBoxPtr⟩⟩
    pending := some ⟨⟨33#64, pendingPtr, baseKey.serialize⟩,
                     unpack32 opkTag ++ unpack32 opkId ++ unpack64 0#64 ++
                       unpack32 spkId ++ unpack32 pad_124⟩
    kyber := some ⟨⟨1569#64, kemCtSerPtr, kemCtSer⟩,
                   unpack32 kyberPreKeyId ++ unpack32 pad_144⟩
    regIds := unpack32 remoteRegId ++ unpack32 localRegId }


private theorem encodeKey_length_le_10_init (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 :=
  Record.Serialization.EncodeRawAux.encodeVarint_length_le_10 _

private theorem lenField_length_le_init (tag : Nat) (b : List (BitVec 8)) :
    (Record.lenField tag b).length ≤ b.length + 20 := by
  unfold Record.lenField
  have h1 := encodeKey_length_le_10_init tag .lengthDelimited
  have h2 := Record.Serialization.EncodeRawAux.encodeVarint_length_le_10 (BitVec.ofNat 64 b.length)
  simp only [List.length_append]
  omega

private theorem bytesField_length_le_init (tag : Nat) (b : List (BitVec 8)) :
    (Record.bytesField tag b).length ≤ b.length + 20 := by
  unfold Record.bytesField
  split_ifs
  · simp
  · exact lenField_length_le_init tag b

private theorem uint32Field_length_le_init (tag : Nat) (v : BitVec 32) :
    (Record.uint32Field tag v).length ≤ 20 := by
  unfold Record.uint32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10_init tag .varint
    have h2 := Record.Serialization.EncodeRawAux.encodeVarint_length_le_10 (v.setWidth 64)
    simp only [List.length_append]
    omega

private theorem uint64Field_length_le_init (tag : Nat) (v : BitVec 64) :
    (Record.uint64Field tag v).length ≤ 20 := by
  unfold Record.uint64Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10_init tag .varint
    have h2 := Record.Serialization.EncodeRawAux.encodeVarint_length_le_10 v
    simp only [List.length_append]
    omega

private theorem int32Field_length_le_init (tag : Nat) (v : BitVec 32) :
    (Record.int32Field tag v).length ≤ 20 := by
  unfold Record.int32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10_init tag .varint
    have h2 := Record.Serialization.EncodeRawAux.encodeVarint_length_le_10 (v.signExtend 64)
    simp only [List.length_append]
    omega

private theorem optUint32Field_length_le_init (tag : Nat) (ov : Option (BitVec 32)) :
    (Record.optUint32Field tag ov).length ≤ 20 := by
  rcases ov with _ | v
  · simp [Record.optUint32Field]
  · unfold Record.optUint32Field
    have h1 := encodeKey_length_le_10_init tag .varint
    have h2 := Record.Serialization.EncodeRawAux.encodeVarint_length_le_10 (v.setWidth 64)
    simp only [List.length_append]
    omega

private theorem encChainKey_length_le_init (ck : ChainKey) :
    (Record.encChainKey ck).length ≤ 72 := by
  unfold Record.encChainKey
  have h1 := uint32Field_length_le_init 1 ck.index
  have h2 := bytesField_length_le_init 2 (keyToBytes32 ck.key)
  have hk : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [hk] at h2
  simp only [List.length_append]
  omega

/-- Upper bound `≤ 3800` on the protobuf encoding of `aliceInitiatedSession`. -/
theorem encodeSession_aliceInitiated_length_le
    (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey baseKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : KeyPair) (ck1 : ChainKey) (opkId? : Option (BitVec 32))
    (spkId kyberPreKeyId remoteRegId localRegId : BitVec 32)
    (kemCtSer pq : List (BitVec 8))
    (hkem_len : kemCtSer.length = 1569)
    (hpq_len : pq.length ≤ 1208) :
    (Bin.encodeSession (aliceInitiatedSession ourIdentity theirIdentity theirRatchetKey baseKey
      rk1 ck0 sendingKeyPair ck1 opkId? spkId kyberPreKeyId remoteRegId localRegId
        kemCtSer pq)).length ≤ 3800 := by
  let s := aliceInitiatedSession ourIdentity theirIdentity theirRatchetKey baseKey
    rk1 ck0 sendingKeyPair ck1 opkId? spkId kyberPreKeyId remoteRegId localRegId kemCtSer pq
  change (Record.encSession s).length ≤ 3800
  have hlen : (Record.encSession s).length =
      (Record.uint32Field 1 4#32).length +
      (Record.bytesField 2 ourIdentity.serialize).length +
      (Record.bytesField 3 theirIdentity.serialize).length +
      (Record.bytesField 4 (keyToBytes32 rk1)).length +
      (Record.uint32Field 5 0#32).length +
      (Record.lenField 6 (Record.encSenderChain ⟨sendingKeyPair, ck1⟩)).length +
      (Record.lenField 7 (Record.encReceiverChain ⟨theirRatchetKey, some ⟨ck0, 0#32⟩, []⟩)).length +
      (Record.lenField 9 (Record.encPendingPreKey ⟨opkId?, spkId, baseKey, 0#64⟩)).length +
      (Record.uint32Field 10 remoteRegId).length +
      (Record.uint32Field 11 localRegId).length +
      (Record.bytesField 13 baseKey.serialize).length +
      (Record.lenField 14 (Record.encPendingKyber ⟨kyberPreKeyId, kemCtSer⟩)).length +
      (Record.bytesField 15 pq).length := by
    simp only [s, aliceInitiatedSession, aliceInitiatedState, Record.encSession,
      Record.msgField, Option.map_some, Option.getD_some, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
  have h1 := uint32Field_length_le_init 1 4#32
  have h2 := bytesField_length_le_init 2 ourIdentity.serialize
  have hik1 : ourIdentity.serialize.length = 33 := PublicKey.serialize_length ourIdentity.publicKey
  rw [hik1] at h2
  have h3 := bytesField_length_le_init 3 theirIdentity.serialize
  have hik2 : theirIdentity.serialize.length =
    33 := PublicKey.serialize_length theirIdentity.publicKey
  rw [hik2] at h3
  have h4 := bytesField_length_le_init 4 (keyToBytes32 rk1)
  have hrk : (keyToBytes32 rk1).length = 32 := by simp [keyToBytes32]
  rw [hrk] at h4
  have h5 := uint32Field_length_le_init 5 0#32
  have h6 : (Record.lenField 6 (Record.encSenderChain ⟨sendingKeyPair, ck1⟩)).length ≤ 217 := by
    have h0 := lenField_length_le_init 6 (Record.encSenderChain ⟨sendingKeyPair, ck1⟩)
    have heq : (Record.encSenderChain ⟨sendingKeyPair, ck1⟩).length =
        (Record.bytesField 1 sendingKeyPair.publicKey.serialize).length +
        (Record.bytesField 2 sendingKeyPair.privateKey.bytes.toList).length +
        (Record.lenField 3 (Record.encChainKey ck1)).length := by
      simp only [Record.encSenderChain, Record.msgField, List.length_append]
    have ha := bytesField_length_le_init 1 sendingKeyPair.publicKey.serialize
    rw [PublicKey.serialize_length] at ha
    have hb := bytesField_length_le_init 2 sendingKeyPair.privateKey.bytes.toList
    rw [List.Vector.toList_length] at hb
    have hc := lenField_length_le_init 3 (Record.encChainKey ck1)
    have hd := encChainKey_length_le_init ck1
    omega
  have h7 : (Record.lenField 7 (Record.encReceiverChain ⟨theirRatchetKey, some ⟨ck0, 0#32⟩,
    []⟩)).length ≤ 165 := by
    have h0 :=
      lenField_length_le_init 7 (Record.encReceiverChain ⟨theirRatchetKey, some ⟨ck0, 0#32⟩, []⟩)
    have heq : (Record.encReceiverChain ⟨theirRatchetKey, some ⟨ck0, 0#32⟩, []⟩).length =
        (Record.bytesField 1 theirRatchetKey.serialize).length +
        (Record.lenField 3 (Record.encChainKey ⟨ck0, 0#32⟩)).length := by
      simp [Record.encReceiverChain, Record.msgField]
    have ha := bytesField_length_le_init 1 theirRatchetKey.serialize
    rw [PublicKey.serialize_length] at ha
    have hb := lenField_length_le_init 3 (Record.encChainKey ⟨ck0, 0#32⟩)
    have hc := encChainKey_length_le_init ⟨ck0, 0#32⟩
    omega
  have h9 : (Record.lenField 9 (Record.encPendingPreKey ⟨opkId?, spkId, baseKey,
    0#64⟩)).length ≤ 133 := by
    have h0 := lenField_length_le_init 9 (Record.encPendingPreKey ⟨opkId?, spkId, baseKey, 0#64⟩)
    have heq : (Record.encPendingPreKey ⟨opkId?, spkId, baseKey, 0#64⟩).length =
        (Record.optUint32Field 1 opkId?).length +
        (Record.bytesField 2 baseKey.serialize).length +
        (Record.int32Field 3 spkId).length +
        (Record.uint64Field 4 0#64).length := by
      simp only [Record.encPendingPreKey, List.length_append]
    have ha := optUint32Field_length_le_init 1 opkId?
    have hb := bytesField_length_le_init 2 baseKey.serialize
    rw [PublicKey.serialize_length] at hb
    have hc := int32Field_length_le_init 3 spkId
    have hd := uint64Field_length_le_init 4 0#64
    omega
  have h10 := uint32Field_length_le_init 10 remoteRegId
  have h11 := uint32Field_length_le_init 11 localRegId
  have h13 := bytesField_length_le_init 13 baseKey.serialize
  rw [PublicKey.serialize_length] at h13
  have h14 : (Record.lenField 14 (Record.encPendingKyber ⟨kyberPreKeyId,
    kemCtSer⟩)).length ≤ 1629 := by
    have h0 := lenField_length_le_init 14 (Record.encPendingKyber ⟨kyberPreKeyId, kemCtSer⟩)
    have heq : (Record.encPendingKyber ⟨kyberPreKeyId, kemCtSer⟩).length =
        (Record.uint32Field 1 kyberPreKeyId).length + (Record.bytesField 2 kemCtSer).length := by
      simp [Record.encPendingKyber]
    have ha := uint32Field_length_le_init 1 kyberPreKeyId
    have hb := bytesField_length_le_init 2 kemCtSer
    rw [hkem_len] at hb
    omega
  have h15 := bytesField_length_le_init 15 pq
  omega

theorem encodeRecord_aliceInitiated_length_lt
    (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey baseKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : KeyPair) (ck1 : ChainKey) (opkId? : Option (BitVec 32))
    (spkId kyberPreKeyId remoteRegId localRegId : BitVec 32)
    (kemCtSer pq : List (BitVec 8))
    (hkem_len : kemCtSer.length = 1569)
    (hpq_len : pq.length ≤ 1208) :
    (Record.encodeRecord ⟨some
      (aliceInitiatedSession ourIdentity theirIdentity theirRatchetKey baseKey
      rk1 ck0 sendingKeyPair ck1 opkId? spkId kyberPreKeyId remoteRegId localRegId
        kemCtSer pq)⟩).length < 2 ^ 32 := by
  let s := aliceInitiatedSession ourIdentity theirIdentity theirRatchetKey baseKey
    rk1 ck0 sendingKeyPair ck1 opkId? spkId kyberPreKeyId remoteRegId localRegId kemCtSer pq
  have hs :=
    encodeSession_aliceInitiated_length_le ourIdentity theirIdentity theirRatchetKey baseKey
    rk1 ck0 sendingKeyPair ck1 opkId? spkId kyberPreKeyId remoteRegId localRegId
    kemCtSer pq hkem_len hpq_len
  have hrec := lenField_length_le_init 1 (Record.encSession s)
  have henc : Record.encodeRecord ⟨some s⟩ = Record.lenField 1 (Record.encSession s) := rfl
  rw [henc]
  change (Bin.encodeSession s).length ≤ 3800 at hs
  change (Record.encSession s).length ≤ 3800 at hs
  omega


theorem deserialize_serialize_pk_init (pk : PublicKey) :
    PublicKey.deserialize pk.serialize = .ok pk := by
  unfold PublicKey.serialize PublicKey.deserialize
  rcases pk with ⟨⟨bs, hbs⟩⟩
  simp [hbs]
  congr 1
  exact Subtype.ext (List.take_of_length_le (Nat.le_of_eq hbs))



theorem vecU8Buf_of_live_pointsToBytes (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat)
    (hcap : cap = BitVec.ofNat 64 n) (hn0 : n ≠ 0) (hn_lt : n < 2 ^ 63)
    (hlen : bs.length = n) (hptr : ptr ≠ 0#64) :
    (ptr ↦ₛ bs) ∗ A.live ptr n 1 ⊢ vecU8Buf A cap ptr bs := by
  have hcap_nat : cap.toNat = n := by
    rw [hcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : cap ≠ 0 := by
    intro h0; rw [h0] at hcap_nat; exact hn0 hcap_nat.symm
  unfold vecU8Buf
  refine Entails.pure_right ⟨by omega, by omega, hptr⟩ ?_
  simp only [hcap_ne, ↓reduceIte, hcap_nat, hlen, Nat.sub_self, ProofLib.memRegion_zero,
    sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

theorem vecU8Buf_empty_0_1 (A : RustAlloc) :
    emp ⊢ vecU8Buf A 0#64 1#64 [] := by
  unfold vecU8Buf
  refine Entails.pure_right ⟨by decide, by decide, by decide⟩ ?_
  exact Entails.refl _

theorem vecBuf_empty_0_8_init {α : Type} (A : RustAlloc) (stride : Nat)
    (elem : α → BitVec 64 → SepProp) :
    emp ⊢ vecBuf A stride 8 elem 0#64 8#64 [] := by
  unfold vecBuf
  refine Entails.pure_right ⟨Nat.zero_le 0, by simp, by decide⟩ ?_
  exact Entails.refl _

theorem vecU8At_of_header_live_pointsToBytes (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat)
    (hcap : cap = BitVec.ofNat 64 n) (hn0 : n ≠ 0) (hn_lt : n < 2 ^ 63)
    (hlen : bs.length = n) (hptr : ptr ≠ 0#64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ cap) ∗
      (ptr ↦ₛ bs) ∗ A.live ptr n 1 ⊢ vecU8At A v cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf]
  have hlen_bv : BitVec.ofNat 64 bs.length = cap := by rw [hlen, ← hcap]
  rw [hlen_bv]
  unfold vecHeader
  have hbuf := vecU8Buf_of_live_pointsToBytes A cap ptr bs n hcap hn0 hn_lt hlen hptr
  have hassoc :
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ cap) ∗
        (ptr ↦ₛ bs) ∗ A.live ptr n 1) =
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ cap)) ∗
        ((ptr ↦ₛ bs) ∗ A.live ptr n 1)) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono_right hbuf

theorem vecU8At_empty_0_1_init (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8At A v 0#64 1#64 [] := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans (Entails.of_eq (sepConj_emp _).symm) ?_
  exact sepConj_mono_right (vecU8Buf_empty_0_1 A)

theorem vecAt_empty_0_8_104_init {α : Type} (A : RustAlloc)
    (elem : α → BitVec 64 → SepProp) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecAt A 104 8 elem v 0#64 8#64 [] := by
  unfold vecAt vecHeader
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans (Entails.of_eq (sepConj_emp _).symm) ?_
  exact sepConj_mono_right (vecBuf_empty_0_8_init A 104 elem)

/-- Fold the single receiver chain at `chainBufPtr` into `vecBuf A 104 8 (chainAt A) 4#64
chainBufPtr [...]`. -/
theorem receiverChainsVecBuf_aliceInitiated (A : RustAlloc)
    (chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr : BitVec 64)
    (theirRatchetKey : PublicKey) (ck0 : BitVec 256)
    (hcb : chainBufPtr ≠ 0#64)
    (hpub : receiverRatchetPubBoxPtr ≠ 0#64)
    (hck : receiverChainKeyBoxPtr ≠ 0#64) :
    A.live chainBufPtr 416 8 ∗
    receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr 0#32 ∗
    memRegion (chainBufPtr + 0x64#64) 316 ∗
    (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗ A.live receiverRatchetPubBoxPtr 33 1 ∗
    (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1 ⊢
      vecBuf A 104 8 (chainAt A) 4#64 chainBufPtr
        [(⟨⟨33#64, receiverRatchetPubBoxPtr, theirRatchetKey.serialize⟩,
           ⟨0#64, 1#64, []⟩, 0#64, 8#64, [], ⟨32#64, receiverChainKeyBoxPtr⟩⟩,
          ⟨theirRatchetKey, some ⟨ck0, 0#32⟩, []⟩)] := by
  have hsplit316 : memRegion (chainBufPtr + 0x64#64) 316 =
      memRegion (chainBufPtr + 0x64#64) 4 ∗ memRegion (chainBufPtr + 0x68#64) 312 :=
    ProofLib.memRegion_split' (b := chainBufPtr + 0x64#64) (n := 4) (k := 312)
      (b' := chainBufPtr + 0x68#64) rfl (by bv_omega) (by decide)
  rw [hsplit316]
  have hsrk := vecU8At_of_header_live_pointsToBytes A chainBufPtr 33#64 receiverRatchetPubBoxPtr
    theirRatchetKey.serialize 33 rfl (by decide) (by decide)
    (PublicKey.serialize_length theirRatchetKey) hpub
  have hpriv := vecU8At_empty_0_1_init A (chainBufPtr + 0x18#64)
  have hmk := vecAt_empty_0_8_104_init A (messageKeyAt A) (chainBufPtr + 0x30#64)
  have hck_vec := vecU8At_of_header_live_pointsToBytes A (chainBufPtr + 0x48#64) 32#64
    receiverChainKeyBoxPtr (keyToBytes32 ck0) 32 rfl (by decide) (by decide)
    (by simp [keyToBytes32]) hck
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsrk hpriv hmk hck_vec
  have hchain :
      receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr 0#32 ∗
      memRegion (chainBufPtr + 0x64#64) 4 ∗
      (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗
        A.live receiverRatchetPubBoxPtr 33 1 ∗
      (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1 ⊢
        chainAt A
          (⟨⟨33#64, receiverRatchetPubBoxPtr, theirRatchetKey.serialize⟩,
            ⟨0#64, 1#64, []⟩, 0#64, 8#64, [], ⟨32#64, receiverChainKeyBoxPtr⟩⟩,
           ⟨theirRatchetKey, some ⟨ck0, 0#32⟩, []⟩)
          chainBufPtr := by
    unfold receiverChainElemAt chainAt vecGhostAt optChainKeyAt
    have hpure :
        PublicKey.deserialize theirRatchetKey.serialize = .ok theirRatchetKey ∧
        ([] : List MessageKeyGenerator).length ≤ maxMessageKeys ∧
        ([] : List MessageKeyGhost).length = ([] : List MessageKeyGenerator).length ∧
        theirRatchetKey.serialize.length = 33 ∧ ([] : List (BitVec 8)) = [] :=
      ⟨deserialize_serialize_pk_init theirRatchetKey, Nat.zero_le _, rfl,
       PublicKey.serialize_length theirRatchetKey, rfl⟩
    refine Entails.pure_right hpure ?_
    dsimp only [List.zip_nil_left]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hrearr :
        ((chainBufPtr ↦₆₄ 33#64) ∗
         ((chainBufPtr + 0x08#64) ↦₆₄ receiverRatchetPubBoxPtr) ∗
         ((chainBufPtr + 0x10#64) ↦₆₄ 33#64) ∗
         ((chainBufPtr + 0x18#64) ↦₆₄ 0#64) ∗
         ((chainBufPtr + 0x20#64) ↦₆₄ 1#64) ∗
         ((chainBufPtr + 0x28#64) ↦₆₄ 0#64) ∗
         ((chainBufPtr + 0x30#64) ↦₆₄ 0#64) ∗
         ((chainBufPtr + 0x38#64) ↦₆₄ 8#64) ∗
         ((chainBufPtr + 0x40#64) ↦₆₄ 0#64) ∗
         ((chainBufPtr + 0x48#64) ↦₆₄ 32#64) ∗
         ((chainBufPtr + 0x50#64) ↦₆₄ receiverChainKeyBoxPtr) ∗
         ((chainBufPtr + 0x58#64) ↦₆₄ 32#64) ∗
         ((chainBufPtr + 0x60#64) ↦₃₂ 0#32)) ∗
        memRegion (chainBufPtr + 0x64#64) 4 ∗
        (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗
          A.live receiverRatchetPubBoxPtr 33 1 ∗
        (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1 =
        ((chainBufPtr ↦₆₄ 33#64) ∗
         ((chainBufPtr + 8#64) ↦₆₄ receiverRatchetPubBoxPtr) ∗
         ((chainBufPtr + 16#64) ↦₆₄ 33#64) ∗
         (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗
           A.live receiverRatchetPubBoxPtr 33 1) ∗
        (((chainBufPtr + 24#64) ↦₆₄ 0#64) ∗
         ((chainBufPtr + 32#64) ↦₆₄ 1#64) ∗
         ((chainBufPtr + 40#64) ↦₆₄ 0#64)) ∗
        (((chainBufPtr + 48#64) ↦₆₄ 0#64) ∗
         ((chainBufPtr + 56#64) ↦₆₄ 8#64) ∗
         ((chainBufPtr + 64#64) ↦₆₄ 0#64)) ∗
        (((chainBufPtr + 72#64) ↦₆₄ 32#64) ∗
         ((chainBufPtr + 80#64) ↦₆₄ receiverChainKeyBoxPtr) ∗
         ((chainBufPtr + 88#64) ↦₆₄ 32#64) ∗
         (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1) ∗
        (((chainBufPtr + 96#64) ↦₃₂ 0#32) ∗ memRegion (chainBufPtr + 100#64) 4) := by ac_rfl
    rw [hrearr]
    have hm := sepConj_mono hsrk (sepConj_mono hpriv (sepConj_mono hmk
      (sepConj_mono hck_vec (Entails.refl (((chainBufPtr + 96#64) ↦₃₂ 0#32) ∗
        memRegion (chainBufPtr + 100#64) 4)))))
    simpa only [sepConj_assoc] using hm
  unfold vecBuf
  have h4_ne : (4#64 : BitVec 64) ≠ 0 := by decide
  simp only [h4_ne, ↓reduceIte, List.length_singleton,
    show (4#64 : BitVec 64).toNat = 4 from rfl,
    show 4 * 104 = 416 from rfl,
    show 1 * 104 = 104 from rfl,
    show (4 - 1) * 104 = 312 from rfl,
    show BitVec.ofNat 64 104 = 0x68#64 from rfl,
    arrayAt_cons, arrayAt_nil, sepConj_emp]
  refine Entails.pure_right ⟨by decide, by decide, hcb⟩ ?_
  have hrearr2 :
      A.live chainBufPtr 416 8 ∗
      receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr 0#32 ∗
      (memRegion (chainBufPtr + 0x64#64) 4 ∗ memRegion (chainBufPtr + 0x68#64) 312) ∗
      (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗
        A.live receiverRatchetPubBoxPtr 33 1 ∗
      (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1 =
      A.live chainBufPtr 416 8 ∗
      (receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr 0#32 ∗
       memRegion (chainBufPtr + 0x64#64) 4 ∗
       (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗
         A.live receiverRatchetPubBoxPtr 33 1 ∗
       (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1) ∗
      memRegion (chainBufPtr + 0x68#64) 312 := by ac_rfl
  rw [hrearr2]
  exact sepConj_mono_right (sepConj_mono_left hchain)


end CryptoVerification.E2E.Pqxdh.TopLevel
