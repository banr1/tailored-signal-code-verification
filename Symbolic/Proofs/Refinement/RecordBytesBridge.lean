/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.Proofs.SpecLemmas.CliPureBytes
public import ProofLib.Lemmas
import Symbolic.Proofs.Refinement.Composed.Cli.Model -- shake: keep

/-!
# Bridge between `recordBytes` and `encodeRecord`

Proves that the refinement statement's protobuf record encoder `recordBytes` agrees with the
session specification's `encodeRecord` on canonical sessions without pending pre-key fields
(`recordBytes_sessionToRecordRec_eq_encodeRecord`).
-/

@[expose] public section

set_option autoImplicit false

namespace Swarm.Phase0WholeFunctionBridge

open CryptoVerification
open DY.Libsignal.Composed.Refinement

private theorem encodeVarintAux_length_le_rbb :
    ∀ (k : Nat) (v : BitVec 64),
      (CryptoVerification.LibsignalProtoCodec.encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
  | k + 1, v => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    split
    · simp
    · have ih := encodeVarintAux_length_le_rbb k (v >>> 7)
      simp only [List.length_cons]
      omega

private theorem keyToBytes32_length_rbb (k : BitVec 256) :
    (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by
  simp [CryptoGames.HMAC.keyToBytes32]

theorem paddedVarint_zero_of_lt_128 {n : Nat} (h : n < 128) :
    DY.Libsignal.Refinement.paddedVarint n 0 = [BitVec.ofNat 8 n] := by
  rw [DY.Libsignal.Refinement.paddedVarint]
  simp [h]

theorem paddedVarint_zero_of_ge_128 {n : Nat} (h : 128 ≤ n) :
    DY.Libsignal.Refinement.paddedVarint n 0 =
      BitVec.ofNat 8 (n % 128 + 128) ::
        DY.Libsignal.Refinement.paddedVarint (n / 128) 0 := by
  rw [DY.Libsignal.Refinement.paddedVarint]
  have hnot' : ¬(n < 128) := by omega
  simp [hnot']

private theorem varint_cont_byte_eq (v : BitVec 64) :
    ((v &&& 0x7F) ||| 0x80).setWidth 8 = (v &&& 127#64).setWidth 8 + 128#8 := by
  have h1 : ((v &&& 0x7F) ||| 0x80).setWidth 8 = (v.setWidth 8 &&& 127#8) ||| 128#8 := by
    ext i hi; simp
  have h2 : (v &&& 127#64).setWidth 8 = v.setWidth 8 &&& 127#8 := by
    ext i hi; simp
  rw [h1, h2]
  generalize v.setWidth 8 = b
  revert b
  decide

theorem paddedVarint_zero_eq_encodeVarintAux :
    ∀ (k : Nat) (n : Nat),
      k ≠ 0 → n < 2 ^ (7 * k) → n < 2 ^ 64 →
      DY.Libsignal.Refinement.paddedVarint n 0 =
        CryptoVerification.LibsignalProtoCodec.encodeVarintAux k (BitVec.ofNat 64 n)
  | 0, _, hk, _, _ => absurd rfl hk
  | k + 1, n, _, hpow, hn => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    have htoNat : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    by_cases hlt : n < 128
    · rw [paddedVarint_zero_of_lt_128 hlt]
      have hlt' : (BitVec.ofNat 64 n).toNat < 0x80 := by rw [htoNat]; exact hlt
      simp only [hlt', ↓reduceIte, List.cons.injEq, and_true]
      apply BitVec.eq_of_toNat_eq
      simp
    · rw [paddedVarint_zero_of_ge_128 (by omega)]
      have hlt' : ¬((BitVec.ofNat 64 n).toNat < 0x80) := by rw [htoNat]; omega
      simp only [hlt', ↓reduceIte, List.cons.injEq]
      have hk_ne : k ≠ 0 := by
        rintro rfl
        simp at hpow
        omega
      have hdiv_pow : n / 128 < 2 ^ (7 * k) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        have : 2 ^ (7 * k) * 128 = 2 ^ (7 * (k + 1)) := by
          rw [show 7 * (k + 1) = 7 * k + 7 by omega, Nat.pow_add]
        omega
      constructor
      · rw [varint_cont_byte_eq]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_and,
          Nat.and_two_pow_sub_one_eq_mod _ 7]
      · rw [paddedVarint_zero_eq_encodeVarintAux k (n / 128) hk_ne hdiv_pow (by omega)]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ushiftRight, htoNat, Nat.shiftRight_eq_div_pow]
        omega

theorem paddedVarint_zero_eq_encodeVarint (n : Nat) (hn : n < 2 ^ 64) :
    DY.Libsignal.Refinement.paddedVarint n 0 =
      CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 n) :=
  paddedVarint_zero_eq_encodeVarintAux 10 n (by decide) (by omega) hn

theorem u32Field_eq_uint32Field (tag : Nat) (v : BitVec 32)
    (htag : tag * 8 < 2 ^ 64 := by decide) :
    DY.Libsignal.Composed.Refinement.u32Field tag v =
      CryptoVerification.E2E.Record.uint32Field tag v := by
  unfold DY.Libsignal.Composed.Refinement.u32Field
    CryptoVerification.E2E.Record.uint32Field
  split_ifs with hv
  · rfl
  · unfold DY.Libsignal.Refinement.encodeField
      CryptoVerification.LibsignalProtoCodec.encodeKey
    dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat]
    rw [paddedVarint_zero_eq_encodeVarint (tag * 8) htag,
        paddedVarint_zero_eq_encodeVarint v.toNat (by have := v.isLt; omega)]
    have hvw : BitVec.ofNat 64 v.toNat = v.setWidth 64 := by
      apply BitVec.eq_of_toNat_eq
      have := v.isLt
      simp [BitVec.toNat_setWidth]
    rw [hvw]

theorem msgField_eq_lenField (tag : Nat) (body : List (BitVec 8))
    (hlen : body.length < 2 ^ 64) (htag : tag * 8 + 2 < 2 ^ 64 := by decide) :
    DY.Libsignal.Composed.Refinement.msgField tag body =
      CryptoVerification.E2E.Record.lenField tag body := by
  unfold DY.Libsignal.Composed.Refinement.msgField
    DY.Libsignal.Refinement.encodeField
    CryptoVerification.E2E.Record.lenField
    CryptoVerification.LibsignalProtoCodec.encodeKey
  dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat]
  rw [paddedVarint_zero_eq_encodeVarint (tag * 8 + 2) htag,
      paddedVarint_zero_eq_encodeVarint body.length hlen]

theorem bytesField_eq_record_bytesField (tag : Nat) (b : List (BitVec 8))
    (hlen : b.length < 2 ^ 64) (htag : tag * 8 + 2 < 2 ^ 64 := by decide) :
    DY.Libsignal.Composed.Refinement.bytesField tag b =
      CryptoVerification.E2E.Record.bytesField tag b := by
  unfold DY.Libsignal.Composed.Refinement.bytesField
    CryptoVerification.E2E.Record.bytesField
  split_ifs with hb
  · rfl
  · exact msgField_eq_lenField tag b hlen htag

theorem encodeVarint_length_le_10 (v : BitVec 64) :
    (CryptoVerification.LibsignalProtoCodec.encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le_rbb 10 v

theorem encodeKey_length_le_10 (tag : Nat)
    (wt : CryptoVerification.LibsignalProtoCodec.WireType) :
    (CryptoVerification.LibsignalProtoCodec.encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le_10 _

theorem uint32Field_length_le_20 (tag : Nat) (v : BitVec 32) :
    (CryptoVerification.E2E.Record.uint32Field tag v).length ≤ 20 := by
  unfold CryptoVerification.E2E.Record.uint32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 (v.setWidth 64)
    rw [List.length_append]
    omega

theorem lenField_length_le (tag : Nat) (body : List (BitVec 8)) :
    (CryptoVerification.E2E.Record.lenField tag body).length ≤ body.length + 20 := by
  unfold CryptoVerification.E2E.Record.lenField
  have h1 := encodeKey_length_le_10 tag .lengthDelimited
  have h2 := encodeVarint_length_le_10 (BitVec.ofNat 64 body.length)
  simp only [List.length_append]
  omega

theorem record_bytesField_length_le (tag : Nat) (b : List (BitVec 8)) :
    (CryptoVerification.E2E.Record.bytesField tag b).length ≤ b.length + 20 := by
  unfold CryptoVerification.E2E.Record.bytesField
  split_ifs
  · simp
  · exact lenField_length_le tag b

theorem chainKey_field_eq_encChainKey (ck : CryptoGames.LibsignalSession.ChainKey) :
    DY.Libsignal.Composed.Refinement.u32Field 1 ck.index ++
      DY.Libsignal.Composed.Refinement.bytesField 2 (CryptoGames.HMAC.keyToBytes32 ck.key) =
      CryptoVerification.E2E.Record.encChainKey ck := by
  have hk_len : (CryptoGames.HMAC.keyToBytes32 ck.key).length = 32 :=
    keyToBytes32_length_rbb ck.key
  rw [u32Field_eq_uint32Field 1 ck.index,
      bytesField_eq_record_bytesField 2 _ (by omega)]
  rfl

theorem encChainKey_length_lt (ck : CryptoGames.LibsignalSession.ChainKey) :
    (CryptoVerification.E2E.Record.encChainKey ck).length < 128 := by
  unfold CryptoVerification.E2E.Record.encChainKey
  have h1 := uint32Field_length_le_20 1 ck.index
  have h2 := record_bytesField_length_le 2 (CryptoGames.HMAC.keyToBytes32 ck.key)
  have hk_len : (CryptoGames.HMAC.keyToBytes32 ck.key).length = 32 :=
    keyToBytes32_length_rbb ck.key
  rw [List.length_append]
  omega

theorem chainBytes_sender_eq_encSenderChain (sc : CryptoGames.LibsignalSession.SenderChain) :
    DY.Libsignal.Composed.Refinement.chainBytes
      { senderRatchetKey := sc.ratchetKey.publicKey.serialize
        senderRatchetKeyPrivate := sc.ratchetKey.privateKey.bytes.toList
        chainKey := some (sc.chainKey.index, CryptoGames.HMAC.keyToBytes32 sc.chainKey.key)
        messageKeys := [] } =
      CryptoVerification.E2E.Record.encSenderChain sc := by
  unfold DY.Libsignal.Composed.Refinement.chainBytes
    CryptoVerification.E2E.Record.encSenderChain
  dsimp only [Option.map_some, Option.getD_some, List.flatMap_nil, List.append_nil,
    CryptoVerification.E2E.Record.msgField]
  have hpub_len : sc.ratchetKey.publicKey.serialize.length = 33 := by
    simp [CryptoGames.LibsignalSession.PublicKey.serialize]
  have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
    List.Vector.toList_length _
  have hck := chainKey_field_eq_encChainKey sc.chainKey
  have hck_len := encChainKey_length_lt sc.chainKey
  rw [bytesField_eq_record_bytesField 1 _ (by omega),
      bytesField_eq_record_bytesField 2 _ (by omega),
      hck, msgField_eq_lenField 3 _ (by omega)]
  simp only [List.flatMap_nil, List.append_nil]

theorem messageKey_field_eq_encMessageKey
    (mk : CryptoGames.LibsignalSession.MessageKeyGenerator)
    (hseed : mk.seed.length < 2 ^ 63) :
    DY.Libsignal.Composed.Refinement.u32Field 1 mk.counter ++
      DY.Libsignal.Composed.Refinement.bytesField 5 mk.seed =
      CryptoVerification.E2E.Record.encMessageKey mk := by
  rw [u32Field_eq_uint32Field 1 mk.counter,
      bytesField_eq_record_bytesField 5 _ (by omega)]
  rfl

theorem encMessageKey_length_le (mk : CryptoGames.LibsignalSession.MessageKeyGenerator) :
    (CryptoVerification.E2E.Record.encMessageKey mk).length ≤ mk.seed.length + 40 := by
  unfold CryptoVerification.E2E.Record.encMessageKey
  have h1 := uint32Field_length_le_20 1 mk.counter
  have h2 := record_bytesField_length_le 5 mk.seed
  rw [List.length_append]
  omega

def senderChainToChainRec (sc : CryptoGames.LibsignalSession.SenderChain) :
    DY.Libsignal.Rust.ChainRec where
  senderRatchetKey := sc.ratchetKey.publicKey.serialize
  senderRatchetKeyPrivate := sc.ratchetKey.privateKey.bytes.toList
  chainKey := some (sc.chainKey.index, CryptoGames.HMAC.keyToBytes32 sc.chainKey.key)
  messageKeys := []

def receiverChainToChainRec (rc : CryptoGames.LibsignalSession.ReceiverChain) :
    DY.Libsignal.Rust.ChainRec where
  senderRatchetKey := rc.senderRatchetKey.serialize
  senderRatchetKeyPrivate := []
  chainKey := rc.chainKey.map fun ck => (ck.index, CryptoGames.HMAC.keyToBytes32 ck.key)
  messageKeys := rc.messageKeys.map fun mk => (mk.counter, mk.seed)

def sessionToSessionRec (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))) :
    DY.Libsignal.Rust.SessionRec where
  sessionVersion := s.state.sessionVersion
  localIdentityPublic := s.state.localIdentity.serialize
  remoteIdentityPublic :=
    (s.state.remoteIdentity.map CryptoGames.LibsignalSession.IdentityKey.serialize).getD []
  rootKey := CryptoGames.HMAC.keyToBytes32 s.state.rootKey
  previousCounter := s.state.previousCounter
  senderChain := s.state.senderChain.map senderChainToChainRec
  receiverChains := s.state.receiverChains.map receiverChainToChainRec
  pendingPreKey := none
  remoteRegistrationId := s.remoteRegistrationId
  localRegistrationId := s.localRegistrationId
  aliceBaseKey := s.aliceBaseKey
  pendingKyberPreKey := none
  pqRatchetState := s.state.pqRatchetState

def sessionToRecordRec (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))) :
    DY.Libsignal.Rust.RecordRec where
  current := sessionToSessionRec s
  previous := []

theorem chainBytes_receiver_eq_encReceiverChain
    (rc : CryptoGames.LibsignalSession.ReceiverChain)
    (hseeds : ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63) :
    DY.Libsignal.Composed.Refinement.chainBytes (receiverChainToChainRec rc) =
      CryptoVerification.E2E.Record.encReceiverChain rc := by
  unfold DY.Libsignal.Composed.Refinement.chainBytes
    receiverChainToChainRec
    CryptoVerification.E2E.Record.encReceiverChain
  dsimp only
  have hpub_len : rc.senderRatchetKey.serialize.length = 33 := by
    simp [CryptoGames.LibsignalSession.PublicKey.serialize]
  have hpriv : DY.Libsignal.Composed.Refinement.bytesField 2 [] = [] := rfl
  rw [hpriv, List.append_nil, bytesField_eq_record_bytesField 1 _ (by omega)]
  have hck_opt :
      ((rc.chainKey.map fun ck => (ck.index, CryptoGames.HMAC.keyToBytes32 ck.key)).map fun k =>
        DY.Libsignal.Composed.Refinement.msgField 3
          (DY.Libsignal.Composed.Refinement.u32Field 1 k.1 ++
            DY.Libsignal.Composed.Refinement.bytesField 2 k.2)).getD [] =
      CryptoVerification.E2E.Record.msgField 3
        (rc.chainKey.map CryptoVerification.E2E.Record.encChainKey) := by
    cases rc.chainKey with
    | none => rfl
    | some ck =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      have hck := chainKey_field_eq_encChainKey ck
      have hck_len := encChainKey_length_lt ck
      rw [hck, msgField_eq_lenField 3 _ (by omega)]
  rw [hck_opt]
  congr 1
  rw [List.flatMap_map, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro mk hmk
  have hs := hseeds mk hmk
  have hmk_eq := messageKey_field_eq_encMessageKey mk hs
  have hmk_len := encMessageKey_length_le mk
  rw [hmk_eq, msgField_eq_lenField 4 _ (by omega)]

/-- On a session with no pending pre-key fields and bounded field lengths, `recordBytes` agrees
with `encodeRecord`. -/
theorem recordBytes_sessionToRecordRec_eq_encodeRecord
    (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (hppk : s.pendingPreKey = none)
    (hpkp : s.pendingKyberPreKey = none)
    (halice : s.aliceBaseKey.length < 2 ^ 63)
    (hpq : s.state.pqRatchetState.length < 2 ^ 63)
    (hseeds : ∀ rc ∈ s.state.receiverChains,
      ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hrc_len : ∀ rc ∈ s.state.receiverChains,
      (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64)
    (hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64) :
    DY.Libsignal.Composed.Refinement.recordBytes (sessionToRecordRec s) =
      CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ := by
  unfold DY.Libsignal.Composed.Refinement.recordBytes
    sessionToRecordRec sessionToSessionRec
    CryptoVerification.E2E.Record.encodeRecord
  dsimp only [List.flatMap_nil, List.append_nil, Option.map_none, Option.getD_none,
    Option.map_some, CryptoVerification.E2E.Record.msgField]
  have hbody :
      DY.Libsignal.Composed.Refinement.u32Field 1 s.state.sessionVersion ++
        DY.Libsignal.Composed.Refinement.bytesField 2 s.state.localIdentity.serialize ++
        DY.Libsignal.Composed.Refinement.bytesField 3
          ((s.state.remoteIdentity.map CryptoGames.LibsignalSession.IdentityKey.serialize).getD []) ++
        DY.Libsignal.Composed.Refinement.bytesField 4
          (CryptoGames.HMAC.keyToBytes32 s.state.rootKey) ++
        DY.Libsignal.Composed.Refinement.u32Field 5 s.state.previousCounter ++
        ((Option.map senderChainToChainRec s.state.senderChain).map
          (DY.Libsignal.Composed.Refinement.msgField 6 ∘
            DY.Libsignal.Composed.Refinement.chainBytes)).getD [] ++
        (List.map receiverChainToChainRec s.state.receiverChains).flatMap
          (DY.Libsignal.Composed.Refinement.msgField 7 ∘
            DY.Libsignal.Composed.Refinement.chainBytes) ++
        [] ++
        DY.Libsignal.Composed.Refinement.u32Field 10 s.remoteRegistrationId ++
        DY.Libsignal.Composed.Refinement.u32Field 11 s.localRegistrationId ++
        DY.Libsignal.Composed.Refinement.bytesField 13 s.aliceBaseKey ++
        [] ++
        DY.Libsignal.Composed.Refinement.bytesField 15 s.state.pqRatchetState =
      CryptoVerification.E2E.Record.encSession s := by
    unfold CryptoVerification.E2E.Record.encSession
    rw [hppk, hpkp]
    dsimp only [Option.map_none, CryptoVerification.E2E.Record.msgField, List.append_nil]
    have hloc_len : s.state.localIdentity.serialize.length = 33 := by
      simp [CryptoGames.LibsignalSession.IdentityKey.serialize,
        CryptoGames.LibsignalSession.PublicKey.serialize]
    have hrem_len :
        ((s.state.remoteIdentity.map
          CryptoGames.LibsignalSession.IdentityKey.serialize).getD []).length < 2 ^ 64 := by
      cases s.state.remoteIdentity <;>
        simp [CryptoGames.LibsignalSession.IdentityKey.serialize,
          CryptoGames.LibsignalSession.PublicKey.serialize]
    have hrk_len : (CryptoGames.HMAC.keyToBytes32 s.state.rootKey).length = 32 :=
      keyToBytes32_length_rbb _
    have hsc_eq :
        ((Option.map senderChainToChainRec s.state.senderChain).map
          (DY.Libsignal.Composed.Refinement.msgField 6 ∘
            DY.Libsignal.Composed.Refinement.chainBytes)).getD [] =
        CryptoVerification.E2E.Record.msgField 6
          (s.state.senderChain.map CryptoVerification.E2E.Record.encSenderChain) := by
      cases s.state.senderChain with
      | none => rfl
      | some sc =>
        dsimp only [Option.map_some, Option.getD_some, Function.comp_apply,
          CryptoVerification.E2E.Record.msgField, senderChainToChainRec]
        rw [chainBytes_sender_eq_encSenderChain sc]
        have hsc_len : (CryptoVerification.E2E.Record.encSenderChain sc).length < 2 ^ 64 := by
          unfold CryptoVerification.E2E.Record.encSenderChain
          dsimp [CryptoVerification.E2E.Record.msgField]
          have h1 := record_bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
          have h2 := record_bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
          have h3 := lenField_length_le 3 (CryptoVerification.E2E.Record.encChainKey sc.chainKey)
          have h4 := encChainKey_length_lt sc.chainKey
          have hpub : sc.ratchetKey.publicKey.serialize.length = 33 := by
            simp [CryptoGames.LibsignalSession.PublicKey.serialize]
          have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
            List.Vector.toList_length _
          simp only [List.length_append]
          omega
        exact msgField_eq_lenField 6 _ hsc_len
    have hrc_eq :
        (List.map receiverChainToChainRec s.state.receiverChains).flatMap
          (DY.Libsignal.Composed.Refinement.msgField 7 ∘
            DY.Libsignal.Composed.Refinement.chainBytes) =
        (s.state.receiverChains.map fun c =>
          CryptoVerification.E2E.Record.lenField 7
            (CryptoVerification.E2E.Record.encReceiverChain c)).flatten := by
      rw [List.flatMap_map, List.flatMap_def]
      congr 1
      apply List.map_congr_left
      intro rc hrc
      dsimp only [Function.comp_apply]
      rw [chainBytes_receiver_eq_encReceiverChain rc (hseeds rc hrc),
          msgField_eq_lenField 7 _ (hrc_len rc hrc)]
    rw [u32Field_eq_uint32Field 1,
        bytesField_eq_record_bytesField 2 _ (by omega),
        bytesField_eq_record_bytesField 3 _ hrem_len,
        bytesField_eq_record_bytesField 4 _ (by omega),
        u32Field_eq_uint32Field 5,
        hsc_eq, hrc_eq,
        u32Field_eq_uint32Field 10,
        u32Field_eq_uint32Field 11,
        bytesField_eq_record_bytesField 13 _ (by omega),
        bytesField_eq_record_bytesField 15 _ (by omega)]
    rfl
  rw [hbody, msgField_eq_lenField 1 _ hsess_len]
  simp only [List.flatMap_nil, List.append_nil]

end Swarm.Phase0WholeFunctionBridge

namespace DY.Libsignal.TripleRatchet.Refinement
export DY.Libsignal.Composed.Refinement (
  vec32 bytesField u32Field msgField chainBytes recordBytes KeyInRecord
)
end DY.Libsignal.TripleRatchet.Refinement
