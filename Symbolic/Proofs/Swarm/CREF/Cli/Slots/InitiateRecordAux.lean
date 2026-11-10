/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# CLI `init` Crypto, SPQR Initialization, and Record Length Helpers

Relates `P.C` under `ModelAgree` to `cryptoOf'`, proves SPQR V1 `.init .a2b`
byte agreement and 118-byte length, and bounds `encodeRecordUnderExtras` to
preserve `PqxdhPartyInSpecDomain` after `initiateState`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
cref_open
open Symbolic.Swarm.CREF.CliPure

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG.CliPure.DecCrypto (keyToBytes32_bytesToKey32_of_length_eq_32)

/-! ## `ModelAgree` crypto and key-pair generation bridges -/

theorem crypto_eq_cryptoOf'_of_modelAgree {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) :
    P.C = cryptoOf' interp P.C.E P.C.D := by
  have hF := hagree.1
  have hX := hagree.2.2.2.1
  have hP := hagree.2.2.2.2.1
  cases hC : P.C with
  | mk F E D X pubKey =>
    rw [hC] at hF hX hP
    dsimp only at hF hX hP ⊢
    have hX_eq : X = (cryptoOf' interp E D).X := by
      funext sec pub
      apply List.Vector.eq
      symm
      exact Proofs.libsignal.Hooks2.cryptoOf'_X_toList_of_some interp E D sec pub
        (X sec pub).toList (List.Vector.toList_length _) (hX sec pub)
    have hP_eq : pubKey = (cryptoOf' interp E D).pubKey := by
      funext sec
      apply List.Vector.eq
      symm
      exact Proofs.libsignal.Hooks2.cryptoOf'_pubKey_toList_of_some interp E D sec
        (pubKey sec).toList (List.Vector.toList_length _) (hP sec)
    rw [hF, hX_eq, hP_eq]
    rfl

theorem keyVec_bytesToKey32_of_len32 {bs : HwBytes} (hbs : bs.length = 32) :
    Ratchet.keyToBytesVec32 (HKDF.bytesToKey32 bs) = vec32 bs := by
  apply List.Vector.eq
  change HMAC.keyToBytes32 (HKDF.bytesToKey32 bs) = (vec32 bs).toList
  rw [keyToBytes32_bytesToKey32_of_length_eq_32 bs hbs,
      Proofs.libsignal.Hooks2.vec32_toList_of_length_32' bs hbs]

theorem keyPair_generate_bytesToKey32_eq_keyPairOf (C : Crypto) {bs : HwBytes}
    (hbs : bs.length = 32) :
    KeyPair.generate C (HKDF.bytesToKey32 bs) = keyPairOf C (vec32 bs) := by
  unfold KeyPair.generate keyPairOf
  rw [keyVec_bytesToKey32_of_len32 hbs]

theorem keyPairOf_vec32_priv_pub {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) {bs : HwBytes} (hbs : bs.length = 32) :
    (keyPairOf P.C (vec32 bs)).privateKey.bytes.toList = clamp bs ∧
    (keyPairOf P.C (vec32 bs)).publicKey.bytes.toList = pubBytes interp bs := by
  have hvec : (vec32 bs).toList = bs :=
    Proofs.libsignal.Hooks2.vec32_toList_of_length_32' bs hbs
  have hcl : (Ratchet.clampScalar (vec32 bs)).toList = clamp bs := by
    rw [clampScalar_toList_eq_composedClamp, hvec]
  refine ⟨?_, ?_⟩
  · unfold keyPairOf
    exact hcl
  · unfold keyPairOf pubBytes
    dsimp only
    have hpub := hagree.2.2.2.2.1 (Ratchet.clampScalar (vec32 bs))
    rw [hcl] at hpub
    rw [hpub, Option.getD_some]

/-! ## SPQR V1 `.init .a2b` bridge and 118-byte length -/

section SpqrInitA2B

open CryptoVerification.LibsignalSpqrV1

private theorem isEmpty_false_of_len32 {xs : List (BitVec 8)} (h : xs.length = 32) :
    xs.isEmpty = false := by
  cases xs with
  | nil => cases h
  | cons _ _ => rfl

private theorem spqr_encodeBytesField_1_len32 {xs : List (BitVec 8)} (h : xs.length = 32) :
    Proto.encodeBytesField 1#32 xs = [0x0a#8, 0x20#8] ++ xs := by
  simp only [Proto.encodeBytesField, isEmpty_false_of_len32 h, Bool.false_eq_true,
    ↓reduceIte, Proto.encodeBytesUncond, h]; rfl

private theorem spqr_encodeBytesField_2_len32 {xs : List (BitVec 8)} (h : xs.length = 32) :
    Proto.encodeBytesField 2#32 xs = [0x12#8, 0x20#8] ++ xs := by
  simp only [Proto.encodeBytesField, isEmpty_false_of_len32 h, Bool.false_eq_true,
    ↓reduceIte, Proto.encodeBytesUncond, h]; rfl

private theorem map_toBEBytes_4_length :
    ∀ l : List (BitVec 32),
      l.map (fun w => (CryptoGames.HMAC.toBEBytes 4 w).length) = List.replicate l.length 4
  | [] => rfl
  | hd :: tl => by
    rw [List.map_cons, map_toBEBytes_4_length tl, List.length_cons, List.replicate_succ]
    have h4 : (CryptoGames.HMAC.toBEBytes 4 hd).length = 4 := by
      simp [CryptoGames.HMAC.toBEBytes]
    rw [h4]

private theorem sha256With_length (F : ShaCompress) (m : List (BitVec 8)) :
    (CryptoGames.HMAC.sha256With F m).length = 32 := by
  unfold CryptoGames.HMAC.sha256With
  generalize (CryptoGames.HMAC.chunks64 (CryptoGames.HMAC.sha256Pad m)).foldl F
    CryptoGames.HMAC.sha256IV = st
  rcases st with ⟨l, hl⟩
  dsimp only [List.Vector.toList]
  rw [List.length_flatMap, map_toBEBytes_4_length l, List.sum_replicate, hl]
  rfl

private theorem hmacWith_length (F : ShaCompress) (k m : List (BitVec 8)) :
    (CryptoGames.HMAC.hmacWith F k m).length = 32 :=
  sha256With_length F _

private theorem hkdfExpand_64_length (F : ShaCompress) (prk info : List (BitVec 8)) :
    (CryptoGames.HKDF.hkdfExpand F prk info 64).length = 64 := by
  change (((CryptoGames.HKDF.hkdfBlocks F prk info 2).flatten).take 64).length = 64
  simp only [CryptoGames.HKDF.hkdfBlocks, List.nil_append, List.cons_append,
    List.flatten_cons, List.flatten_nil, List.append_nil,
    List.length_take, List.length_append, hmacWith_length]
  rfl

private theorem authenticator_new_rk_mk_len32 (F : ShaCompress) (k : List (BitVec 8))
    (ep : BitVec 64) :
    (Authenticator.new F k ep).rootKey.length = 32 ∧
    (Authenticator.new F k ep).macKey.length = 32 := by
  unfold Authenticator.new Authenticator.update hkdfToVecUnchecked hkdfToSliceUnchecked
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [List.length_take, hkdfExpand_64_length]; rfl
  · rw [List.length_drop, hkdfExpand_64_length]

theorem spqrPq_init_a2b_length (P : PEParams) (k : BitVec 256) :
    ((pqxdhSpqrSession P).init .a2b k).length = 118 := by
  have hak : (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by
    simp [CryptoGames.HMAC.keyToBytes32]
  obtain ⟨hrk, hmk⟩ := authenticator_new_rk_mk_len32 P.C.F (CryptoGames.HMAC.keyToBytes32 k) 1#64
  change (Proto.encodeState
    { versionNegotiation := some
        { authKey := CryptoGames.HMAC.keyToBytes32 k
          direction := Direction.a2b.toI32
          minVersion := Version.v1.toI32
          chainParams := some DEFAULT_CHAIN_PARAMS.intoPb }
      chain := none
      inner := some (.v1
        { innerState := some (.keysUnsampled
            { uc := some { epoch := 1#64, auth := some (Authenticator.new P.C.F
                (CryptoGames.HMAC.keyToBytes32 k) 1#64).intoPb } }) }) }).length = 118
  generalize Authenticator.new P.C.F (CryptoGames.HMAC.keyToBytes32 k) 1#64 = auth at hrk hmk ⊢
  have hauth_len : (ProtoAuthenticator.encodeRaw auth.intoPb).length = 68 := by
    unfold ProtoAuthenticator.encodeRaw Authenticator.intoPb
    rw [spqr_encodeBytesField_1_len32 hrk, spqr_encodeBytesField_2_len32 hmk]
    simp [hrk, hmk]
  have huc_len : (V1State.Unchunked.KeysUnsampled.encodeRaw
      { epoch := 1#64, auth := some auth.intoPb }).length = 72 := by
    unfold V1State.Unchunked.KeysUnsampled.encodeRaw Proto.encodeOptMessage Proto.encodeMessage
    dsimp only
    rw [hauth_len]
    change ([0x08#8, 0x01#8] ++ ([0x12#8, 0x44#8] ++ auth.intoPb.encodeRaw)).length = 72
    simp [hauth_len]
  have hck_len : (V1State.Chunked.KeysUnsampled.encodeRaw
      { uc := some { epoch := 1#64, auth := some auth.intoPb } }).length = 74 := by
    unfold V1State.Chunked.KeysUnsampled.encodeRaw Proto.encodeOptMessage Proto.encodeMessage
    dsimp only
    rw [huc_len]
    change ([0x0a#8, 0x48#8] ++
      V1State.Unchunked.KeysUnsampled.encodeRaw { epoch := 1#64, auth := some auth.intoPb }).length = 74
    simp [huc_len]
  have hv1_len : (V1State.encodeRaw
      { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some auth.intoPb } }) }).length = 76 := by
    unfold V1State.encodeRaw V1State.InnerState.encode Proto.encodeMessage
    dsimp only
    rw [hck_len]
    change ([0x0a#8, 0x4a#8] ++
      V1State.Chunked.KeysUnsampled.encodeRaw
        { uc := some { epoch := 1#64, auth := some auth.intoPb } }).length = 76
    simp [hck_len]
  have hvn_len : (VersionNegotiationPB.encodeRaw
      { authKey := CryptoGames.HMAC.keyToBytes32 k
        direction := Direction.a2b.toI32
        minVersion := Version.v1.toI32
        chainParams := some DEFAULT_CHAIN_PARAMS.intoPb }).length = 38 := by
    unfold VersionNegotiationPB.encodeRaw
    rw [spqr_encodeBytesField_1_len32 hak]
    change (([0x0a#8, 0x20#8] ++ CryptoGames.HMAC.keyToBytes32 k) ++ [] ++
      [0x18#8, 0x01#8] ++ [0x22#8, 0x00#8]).length = 38
    simp [hak]
  unfold Proto.encodeState PqRatchetState.encode PqRatchetState.encodeRaw
    PqRatchetState.Inner.encode Proto.encodeOptMessage Proto.encodeMessage
  dsimp only
  rw [hvn_len, hv1_len]
  change (([0x0a#8, 0x26#8] ++ VersionNegotiationPB.encodeRaw _) ++ [] ++
    ([0x1a#8, 0x4c#8] ++ V1State.encodeRaw _)).length = 118
  simp only [List.length_append, List.length_cons, List.length_nil, hvn_len, hv1_len]

theorem spqrPq_init_a2b_eq_compSemOf {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (r : ProtocolSetup) {pqr0 : HwBytes} (hpqr : pqr0.length = 32) :
    (pqxdhSpqrSession P).init .a2b (HKDF.bytesToKey32 pqr0) =
      (compSemOf interp r).init pqr0 [0#8] := by
  unfold pqxdhSpqrSession spqrV1Session CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqrWith
    spqrV1Init spqrV1InitialStateFor libsignalSpqrParams
  dsimp only
  rw [hagree.1, keyToBytes32_bytesToKey32_of_length_eq_32 pqr0 hpqr]
  rfl

end SpqrInitA2B

/-! ## Record length bound and `PqxdhPartyInSpecDomain` preservation -/

private theorem state_lenField_length_le (tag : Nat) (payload : HwBytes) :
    (CryptoVerification.E2E.lenField tag payload).length ≤ payload.length + 22 := by
  unfold CryptoVerification.E2E.lenField
  simp only [List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 payload.length)
  omega

private theorem state_bytesField_length_le (tag : Nat) (v : HwBytes) :
    (CryptoVerification.E2E.bytesField tag v).length ≤ v.length + 22 := by
  unfold CryptoVerification.E2E.bytesField
  split
  · simp
  · exact state_lenField_length_le tag v

private theorem state_uint32Field_length_le (tag : Nat) (v : BitVec 32) :
    (CryptoVerification.E2E.uint32Field tag v).length ≤ 22 := by
  unfold CryptoVerification.E2E.uint32Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.setWidth 64)
    omega

private theorem state_uint64FieldX_length_le (tag : Nat) (v : BitVec 64) :
    (uint64FieldX tag v).length ≤ 22 := by
  unfold uint64FieldX
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le v
    omega

private theorem state_int32FieldX_length_le (tag : Nat) (v : BitVec 32) :
    (int32FieldX tag v).length ≤ 22 := by
  unfold int32FieldX
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.signExtend 64)
    omega

private theorem state_optUint32FieldX_length_le (tag : Nat) (o : Option (BitVec 32)) :
    (optUint32FieldX tag o).length ≤ 22 := by
  cases o with
  | none => simp [optUint32FieldX]
  | some v =>
    unfold optUint32FieldX
    simp only [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.setWidth 64)
    omega

private theorem state_msgField_some_length_le (tag : Nat) (body : HwBytes) :
    (CryptoVerification.E2E.msgField tag (some body)).length ≤ body.length + 22 :=
    state_lenField_length_le tag body

private theorem encChainKey_length_le (ck : ChainKey) :
    (encChainKey ck).length ≤ 76 := by
  unfold encChainKey
  simp only [List.length_append]
  have h1 := state_uint32Field_length_le 1 ck.index
  have h2 := state_bytesField_length_le 2 (HMAC.keyToBytes32 ck.key)
  have hk : (HMAC.keyToBytes32 ck.key).length = 32 := by simp [HMAC.keyToBytes32]
  omega

private theorem encSenderChain_length_le (c : SenderChain) :
    (encSenderChain c).length ≤ 207 := by
  unfold encSenderChain
  simp only [List.length_append]
  have h1 := state_bytesField_length_le 1 c.ratchetKey.publicKey.serialize
  have h2 := state_bytesField_length_le 2 c.ratchetKey.privateKey.bytes.toList
  have h3 := state_msgField_some_length_le 3 (encChainKey c.chainKey)
  have hc := encChainKey_length_le c.chainKey
  have hp1 : c.ratchetKey.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hp2 : c.ratchetKey.privateKey.bytes.toList.length = 32 := List.Vector.toList_length _
  omega

private theorem encReceiverChain_nil_length_le (pk : PublicKey) (ck : ChainKey) :
    (encReceiverChain ⟨pk, some ck, []⟩).length ≤ 153 := by
  unfold encReceiverChain
  simp only [Option.map_some, List.map_nil, List.flatten_nil, List.append_nil, List.length_append]
  have h1 := state_bytesField_length_le 1 pk.serialize
  have h2 := state_msgField_some_length_le 3 (encChainKey ck)
  have hc := encChainKey_length_le ck
  have hp : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  omega

private theorem encPendingPreKeyX_length_le (p : PendingPreKey) :
    (encPendingPreKeyX p).length ≤ 121 := by
  unfold encPendingPreKeyX
  simp only [List.length_append]
  have h1 := state_optUint32FieldX_length_le 1 p.preKeyId
  have h2 := state_bytesField_length_le 2 p.baseKey.serialize
  have h3 := state_int32FieldX_length_le 3 p.signedPreKeyId
  have h4 := state_uint64FieldX_length_le 4 p.timestamp
  have hp : p.baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  omega

private theorem encPendingKyberX_length_le (p : PendingKyberPreKey)
    (hct : p.ciphertext.length = 1569) :
    (encPendingKyberX p).length ≤ 1613 := by
  unfold encPendingKyberX
  simp only [List.length_append]
  have h1 := state_uint32Field_length_le 1 p.preKeyId
  have h2 := state_bytesField_length_le 2 p.ciphertext
  omega

private theorem encodeRecordX_initShape_lt_2pow31
    (pty : Party) (me : LocalIdentity) (bE : PreKeyBundleFields)
    (localPub : PublicKey) (baseKey : PublicKey) (kemCt : List.Vector (BitVec 8) 1568)
    (rk1 : RootKey) (ck0 : BitVec 256) (scKp : KeyPair) (ck1 : ChainKey)
    (pqr : HwBytes) (hpqr : pqr.length = 118) :
    (encodeRecordUnderExtras (fun _ => initiatorRecordExtras me bE baseKey kemCt)
      { party := pty
        session := ((((SessionState.new currentVersion ⟨localPub⟩ ⟨⟨bE.idPub⟩⟩
          rk1 pqr).addReceiverChain ⟨bE.spkPub⟩ ⟨ck0, 0⟩).setSenderChain
          scKp ck1).setUnacknowledgedPreKeyMessage)
        epoch := 0
        chainEpochs := [0] }).length < 2 ^ 31 := by
  unfold encodeRecordUnderExtras
  dsimp only
  apply Nat.lt_of_le_of_lt (state_msgField_some_length_le 1 _)
  unfold encStateUnderExtras
  simp only [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
    SessionState.setUnacknowledgedPreKeyMessage, initiatorRecordExtras, maxReceiverChains,
    Option.map_some, Option.getD_some, show ¬ (5 < 1) by decide, ↓reduceIte,
    List.nil_append, List.length_singleton, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
  have hf1 := state_uint32Field_length_le 1 (BitVec.ofNat 32 currentVersion.toNat)
  have hf2 := state_bytesField_length_le 2 (IdentityKey.mk localPub).serialize
  have hf3 := state_bytesField_length_le 3 (IdentityKey.mk ⟨bE.idPub⟩).serialize
  have hf4 := state_bytesField_length_le 4 (HMAC.keyToBytes32 rk1)
  have hf5 := state_uint32Field_length_le 5 0
  have hf6 := state_msgField_some_length_le 6 (encSenderChain ⟨scKp, ck1⟩)
  have hsc := encSenderChain_length_le ⟨scKp, ck1⟩
  have hf7 := state_lenField_length_le 7 (encReceiverChain ⟨⟨bE.spkPub⟩, some ⟨ck0, 0⟩, []⟩)
  have hrc_len := encReceiverChain_nil_length_le ⟨bE.spkPub⟩ ⟨ck0, 0⟩
  have hf9 := state_msgField_some_length_le 9
    (encPendingPreKeyX ⟨bE.opk.map Prod.fst, bE.spkId, baseKey, 0#64⟩)
  have hppk := encPendingPreKeyX_length_le ⟨bE.opk.map Prod.fst, bE.spkId, baseKey, 0#64⟩
  have hf10 := state_uint32Field_length_le 10 bE.regId
  have hf11 := state_uint32Field_length_le 11 me.regId
  have hf13 := state_bytesField_length_le 13 baseKey.serialize
  have hf14 := state_msgField_some_length_le 14
    (encPendingKyberX ⟨bE.kpkId, CryptoVerification.E2E.kyberKey kemCt⟩)
  have hpky := encPendingKyberX_length_le ⟨bE.kpkId, CryptoVerification.E2E.kyberKey kemCt⟩
    (by simp [CryptoVerification.E2E.kyberKey])
  have hf15 := state_bytesField_length_le 15 pqr
  have hid1 : (IdentityKey.mk localPub).serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize]
  have hid2 : (IdentityKey.mk ⟨bE.idPub⟩).serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize]
  have hrk1 : (HMAC.keyToBytes32 rk1).length = 32 := by simp [HMAC.keyToBytes32]
  have habk : baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have h2500 : 2500 < 2 ^ 31 := by decide
  omega

theorem encodeRecordX_initiateState_lt_2pow31 {X : UnreachedPqxdhPrimitives} {P : PEParams}
    {pty : Party} {me : LocalIdentity} {bE : PreKeyBundleFields} {tVec : List.Vector (BitVec 8) initiateTapeLen}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hinit : initiateState X P pty me bE tVec = some (x, g)) :
    (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := by
  unfold initiateState at hinit
  rcases hik : SignalPqxdh.Model.initiateKeys (modelPrims X P) (initiateInput P me bE tVec) with
    _ | ⟨dk, hdr⟩
  · simp [hik] at hinit
  · rw [hik] at hinit; dsimp only at hinit
    unfold initializeInitiatorSession at hinit
    dsimp only [bind, Except.bind, pure, Except.pure] at hinit
    rcases hrc : rootCreateChain P.C (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨bE.spkPub⟩
        (KeyPair.generate P.C (HKDF.bytesToKey32 ((tVec.toList.drop 160).take 32))).privateKey with
      _ | ⟨rk1, ck1⟩
    · simp [hrc] at hinit
    · rw [hrc] at hinit
      simp only [Option.some.injEq, Prod.mk.injEq] at hinit
      rcases hinit with ⟨rfl, rfl⟩
      exact encodeRecordX_initShape_lt_2pow31 pty me bE
        (keyPairOf P.C me.idPriv).publicKey ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt)
        rk1 (HKDF.bytesToKey32 (ofU8 dk.chainKey))
        (KeyPair.generate P.C (HKDF.bytesToKey32 ((tVec.toList.drop 160).take 32))) ck1
        ((pqxdhSpqrSession P).init .a2b (HKDF.bytesToKey32 (ofU8 dk.pqrKey)))
        (spqrPq_init_a2b_length P (HKDF.bytesToKey32 (ofU8 dk.pqrKey)))

theorem wfPq_after_initiateState {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {st : PqParty} (hal : AlicePqParty interp r st) (hwf_st : PqxdhPartyInSpecDomain P st)
    {X : UnreachedPqxdhPrimitives} {bE : PreKeyBundleFields} {tVec : List.Vector (BitVec 8) initiateTapeLen}
    (htrust : st.trusts ⟨⟨bE.idPub⟩⟩ = true)
    {x : RecordExtras} {g : GhostState HwBytes}
    (hinit : initiateState X P st.party st.me bE tVec = some (x, g)) :
    let st' : PqParty := { st with peerId := some ⟨⟨bE.idPub⟩⟩, session := some (x, g) }
    AlicePqParty interp r st' ∧
    ReachablePqxdhSession P st'.me x g ∧
    g.party = st'.party ∧
    PqxdhPartyInSpecDomain P st' := by
  intro st'
  have hpeer_eq : (some ⟨⟨bE.idPub⟩⟩ : Option IdentityKey) = st.peerId := by
    unfold PqParty.trusts at htrust
    rw [hal.peerId_eq] at htrust ⊢
    simp only [decide_eq_true_eq] at htrust
    rw [htrust]
  have hal' : AlicePqParty interp r st' :=
    ⟨hal.party_eq, hal.me_eq, hpeer_eq.trans hal.peerId_eq, hal.signed_nil,
     hal.oneTime_nil, hal.kyberOneTime_nil, hal.kyberLastResort_nil⟩
  have hreach : ReachablePqxdhSession P st'.me x g :=
    ReachablePqxdhSession.initiate X st.party st.me bE tVec x g hinit
  have hg_party : g.party = st'.party := by
    unfold initiateState at hinit
    rcases hik : SignalPqxdh.Model.initiateKeys (modelPrims X P)
        (initiateInput P st.me bE tVec) with _ | ⟨dk, hdr⟩
    · simp [hik] at hinit
    · rw [hik] at hinit; dsimp only at hinit
      rcases hii : initializeInitiatorSession P.C (pqxdhSpqrSession P)
          ⟨(keyPairOf P.C st.me.idPriv).publicKey⟩ ⟨⟨bE.idPub⟩⟩ ⟨bE.spkPub⟩
          (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
          (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          (HKDF.bytesToKey32 ((tVec.toList.drop 160).take 32)) with _ | sess
      · simp [hii] at hinit
      · rw [hii] at hinit
        simp only [Option.some.injEq, Prod.mk.injEq] at hinit
        rcases hinit with ⟨_, rfl⟩
        rfl
  have hrec_lt : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 :=
    encodeRecordX_initiateState_lt_2pow31 hinit
  refine ⟨hal', hreach, hg_party, ⟨fun x' g' hs' => ?_, ?_,
    hwf_st.2.2.1, hwf_st.2.2.2.1, hwf_st.2.2.2.2.1, hwf_st.2.2.2.2.2⟩⟩
  · dsimp only [st'] at hs'
    simp only [Option.some.injEq, Prod.mk.injEq] at hs'
    rcases hs' with ⟨rfl, rfl⟩
    exact ⟨⟨g, hreach, rfl, rfl⟩, hg_party, hrec_lt⟩
  · rw [encodeDir_of_alicePqParty hagree hEq hwf hal']
    dsimp only [st']
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ⟨commonFiles_alice_bounded hEq hwf f hf, fun _ => commonFiles_alice_fileCapBytes hEq hwf f hf⟩
    · rw [List.mem_singleton] at hf; subst hf
      exact ⟨hrec_lt, fun _ =>
        LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.reachPq_encodeRecordX_length_le_fileCapBytes hreach⟩

end Symbolic.Swarm.CREF.Cli.Slots
