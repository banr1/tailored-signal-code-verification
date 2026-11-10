/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrWindowHonest
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge -- shake: keep
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RoundTrip -- shake: keep
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrCorrect -- shake: keep
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.SignalWireRoundTrip
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import LibsignalBinary.Proofs.SpqrV1.InitFacts
import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec
public import Computational.Proofs.E2E.PqxdhSessionModelProofDefs
public import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.LibsignalCli.PqFirstMessageSpqr

@[expose] public section

/-!
# First-Message Roundtrip for PQXDH Sessions

Proves `pqxdhFirstMessageRoundtrip_proof : PqxdhFirstMessageRoundtrip X W` by combining the
AES-256-CBC roundtrip, wire-length bounds, PQXDH handshake roundtrip, and Double Ratchet
first-message roundtrip.
-/

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.SignalSession.FirstMessage

private theorem flatMap_ofFn_chunks16' (k : Nat) (bs : List (BitVec 8)) (h : bs.length = 16 * k) :
    (List.ofFn fun i : Fin k => CBC.bytesToBlock ((bs.drop (16 * i.val)).take 16)).flatMap
      CBC.blockToBytesLE = bs := by
  induction k generalizing bs with
  | zero =>
    have h0 : bs.length = 0 := by omega
    rw [List.eq_nil_of_length_eq_zero h0]
    rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.flatMap_cons]
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    rw [blockToBytesLE_bytesToBlock' (bs.take 16) (by simp [h])]
    have hrest : (List.ofFn fun i : Fin k =>
        CBC.bytesToBlock ((bs.drop (16 * (i.val + 1))).take 16)) =
      List.ofFn fun i : Fin k =>
        CBC.bytesToBlock (((bs.drop 16).drop (16 * i.val)).take 16) := by
      congr 1
      ext i
      rw [List.drop_drop]
      have : 16 * (i.val + 1) = 16 + 16 * i.val := by omega
      rw [this]
    rw [hrest, ih (bs.drop 16) (by simp [h]; omega), List.take_append_drop]

private theorem flatMap_pkcs7Blocks' {ℓ : Nat} (m : CBC.Plain ℓ) :
    (CBC.pkcs7Blocks m).toList.flatMap CBC.blockToBytesLE = CBC.pkcs7Bytes m := by
  have hlen : (CBC.pkcs7Bytes m).length = 16 * CBC.nBlocks ℓ := by
    simp only [CBC.pkcs7Bytes, List.length_append, List.Vector.toList_length, List.length_replicate,
      CBC.padLen, CBC.nBlocks]
    omega
  unfold CBC.pkcs7Blocks
  rw [List.Vector.toList_ofFn]
  exact flatMap_ofFn_chunks16' (CBC.nBlocks ℓ) (CBC.pkcs7Bytes m) hlen

theorem cbcDecRaw_correct' {E D : CBC.AesKey → CBC.Block → CBC.Block}
    (hD : ∀ k x, D k (E k x) = x) (k : CBC.AesKey) (iv : CBC.Block) {ℓ : Nat} (m : CBC.Plain ℓ) :
    CBC.cbcDecRaw D k iv
      ((CBC.cbcEncrypt (E k) iv (CBC.pkcs7Blocks m)).toList.flatMap CBC.blockToBytesLE) =
      some m.toList := by
  have hlen :
      ((CBC.cbcEncrypt (E k) iv (CBC.pkcs7Blocks m)).toList.flatMap CBC.blockToBytesLE).length =
      16 * CBC.nBlocks ℓ := by
    rw [List.length_flatMap]
    have h16 : ∀ b : CBC.Block, (CBC.blockToBytesLE b).length = 16 := fun b => by
      simp [CBC.blockToBytesLE]
    simp [h16, List.sum_replicate, Nat.mul_comm]
  have hne : ¬ (((CBC.cbcEncrypt (E k) iv (CBC.pkcs7Blocks m)).toList.flatMap
        CBC.blockToBytesLE = []) ∨
      ((CBC.cbcEncrypt (E k) iv (CBC.pkcs7Blocks m)).toList.flatMap
        CBC.blockToBytesLE).length % 16 ≠ 0) := by
    rw [hlen]
    rintro (h | h)
    · have := congrArg List.length h
      rw [hlen] at this
      simp [CBC.nBlocks] at this
    · simp at h
  simp only [CBC.cbcDecRaw, hne, ↓reduceIte]
  rw [CBC.chunks16_flatMap, CBC.cbcDecryptBlocks_cbcEncrypt (hD k), flatMap_pkcs7Blocks',
    CBC.pkcs7Unpad_pkcs7Bytes]

theorem aesCbcDecrypt_aesCbcEncrypt' {E D : CBC.AesKey → CBC.Block → CBC.Block}
    (hD : ∀ k x, D k (E k x) = x) (key : CBC.AesKey) (iv : CBC.Block)
    (ptext : List (BitVec 8)) :
    aesCbcDecrypt D key iv (aesCbcEncrypt E key iv ptext) = some ptext := by
  dsimp only [aesCbcDecrypt, aesCbcEncrypt, CBC.cbcPkcs7EncryptOnly, CipherScheme.enc]
  exact cbcDecRaw_correct' hD key iv ⟨ptext, rfl⟩

/-! ## Wire length and `SignalWireShort` lemmas -/

theorem encodeVarintAux_length_le (k : Nat) (v : BitVec 64) :
    (encodeVarintAux k v).length ≤ k := by
  induction k generalizing v with
  | zero => simp [encodeVarintAux]
  | succ k ih =>
    simp only [encodeVarintAux]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (v >>> 7)
      omega

theorem encodeVarint_length_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v

theorem aesCbcEncrypt_length (E : CBC.AesKey → CBC.Block → CBC.Block)
    (key : CBC.AesKey) (iv : CBC.Block) (pt : List (BitVec 8)) :
    (aesCbcEncrypt E key iv pt).length = 16 * CBC.nBlocks pt.length := by
  dsimp only [aesCbcEncrypt, CBC.cbcPkcs7EncryptOnly, CipherScheme.enc]
  rw [List.length_flatMap]
  have h16 : ∀ b : CBC.Block, (CBC.blockToBytesLE b).length = 16 := fun b => by
    simp [CBC.blockToBytesLE]
  simp [h16, List.sum_replicate, Nat.mul_comm]

theorem aesCbcEncrypt_length_le (E : CBC.AesKey → CBC.Block → CBC.Block)
    (key : CBC.AesKey) (iv : CBC.Block) (pt : List (BitVec 8)) :
    (aesCbcEncrypt E key iv pt).length ≤ pt.length + 16 := by
  rw [aesCbcEncrypt_length, CBC.nBlocks]
  omega

theorem addrsE_length {uuidParse : LibsignalTripleRatchetRepr.UuidParser} {s r : Party} {a : Bytes}
    (h : serializedPartyAddresses uuidParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : LibsignalTripleRatchetRepr.serviceIdParse uuidParse
      (LibsignalTripleRatchetRepr.utf8 (partyAddressName s)) with
  | none => simp [hs, bind] at h
  | some sidS =>
    cases hr : LibsignalTripleRatchetRepr.serviceIdParse uuidParse
        (LibsignalTripleRatchetRepr.utf8 (partyAddressName r)) with
    | none => simp [hs, hr, bind] at h
    | some sidR =>
      simp only [hs, hr, bind, Option.bind, pure] at h
      injection h with h
      subst h
      simp [LibsignalTripleRatchetRepr.addrBytes, List.Vector.toList_length]

theorem encodeBytesField_addrsE_length_le (uuidParse : LibsignalTripleRatchetRepr.UuidParser)
    (s r : Party) :
    (encodeBytesField 6 (serializedPartyAddresses uuidParse s r)).length ≤ 38 := by
  cases h : serializedPartyAddresses uuidParse s r with
  | none => simp [encodeBytesField]
  | some a =>
    have ha := addrsE_length h
    have hk : (encodeKey 6 .lengthDelimited).length = 1 := by decide
    have hv : (encodeVarint 36#64).length = 1 := by decide
    simp only [encodeBytesField, List.length_append, hk, ha]
    rw [show BitVec.ofNat 64 36 = 36#64 from rfl, hv]

theorem signalWireShort_firstMsg (uuidParse : LibsignalTripleRatchetRepr.UuidParser)
    (s r : Party) (rk : PublicKey) (E : CBC.AesKey → CBC.Block → CBC.Block)
    (key : CBC.AesKey) (iv : CBC.Block) (pt pqMsg : Bytes)
    (hpt : pt.length + 2304 < 2 ^ 32) (hpq : pqMsg.length ≤ 64) :
    SignalWireShort ⟨currentVersion, rk, 0#32, 0#32, pqMsg, serializedPartyAddresses uuidParse s r⟩
      (aesCbcEncrypt E key iv pt) := by
  refine ⟨rfl, by unfold rustLenBound; dsimp only; omega, ?_, ?_⟩
  · intro a ha
    have := addrsE_length ha
    unfold rustLenBound
    omega
  · have := aesCbcEncrypt_length_le E key iv pt
    unfold rustLenBound
    omega

theorem signalMessage_new_firstMsg_length_lt (F : ShaCompress)
    (uuidParse : LibsignalTripleRatchetRepr.UuidParser) (s r : Party)
    (macKey : BitVec 256) (rk : PublicKey)
    (E : CBC.AesKey → CBC.Block → CBC.Block) (key : CBC.AesKey) (iv : CBC.Block)
    (pt : Bytes) (sId rId : IdentityKey) (pqMsg : Bytes)
    (hpt : pt.length + 2304 < 2 ^ 32) (hpq : pqMsg.length ≤ 64) :
    (SignalMessage.new F protoSignalCodec currentVersion macKey (serializedPartyAddresses uuidParse s r)
      rk 0#32 0#32 (aesCbcEncrypt E key iv pt) sId rId pqMsg).serialized.length +
      2048 < 2 ^ 32 := by
  dsimp only [SignalMessage.new]
  rw [List.length_append, computeMac_length]
  dsimp only [serializeContent, protoSignalCodec, encode]
  have hrk : (encodeBytesField 1 (some rk.serialize)).length = 35 := by
    have hser : rk.serialize.length = 33 := by
      simp [PublicKey.serialize, List.Vector.toList_length]
    have hk : (encodeKey 1 .lengthDelimited).length = 1 := by decide
    have hv : (encodeVarint 33#64).length = 1 := by decide
    simp only [encodeBytesField, List.length_append, hk, hser]
    rw [show BitVec.ofNat 64 33 = 33#64 from rfl, hv]
  have h2 : (encodeUint32Field 2 (some 0#32)).length = 2 := by decide
  have h3 : (encodeUint32Field 3 (some 0#32)).length = 2 := by decide
  have h4 : (encodeBytesField 4 (some (aesCbcEncrypt E key iv pt))).length ≤ pt.length + 27 := by
    have hk : (encodeKey 4 .lengthDelimited).length = 1 := by decide
    have hv := encodeVarint_length_le (BitVec.ofNat 64 (aesCbcEncrypt E key iv pt).length)
    have hct := aesCbcEncrypt_length_le E key iv pt
    simp only [encodeBytesField, List.length_append, hk]
    omega
  have h5 : (encodeBytesField 5
      (if pqMsg.isEmpty then none else some pqMsg)).length ≤ 75 := by
    split
    · simp [encodeBytesField]
    · have hk : (encodeKey 5 .lengthDelimited).length = 1 := by decide
      have hv := encodeVarint_length_le (BitVec.ofNat 64 pqMsg.length)
      simp only [encodeBytesField, List.length_append, hk]
      omega
  have h6 := encodeBytesField_addrsE_length_le uuidParse s r
  simp only [List.length_cons, List.length_append, hrk, h2, h3, macLength]
  omega

/-! ## PQXDH handshake roundtrip -/

theorem initiateKeys_hdr_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (inp : SignalPqxdh.InitiateKeysInput) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
    (h : SignalPqxdh.Model.initiateKeys (modelPrims X W) inp = some (dk, hdr)) :
    hdr.ikAPk = inp.ikAPk ∧
      hdr.ekAPk.length = 32 ∧
      hdr.spkId = inp.bundle.spkId ∧
      hdr.opkId? = (inp.bundle.opkB?.map Prod.fst) ∧
      hdr.pqspkId = inp.bundle.pqspkId ∧
      hdr.kemCt.length = 1568 := by
  unfold SignalPqxdh.Model.initiateKeys at h
  simp only [bind, Option.bind] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  cases henc : (modelPrims X W).kemEncaps inp.bundle.pqspkB inp.kemCoins with
  | none => simp [henc] at h
  | some p =>
    rw [henc] at h
    dsimp only [modelPrims, blockLevelPrims] at h henc
    split at henc <;> simp at henc
    rcases henc with ⟨_, rfl⟩
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    have hhdr := h.2.symm
    subst hhdr
    refine ⟨rfl, ?_, rfl, rfl, rfl, ?_⟩
    · exact vecU8_length _
    · exact vecU8_length _

theorem initiateKeys_acceptKeys_roundtrip (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (meA meB : LocalIdentity) (k : ResponderPreKeySecrets) (spkSig kpkSig : List.Vector (BitVec 8) 64)
    (t : List.Vector (BitVec 8) initiateTapeLen)
    (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr) (innerBytes : Bytes)
    (hXcomm : ∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) =
      W.C.X (Ratchet.clampScalar b) (W.C.pubKey (Ratchet.clampScalar a)))
    (hXnz : ∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8)
    (hKyber : ∀ coins, W.Q.decaps k.kpkSec (W.Q.encaps k.kpkPub coins).1 =
      (W.Q.encaps k.kpkPub coins).2)
    (hCanon : ∀ a, SignalPqxdh.isCanonicalRef (modelPrims X W)
      (vecU8 (W.C.pubKey (Ratchet.clampScalar a))) = true)
    (hAes : ∀ key blk, W.C.D key (W.C.E key blk) = blk)
    (hsigs : (honestBundle W.C meB k spkSig kpkSig).signaturesVerify X W = true)
    (hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W)
      (initiateInput W meA (honestBundle W.C meB k spkSig kpkSig) t) = some (dk, hdr)) :
    let b := honestBundle W.C meB k spkSig kpkSig
    let m : PreKeyMessageFields :=
      { regId := meA.regId
        opkId := b.opk.map Prod.fst
        spkId := k.spkId
        kpkId := k.kpkId
        kyberCt := u8Vec 1568 hdr.kemCt
        baseKey := u8Vec 32 hdr.ekAPk
        idPub := (keyPairOf W.C meA.idPriv).publicKey.bytes
        inner := innerBytes }
    SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W meB k m) = some dk := by
  intro b m
  set P := modelPrims X W
  set i := initiateInput W meA b t
  set initInp : SignalPqxdh.InitiateInput :=
    { toInitiateKeysInput := i, ephASk := [], spqrCoins := [], plaintext := [] }
  set accInp := acceptInput W meB k m
  have hsigs' :
      P.sigVerify i.bundle.ikB (SignalPqxdh.encodeEC i.bundle.spkB) i.bundle.spkSig = true ∧
      P.sigVerify i.bundle.ikB (SignalPqxdh.encodeKEM i.bundle.pqspkB) i.bundle.pqspkSig = true :=
    Bool.and_eq_true _ _ |>.mp hsigs
  have hIkA : initInp.ikAPk = P.x25519Base initInp.ikASk := by
    dsimp only [initInp, i, initiateInput, keyPairOf, P, modelPrims, blockLevelPrims]
    rw [u8Vec_vecU8, clampScalar_idem]
  have hIkB : initInp.bundle.ikB = P.x25519Base accInp.ikBSk ∧
      accInp.ikBPk = initInp.bundle.ikB := by
    refine ⟨?_, rfl⟩
    dsimp only [initInp, i, initiateInput, accInp, acceptInput, b, honestBundle, keyPairOf,
      P, modelPrims, blockLevelPrims]
    rw [u8Vec_vecU8, clampScalar_idem]
  have hSpkB : initInp.bundle.spkB = P.x25519Base accInp.spkBSk ∧
      accInp.spkBPk = initInp.bundle.spkB := by
    refine ⟨?_, rfl⟩
    dsimp only [initInp, i, initiateInput, accInp, acceptInput, b, honestBundle, keyPairOf,
      P, modelPrims, blockLevelPrims]
    rw [u8Vec_vecU8, clampScalar_idem]
  have hOpkB : initInp.bundle.opkB?.map Prod.snd = accInp.opkBSk?.map P.x25519Base ∧
      initInp.bundle.opkB?.isSome = accInp.opkBSk?.isSome := by
    dsimp only [initInp, i, initiateInput, accInp, acceptInput, m, b, honestBundle, keyPairOf,
      P, modelPrims, blockLevelPrims]
    cases k.opk with
    | none => simp
    | some pair =>
      rcases pair with ⟨id, sk⟩
      simp [u8Vec_vecU8, clampScalar_idem]
  set coins := initiateKemCoins t
  set ss := vecU8 (W.Q.encaps k.kpkPub coins).2
  set kemCt := vecU8 (W.Q.encaps k.kpkPub coins).1
  have hEncaps : P.kemEncaps initInp.bundle.pqspkB initInp.kemCoins = some (ss, kemCt) := by
    dsimp only [initInp, i, initiateInput, b, honestBundle, P, modelPrims, blockLevelPrims,
      ss, kemCt, coins]
    simp only [vecU8_length, SignalPqxdh.kyberPkLen, beq_self_eq_true, ↓reduceIte]
    rw [u8Vec_vecU8, u8Vec_vecU8]
  have hDecaps : P.kemDecaps accInp.pqspkBSk kemCt = some ss := by
    dsimp only [accInp, acceptInput, P, modelPrims, blockLevelPrims, ss, kemCt]
    simp only [vecU8_length, SignalPqxdh.kyberCtLen, beq_self_eq_true, ↓reduceIte]
    rw [u8Vec_vecU8, u8Vec_vecU8, hKyber]
  obtain ⟨drKey, hdr', rk1, ck1_1, msg, hInit', hAcc', -, -⟩ :=
    SignalPqxdh.pqxdh_handshake_roundtrip P
      (modelPrims_x25519_comm X W hXcomm)
      (fun e => hCanon (u8Vec 32 e))
      (fun _ => vecU8_length _)
      (modelPrims_x25519Base_ne_zero X W hXnz)
      (modelPrims_aead_roundtrip X W hAes)
      initInp accInp rfl rfl rfl hsigs'.1 hsigs'.2 hIkA hIkB hSpkB hOpkB ss kemCt hEncaps hDecaps
      (vecU8_length _)
      (fun _ _ _ _ h => by
        injection h with h
        rcases Prod.mk.inj h with ⟨_, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact ⟨[], rfl⟩)
      rfl
  have hEq : some (drKey, hdr') = some (dk, hdr) := hInit'.symm.trans hinit
  injection hEq with hPair
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPair
  obtain ⟨hikA, hekLen, hspkId, hopkId, hpqId, hctLen⟩ := initiateKeys_hdr_eq X W i drKey hdr' hinit
  have hHdrEq : hdr' = accInp.hdr := by
    rcases hdr' with ⟨hik, hek, hspk, hopk, hpq, hct⟩
    dsimp only at hikA hekLen hspkId hopkId hpqId hctLen
    dsimp only [accInp, acceptInput, m, i, initiateInput, b,
      honestBundle] at hikA hspkId hopkId hpqId ⊢
    have hek' : hek = vecU8 (u8Vec 32 hek) := (vecU8_u8Vec_of_length hek hekLen).symm
    have hopk' : hopk = Option.map u32 (Option.map Prod.fst
        (Option.map (fun x => (x.1, (keyPairOf W.C x.2).publicKey.bytes)) k.opk)) := by
      rw [hopkId]; cases k.opk <;> rfl
    have hct' : hct = vecU8 (u8Vec 1568 hct) := (vecU8_u8Vec_of_length hct hctLen).symm
    rw [hikA, hspkId, hpqId, ← hek', ← hopk', ← hct']
  rw [hHdrEq] at hAcc'
  exact hAcc'

/-! ## Double Ratchet first-message roundtrip -/

theorem toList_ne_replicate_zero {v : List.Vector (BitVec 8) 32}
    (h : v ≠ List.Vector.replicate 32 0#8) :
    v.toList ≠ List.replicate 32 0#8 := by
  intro heq
  apply h
  apply List.Vector.eq
  rw [heq]
  simp [List.Vector.replicate, List.Vector.toList]

theorem rootCreateChain_honest (C : Crypto)
    (hXnz : ∀ a b, C.X (Ratchet.clampScalar a) (C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8)
    (rk : RootKey) (a b : List.Vector (BitVec 8) 32) :
    rootCreateChain C rk ⟨C.pubKey (Ratchet.clampScalar b)⟩ ⟨Ratchet.clampScalar a⟩ =
      .ok (let p := Ratchet.rootKdf C.F rk
             (C.X (Ratchet.clampScalar a) (C.pubKey (Ratchet.clampScalar b))).toList
           (p.1, ⟨p.2, 0#32⟩)) := by
  dsimp only [rootCreateChain, Ratchet.createChain]
  rw [clampScalar_idem]
  have hne := toList_ne_replicate_zero (hXnz a b)
  simp only [hne, ↓reduceIte]
  rfl

theorem addrsOk_refl (a : Option (List (BitVec 8))) :
    LibsignalAead.addressCheckPasses a a = true := by
  cases a <;> simp [LibsignalAead.addressCheckPasses]

/-- First-message roundtrip for PQXDH sessions. -/
theorem pqxdhFirstMessageRoundtrip_proof (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    PqxdhFirstMessageRoundtrip X W := by
  intro meA meB k spkSig kpkSig t rs rc pt x g r w
    hXcomm hXnz hKyber hCanon hAes hpt hsigs hinit hsend
  set b := honestBundle W.C meB k spkSig kpkSig
  unfold initiateState at hinit
  cases hIK : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W meA b t) with
  | none =>
    rw [hIK] at hinit
    contradiction
  | some dk_hdr =>
    rcases dk_hdr with ⟨dk, hdr⟩
    rw [hIK] at hinit
    dsimp only at hinit
    set idA := keyPairOf W.C meA.idPriv
    set idB := keyPairOf W.C meB.idPriv
    set spkB := keyPairOf W.C k.spkPriv
    set rk0 := HKDF.bytesToKey32 (ofU8 dk.rootKey)
    set ck0 := HKDF.bytesToKey32 (ofU8 dk.chainKey)
    set pqr0 := HKDF.bytesToKey32 (ofU8 dk.pqrKey)
    set coinsA := HKDF.bytesToKey32 ((t.toList.drop 160).take 32)
    set ephA := KeyPair.generate W.C coinsA
    obtain ⟨stA1, salt, pqMsg, stB1, hSpqrSend, hpqLen, hSpqrRecv⟩ :=
      spqrPq_firstMessage_send_recv W pqr0 rs
    obtain ⟨stA0, hstA0⟩ : ∃ stA0, (pqxdhSpqrSession W).init .a2b pqr0 = stA0 := ⟨_, rfl⟩
    obtain ⟨stB0, hstB0⟩ : ∃ stB0, (pqxdhSpqrSession W).init .b2a pqr0 = stB0 := ⟨_, rfl⟩
    rw [hstA0] at hSpqrSend
    rw [hstB0] at hSpqrRecv
    set pA := Ratchet.rootKdf W.C.F rk0
      (W.C.X (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA))
        (W.C.pubKey (Ratchet.clampScalar k.spkPriv))).toList
    set sA0 := (((SessionState.new currentVersion ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pA.1
      stA0).addReceiverChain ⟨b.spkPub⟩ ⟨ck0, 0#32⟩).setSenderChain
      ephA ⟨pA.2, 0#32⟩).setUnacknowledgedPreKeyMessage
    have hInitSess :
        initializeInitiatorSession W.C (pqxdhSpqrSession W) ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ ⟨b.spkPub⟩
          rk0 ck0 pqr0 coinsA =
        .ok (((SessionState.new currentVersion ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pA.1
          stA0).addReceiverChain ⟨b.spkPub⟩ ⟨ck0, 0#32⟩).setSenderChain
          ephA ⟨pA.2, 0#32⟩) := by
      dsimp only [initializeInitiatorSession, KeyPair.generate, b, honestBundle,
        keyPairOf, pA]
      rw [hstA0, rootCreateChain_honest W.C hXnz rk0 (Ratchet.keyToBytesVec32 coinsA) k.spkPriv]
      rfl
    rw [hInitSess] at hinit
    injection hinit with hpair
    obtain ⟨hx, hg⟩ := Prod.mk.inj hpair
    subst hx hg
    have hpqLe : pqMsg.length ≤ 64 := by omega
    set mk := ((⟨pA.2, 0#32⟩ : ChainKey).messageKeys W.C.F).generateKeys W.C.F salt
    set ctext := aesCbcEncrypt W.C.E mk.cipherKey mk.iv pt
    set msg := SignalMessage.new W.C.F protoSignalCodec currentVersion mk.macKey
      (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B) ephA.publicKey 0#32 0#32
      ctext ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pqMsg
    have hFrom :
        Mut.exec OutgoingTripleRatchet.fromSessionState sA0 =
        (.ok ⟨ephA, ⟨pA.2, 0#32⟩, 0, stA0, currentVersion, ⟨idA.publicKey⟩, ⟨⟨b.idPub⟩⟩⟩,
         { sA0 with pqRatchetState := [] }) := rfl
    have hEnc :
        SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W) ((pqxdhSessionParams W).sendAddrs .A)
          pt rs.toList sA0 =
        (.ok msg,
         { (((SessionState.new currentVersion ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pA.1
              stA0).addReceiverChain ⟨b.spkPub⟩ ⟨ck0, 0#32⟩).setSenderChain
              ephA ⟨HKDF.bytesToKey32
                (Ratchet.chainHmac W.C.F pA.2 Ratchet.chainKeySeed), 1#32⟩
            ).setUnacknowledgedPreKeyMessage
            with pqRatchetState := stA1 }) := by
      have hSpqrSendPan := spqrPq_sendPanics_false_of_send_some W stA0 rs.toList hSpqrSend
      unfold SessionState.messageEncrypt
      rw [hFrom]
      dsimp only [OutgoingTripleRatchet.encrypt,
        Mut.exec, ExceptT.run, StateT.run, Id.run,
        monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
        ExceptT.lift, Functor.map, StateT.map,
        bind, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, Pure.pure, ExceptT.pure, StateT.bind, StateT.pure,
        get, getThe, MonadStateOf.get, StateT.get]
      simp only [hSpqrSendPan, Bool.false_eq_true, ↓reduceIte]
      rw [hSpqrSend]
      rfl
    change sendWirePending W (initiatorRecordExtras meA b ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt))
        ⟨.A, sA0, 0, [0]⟩ pt rs.toList = some _ at hsend
    unfold sendWirePending at hsend
    dsimp only at hsend
    rw [hEnc] at hsend
    dsimp only at hsend
    injection hsend with hsend'
    injection hsend' with hrw
    have hw : w = wirePrekey :: firstMessageBody
        (initiatorRecordExtras meA b ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt))
        sA0 msg :=
      (Prod.mk.inj hrw).2.symm
    set m : PreKeyMessageFields :=
      { regId := meA.regId
        opkId := b.opk.map Prod.fst
        spkId := k.spkId
        kpkId := k.kpkId
        kyberCt := u8Vec 1568 hdr.kemCt
        baseKey := u8Vec 32 hdr.ekAPk
        idPub := idA.publicKey.bytes
        inner := msg.serialized }
    refine ⟨m, hw, ?_, ?_⟩
    · exact signalMessage_new_firstMsg_length_lt W.C.F
        LibsignalTripleRatchetRepr.uuidTryParse .A .B
        mk.macKey ephA.publicKey W.C.E mk.cipherKey mk.iv pt ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pqMsg
        hpt hpqLe
    · have hrt : (signalWireCodec protoSignalCodec).parse
          ((signalWireCodec protoSignalCodec).encode
            ⟨currentVersion, ephA.publicKey, 0#32, 0#32, pqMsg,
              serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B⟩ ctext) =
          some (⟨currentVersion, ephA.publicKey, 0#32, 0#32, pqMsg,
            serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B⟩, ctext) :=
        LibsignalSession.signalRoundTripShort_proto
          ⟨currentVersion, ephA.publicKey, 0#32, 0#32, pqMsg,
            serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B⟩ ctext
          (signalWireShort_firstMsg LibsignalTripleRatchetRepr.uuidTryParse .A .B
            ephA.publicKey W.C.E
            mk.cipherKey mk.iv pt pqMsg hpt hpqLe)
      have htf : SignalMessage.tryFrom protoSignalCodec m.inner = .ok msg :=
        tryFrom_new W.C.F currentVersion mk.macKey
          (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B)
          ephA.publicKey 0#32 0#32 ctext ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pqMsg hrt
      have hAcc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W meB k m) = some dk :=
        initiateKeys_acceptKeys_roundtrip X W meA meB k spkSig kpkSig t dk hdr msg.serialized
          hXcomm hXnz hKyber hCanon hAes hsigs hIK
      unfold recvPrekeyModel recvPrekeyState
      rw [htf]
      simp only [m, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
      rw [hAcc]
      dsimp only
      set st0 : SessionState Bytes :=
        initializeRecipientSession (pqxdhSpqrSession W) ⟨(keyPairOf W.C meB.idPriv).publicKey⟩
          ⟨⟨idA.publicKey.bytes⟩⟩ (keyPairOf W.C k.spkPriv) rk0 ck0 pqr0
      have hrc1 : rootCreateChain W.C rk0 msg.senderRatchetKey
          (keyPairOf W.C k.spkPriv).privateKey = .ok (pA.1, ⟨pA.2, 0#32⟩) := by
        change rootCreateChain W.C rk0
          ⟨W.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA))⟩
          ⟨Ratchet.clampScalar k.spkPriv⟩ = .ok (pA.1, ⟨pA.2, 0#32⟩)
        rw [rootCreateChain_honest W.C hXnz rk0 k.spkPriv (Ratchet.keyToBytesVec32 coinsA),
          hXcomm k.spkPriv (Ratchet.keyToBytesVec32 coinsA)]
      have hrc2 : rootCreateChain W.C pA.1 msg.senderRatchetKey
          (KeyPair.generate W.C rc).privateKey =
          .ok (let p := Ratchet.rootKdf W.C.F pA.1
                 (W.C.X (Ratchet.clampScalar (Ratchet.keyToBytesVec32 rc))
                   (W.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA)))).toList
               (p.1, ⟨p.2, 0#32⟩)) := by
        change rootCreateChain W.C pA.1
          ⟨W.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA))⟩
          ⟨Ratchet.clampScalar (Ratchet.keyToBytesVec32 rc)⟩ = _
        exact rootCreateChain_honest W.C hXnz pA.1 (Ratchet.keyToBytesVec32 rc) (Ratchet.keyToBytesVec32 coinsA)
      have hmac : msg.verifyMacWithAddresses W.C.F ((pqxdhSessionParams W).expectedAddrs .B)
          ⟨⟨idA.publicKey.bytes⟩⟩ ⟨(keyPairOf W.C meB.idPriv).publicKey⟩ mk.macKey = true := by
        change msg.verifyMacWithAddresses W.C.F
          (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B)
          ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ mk.macKey = true
        exact verifyMacWithAddresses_new W.C.F protoSignalCodec currentVersion mk.macKey
          (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B)
          (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B) ephA.publicKey 0#32 0#32
          ctext ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pqMsg (addrsOk_refl _)
      have hcbc : aesCbcDecrypt W.C.D mk.cipherKey mk.iv msg.ciphertext = some pt :=
        aesCbcDecrypt_aesCbcEncrypt' hAes mk.cipherKey mk.iv pt
      have hver : ¬ (st0.version.toNat ≠ msg.messageVersion.toNat) := by
        intro h; exact h rfl
      have hcnt : ¬ (msg.counter < (0#32 : BitVec 32)) := by
        change ¬ ((0#32 : BitVec 32) < 0#32); decide
      have hsub0 : (msg.counter - 0#32).toNat = 0 := by
        change ((0#32 : BitVec 32) - 0#32).toNat = 0; decide
      have hdrop : (1 - 5 : Nat) = 0 := rfl
      have hnext : (⟨pA.2, 0#32⟩ : ChainKey).nextChainKey W.C.F =
          .ok ⟨HKDF.bytesToKey32 (Ratchet.chainHmac W.C.F pA.2 Ratchet.chainKeySeed), 1#32⟩ :=
        rfl
      have hSpqrRecvPan := spqrPq_recvPanics_false_of_recv_ok W stB0 pqMsg hSpqrRecv
      unfold SessionState.tryDecryptFromRecord
      simp only [hver, ↓reduceIte]
      dsimp only [st0, initializeRecipientSession]
      rw [hstB0]
      dsimp only [SessionState.tryDecryptWithState, TripleRatchet.fromSessionState,
        SessionState.takeRatchetState, SessionState.takePqRatchetState,
        TripleRatchet.decrypt, TripleRatchet.onRatchet, zoom,
        RatchetState.ensureReceiverChain, RatchetState.findReceiverChainKey,
        RatchetState.findReceiverChainIndex, List.findIdx?, List.findIdx?.go,
        RatchetState.dhRatchetStep, RatchetState.takeRootKey,
        RatchetState.evictReceiverChains, maxReceiverChains,
        RatchetState.consumeMessageKey, RatchetState.advanceChain,
        RatchetState.setReceiverChainKey,
        SessionState.new, SessionState.setSenderChain,
        Mut.exec, ExceptT.run, StateT.run, Id.run,
        monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
        ExceptT.lift, Functor.map, StateT.map,
        bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, ExceptT.pure, StateT.bind, StateT.pure, get, getThe, MonadStateOf.get,
        StateT.get, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, liftE]
      rw [hrc1]
      dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
        get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
      rw [hrc2]
      dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
        get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
        List.nil_append, List.length_singleton]
      simp only [hdrop, List.drop_zero, hcnt, hsub0, maxForwardJumps, Nat.not_lt_zero,
        RatchetState.advanceChain, ↓reduceIte]
      dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
        get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
      rw [hnext]
      dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
        get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
        List.findIdx?.go]
      simp only [beq_self_eq_true, ↓reduceIte]
      dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
        get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
        List.getElem?_cons_zero, List.set]
      rw [show msg.pqRatchet = pqMsg from rfl]
      simp only [hSpqrRecvPan, Bool.false_eq_true, ↓reduceIte]
      rw [hSpqrRecv]
      dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
        get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]
      rw [hmac, hcbc]
      rfl

end CryptoVerification.E2E
