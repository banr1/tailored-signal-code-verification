/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Game.StatementPq
public import Computational.Proofs.SpqrV1Sync.TopStateTight
import LibsignalBinary.Proofs.E2E.V1.SpqrV1FactsPure

/-!
# CLI I/O and plaintext cap completeness

Proves that honest plaintexts, ciphertexts, random-coin tapes, pre-key bundles, and party store
files fit within `maxPlaintextBytes`, `stdinCapBytes`, `fileCapBytes`, and `cliPathMaxBytes`.
-/

@[expose] public section

set_option autoImplicit false

open CryptoGames (Party)
open CryptoGames.LibsignalSession (ChainKey Crypto GhostState IdentityKey MessageKeyGenerator MessageType Mut PrivateKey PublicKey RatchetState ReceiverChain SenderChain SessionState ShaCompress SignalMessage SignalMessageProtoCodec SignalProtocolError Spqr TripleRatchet aesCbcDecrypt aesCbcEncrypt currentVersion initializeInitiatorSession initializeRecipientSession liftE maxForwardJumps maxMessageKeys maxReceiverChains rootCreateChain serializeContent)
open CryptoGames.LibsignalSessionApi (KyberPayload)
open CryptoVerification.E2E (BinState Bytes LocalIdentity ModelDriverInstance PEParams PreKeyBundleFields ReachablePqxdhSession RecordExtras acceptInput bhExpectedPreKeyMsg bytesField cliPqDirA cliPqDirOf cliPqDirRaw cliPqxdhDirBobAfterAccept cliPqxdhDirBobBeforeAccept djbKey encChainKey encMessageKey encPendingKyberX encPendingPreKeyX encReceiverChain encSenderChain encStateUnderExtras encodeRecordUnderExtras firstMessageBody initiateInput initiateState initiateTapeLen initiatorRecordExtras int32FieldX keyPairOf kyberKey lenField modelPrims msgField ofU8 optUint32FieldX partyAddressName pqxdhSessionParams pqxdhSpqrSession recvPrekeyState responderRecordExtras serializedPartyAddresses uint32Field uint64FieldX wirePrekey)
open CryptoVerification.LibsignalProtoCodec (WireType encodeBytesField encodeKey encodeUint32Field encodeVarint encodeVarintAux protoSignalCodec)
open CryptoVerification.SignalSession (PqKyberKey PqParty PqSignedKey baseKeysBytes bundleDir cliPathMaxBytes encodeDir fileCapBytes kyberRecordBytes le32 markKyberUsed maxPlaintextBytes oneTimeRecordBytes partyAddress pqSendModel publicBundleOf removeOpk signedRecordBytes stdinCapBytes textBytes)

namespace Computational.Proofs.LibsignalCli.CliCapsCompleteness

open CryptoVerification.RecordCodecs
  (IdentityKeyPairStructure PreKeyRecordStructure SignedPreKeyRecordStructure
   encodeProto3BytesField encodeProto3Fixed64Field encodeProto3Uint32Field le64Bytes)
open CryptoVerification.SpqrV1Sync.SendTotal
  (TopStateTight topStateTight_init topStateTight_length_le topStateTight_recv topStateTight_send)
open CryptoVerification.E2E.V1 (spqrV1Send_msg_len_le)

theorem fileCapBytes_eq_two_pow_21 : fileCapBytes = 2 ^ 21 := rfl

theorem stdinCapBytes_eq_two_pow_20 : stdinCapBytes = 2 ^ 20 := rfl

theorem send_plaintext_within_caps {m : List (BitVec 8)} (hm : m.length ≤ maxPlaintextBytes) :
    m.length ≤ maxPlaintextBytes ∧ m.length ≤ stdinCapBytes := by
  unfold maxPlaintextBytes stdinCapBytes at *
  omega

/-! ## Varint and protobuf encoding bounds -/

private theorem encodeVarintAux_len_le :
    ∀ (k : Nat) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (encodeVarintAux_len_le k (v >>> 7)) 1

private theorem encodeVarint_len_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_len_le 10 v

private theorem encodeKey_len_le (tag : Nat) (wt : WireType) : (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_len_le _

private theorem encodeUint32Field_len_le (tag : Nat) (ov : Option (BitVec 32)) :
    (encodeUint32Field tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := encodeKey_len_le tag .varint
    have h2 := encodeVarint_len_le (v.zeroExtend 64)
    omega

private theorem encodeBytesField_some_len_le (tag : Nat) (bs : Bytes) :
    (encodeBytesField tag (some bs)).length ≤ 20 + bs.length := by
  simp only [encodeBytesField, List.length_append]
  have h1 := encodeKey_len_le tag .lengthDelimited
  have h2 := encodeVarint_len_le (BitVec.ofNat 64 bs.length)
  omega

private theorem encodeProto3Bytes_len_le (tag : Nat) (bs : Bytes) :
    (encodeProto3BytesField tag bs).length ≤ 20 + bs.length := by
  unfold encodeProto3BytesField
  split_ifs
  · simp
  · exact encodeBytesField_some_len_le tag bs

private theorem encodeProto3Uint32_len_le (tag : Nat) (v : BitVec 32) :
    (encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold encodeProto3Uint32Field
  split_ifs
  · simp
  · exact encodeUint32Field_len_le tag (some v)

private theorem encodeProto3Fixed64_len_le (tag : Nat) (v : BitVec 64) :
    (encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold encodeProto3Fixed64Field
  split_ifs
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_len_le tag .sixtyFourBit
    have h2 : (le64Bytes v).length = 8 := by simp [le64Bytes]
    omega

private theorem prost_varint_len_le (k : Nat) :
    ∀ n : Nat, n < 128 ^ (k + 1) → (CryptoGames.LibsignalSessionApi.Prost.varint n).length ≤ k + 1 := by
  induction k with
  | zero =>
    intro n hn
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    simp [show n < 128 by omega]
  | succ k ih =>
    intro n hn
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      have hpow : 128 ^ (k + 1 + 1) = 128 * 128 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hdiv : n / 128 < 128 ^ (k + 1) := by omega
      have := ih (n / 128) hdiv
      omega

private theorem prost_uint32Field_len_le {tag : Nat} (ht : tag ≤ 8) (v? : Option (BitVec 32)) :
    (CryptoGames.LibsignalSessionApi.Prost.uint32Field tag v?).length ≤ 10 := by
  cases v? with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.uint32Field]
  | some v =>
    simp only [CryptoGames.LibsignalSessionApi.Prost.uint32Field, CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have h1 := prost_varint_len_le 0 (8 * tag + 0) (by omega)
    have h2 := prost_varint_len_le 4 v.toNat (by have := v.isLt; omega)
    omega

private theorem prost_bytesField_opt_len_le {tag : Nat} (ht : tag ≤ 8) (bs? : Option Bytes)
    (B : Nat) (hB : ∀ bs, bs? = some bs → bs.length ≤ B ∧ bs.length < 2 ^ 32) :
    (CryptoGames.LibsignalSessionApi.Prost.bytesField tag bs?).length ≤ 10 + B := by
  cases bs? with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.bytesField]
  | some bs =>
    obtain ⟨hle, hlt⟩ := hB bs rfl
    simp only [CryptoGames.LibsignalSessionApi.Prost.bytesField, CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have h1 := prost_varint_len_le 0 (8 * tag + 2) (by omega)
    have h2 := prost_varint_len_le 4 bs.length (by omega)
    omega

/-! ## Session record size bounds -/

private theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (m >>= f) s =
      match CryptoGames.LibsignalSession.Mut.exec m s with
      | (.ok a, s') => CryptoGames.LibsignalSession.Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  cases h : m s with | mk r s' =>
    cases r <;> (simp [CryptoGames.LibsignalSession.Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
      StateT.run, ExceptT.run]; try rfl)

private theorem mut_exec_pure {σ α : Type} (a : α) (s : σ) : CryptoGames.LibsignalSession.Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl
private theorem mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) : CryptoGames.LibsignalSession.Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
private theorem mut_exec_get {σ : Type} (s : σ) : CryptoGames.LibsignalSession.Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
private theorem mut_exec_set {σ : Type} (s' s : σ) : CryptoGames.LibsignalSession.Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl
private theorem mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) : CryptoGames.LibsignalSession.Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl
private theorem mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) : CryptoGames.LibsignalSession.Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
private theorem mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) : CryptoGames.LibsignalSession.Mut.exec (liftE r : Mut σ α) s = (r, s) := by cases r <;> rfl

private theorem mem_set_or {α : Type} : ∀ (l : List α) (i : Nat) (v x : α), x ∈ l.set i v → x = v ∨ x ∈ l
  | [], _, _, _, h => nomatch h
  | _ :: _, 0, _, _, h => (List.mem_cons.mp h).elim Or.inl (fun hm => Or.inr (List.mem_cons_of_mem _ hm))
  | hd :: tl, i + 1, v, x, h => (List.mem_cons.mp h).elim (fun e => Or.inr (e ▸ List.mem_cons_self ..))
      (fun hm => (mem_set_or tl i v x hm).elim Or.inl (fun h2 => Or.inr (List.mem_cons_of_mem hd h2)))

private theorem length_eraseIdx_le {α : Type} : ∀ (l : List α) (i : Nat), (l.eraseIdx i).length ≤ l.length
  | [], _ => Nat.le_refl 0 | _ :: tl, 0 => Nat.le_succ tl.length
  | _ :: tl, i + 1 => Nat.succ_le_succ (length_eraseIdx_le tl i)

private theorem mem_of_mem_eraseIdx {α : Type} : ∀ (l : List α) (i : Nat) (x : α), x ∈ l.eraseIdx i → x ∈ l
  | [], _, _, h => nomatch h | _ :: _, 0, _, h => List.mem_cons_of_mem _ h
  | hd :: tl, i + 1, x, h => (List.mem_cons.mp h).elim (fun e => e ▸ List.mem_cons_self ..)
      (fun hm => List.mem_cons_of_mem hd (mem_of_mem_eraseIdx tl i x hm))

private theorem mem_of_mem_dropLast {α : Type} : ∀ (l : List α) (x : α), x ∈ l.dropLast → x ∈ l
  | [], _, h => nomatch h | [_], _, h => nomatch h
  | hd :: b :: tl, x, h => (List.mem_cons.mp h).elim (fun e => e ▸ List.mem_cons_self ..)
      (fun hm => List.mem_cons_of_mem hd (mem_of_mem_dropLast (b :: tl) x hm))

private theorem mem_of_mem_drop {α : Type} : ∀ (n : Nat) (l : List α) (x : α), x ∈ l.drop n → x ∈ l
  | 0, _, _, h => h | _ + 1, [], _, h => nomatch h
  | n + 1, _ :: tl, _, h => List.mem_cons_of_mem _ (mem_of_mem_drop n tl _ h)

private theorem keyToBytes32_length (k : BitVec 256) : (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by simp [CryptoGames.HMAC.keyToBytes32]
private theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by simp [CryptoGames.LibsignalSession.PublicKey.serialize]
private theorem identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 := by simp [CryptoGames.LibsignalSession.IdentityKey.serialize, CryptoGames.LibsignalSession.PublicKey.serialize]
private theorem privateKey_bytes_length (sk : PrivateKey) : sk.bytes.toList.length = 32 := sk.bytes.toList_length
private theorem chainKey_messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) : (ck.messageKeys F).seed.length = 32 :=
  CryptoVerification.LibsignalSpqrV1.length_hmacWith F (CryptoGames.HMAC.keyToBytes32 ck.key) [CryptoGames.Ratchet.messageKeySeed]

private def RecvChainsOk (cs : List ReceiverChain) : Prop :=
  cs.length ≤ maxReceiverChains ∧
  ∀ rc ∈ cs, rc.messageKeys.length ≤ maxMessageKeys ∧ ∀ mk ∈ rc.messageKeys, mk.seed.length = 32

private theorem recvChainsOk_nil : RecvChainsOk [] := ⟨Nat.zero_le _, fun _ h => nomatch h⟩

private theorem recvChainsOk_addReceiverChain {PQ : Type} (s : SessionState PQ)
    (sender : PublicKey) (ck : ChainKey) (h : RecvChainsOk s.receiverChains) :
    RecvChainsOk (s.addReceiverChain sender ck).receiverChains := by
  unfold CryptoGames.LibsignalSession.SessionState.addReceiverChain; dsimp only
  set cs := s.receiverChains ++ [⟨sender, some ck, []⟩]
  have hcs_elem : ∀ rc ∈ cs,
      rc.messageKeys.length ≤ maxMessageKeys ∧ ∀ mk ∈ rc.messageKeys, mk.seed.length = 32 := by
    intro rc hmem; rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact h.2 rc hmem
    · rw [List.mem_singleton] at hmem; subst hmem; exact ⟨Nat.zero_le _, fun _ hm => nomatch hm⟩
  have hcs_len : cs.length = s.receiverChains.length + 1 := by simp [cs]
  have hmax : s.receiverChains.length ≤ maxReceiverChains := h.1
  by_cases hlt : maxReceiverChains < cs.length
  · simp only [hlt, ↓reduceIte]
    exact ⟨by rw [List.length_drop]; omega, fun rc hm => hcs_elem rc (mem_of_mem_drop 1 cs rc hm)⟩
  · simp only [hlt, ↓reduceIte]; exact ⟨by omega, hcs_elem⟩

private theorem recvChainsOk_evict_push (cs : List ReceiverChain) (their : PublicKey)
    (ck : ChainKey) (h : RecvChainsOk cs) :
    RecvChainsOk (CryptoGames.LibsignalSession.RatchetState.evictReceiverChains (cs ++ [⟨their, some ck, []⟩])) := by
  unfold CryptoGames.LibsignalSession.RatchetState.evictReceiverChains
  set cs1 := cs ++ [⟨their, some ck, []⟩]
  refine ⟨by rw [List.length_drop]; omega, fun rc hmem => ?_⟩
  have hmem1 := mem_of_mem_drop (cs1.length - maxReceiverChains) cs1 rc hmem
  rw [List.mem_append] at hmem1; rcases hmem1 with hmem1 | hmem1
  · exact h.2 rc hmem1
  · rw [List.mem_singleton] at hmem1; subst hmem1; exact ⟨Nat.zero_le _, fun _ hm => nomatch hm⟩

private theorem dhRatchetStep_recvChainsOk (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r r' : RatchetState) (ck : ChainKey) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.dhRatchetStep C their coins) r = (.ok ck, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.dhRatchetStep CryptoGames.LibsignalSession.RatchetState.takeRootKey at h
  rcases hsc : r.senderChain with _ | sc
  · simp [mut_exec_bind, mut_exec_get, hsc, mut_exec_throw] at h
  · simp only [mut_exec_bind, mut_exec_get, hsc, mut_exec_modifyGet] at h
    rcases h1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with _ | ⟨rk1, rck⟩
    · simp [h1, mut_exec_liftE] at h
    · simp only [h1, mut_exec_liftE] at h
      rcases h2 : rootCreateChain C rk1 their (CryptoGames.LibsignalSession.KeyPair.generate C coins).privateKey with
        _ | ⟨rk2, sck⟩
      · simp [h2] at h
      · simp only [h2, mut_exec_modify, mut_exec_pure, Prod.mk.injEq] at h
        rcases h with ⟨-, rfl⟩; exact recvChainsOk_evict_push r.receiverChains their rck hr

private theorem ensureReceiverChain_recvChainsOk (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r' : RatchetState) (ck : ChainKey) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.ensureReceiverChain at h; simp only [mut_exec_bind, mut_exec_get] at h
  rcases hf : r.findReceiverChainKey their with _ | (_ | ck0)
  · simp [hf, mut_exec_liftE] at h
  · simp only [hf, mut_exec_liftE] at h; exact dhRatchetStep_recvChainsOk C their coins r r' ck hr h
  · simp only [hf, mut_exec_liftE, mut_exec_pure, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩; exact hr

private theorem takeSkippedKey_recvChainsOk (their : PublicKey) (counter : BitVec 32)
    (r r' : RatchetState) (opt : Option MessageKeyGenerator) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.takeSkippedKey their counter) r = (.ok opt, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.takeSkippedKey at h; simp only [mut_exec_bind, mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp only [hidx, mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, mut_exec_throw] at h
    · simp only [hc] at h
      rcases hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp only [hpos, mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
      · simp only [hpos] at h
        rcases hk : c.messageKeys[pos]? with _ | key
        · simp [hk, mut_exec_throw] at h
        · simp only [hk, mut_exec_bind, mut_exec_set, mut_exec_pure, Prod.mk.injEq] at h
          rcases h with ⟨-, rfl⟩; have hc_ok := hr.2 c (List.mem_of_getElem? hc)
          refine ⟨by rw [List.length_set]; exact hr.1, fun rc hmem => ?_⟩
          rcases mem_set_or r.receiverChains idx _ rc hmem with rfl | hmem0
          · exact ⟨Nat.le_trans (length_eraseIdx_le c.messageKeys pos) hc_ok.1,
              fun mk hmk => hc_ok.2 mk (mem_of_mem_eraseIdx c.messageKeys pos mk hmk)⟩
          · exact hr.2 rc hmem0

private theorem storeSkippedKey_recvChainsOk (their : PublicKey) (key : MessageKeyGenerator)
    (r r' : RatchetState) (u : Unit) (hkey : key.seed.length = 32)
    (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.storeSkippedKey their key) r = (.ok u, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.storeSkippedKey at h; simp only [mut_exec_bind, mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp [hidx, mut_exec_throw] at h
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, mut_exec_throw] at h
    · simp only [hc, mut_exec_set, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
      have hc_ok := hr.2 c (List.mem_of_getElem? hc)
      refine ⟨by rw [List.length_set]; exact hr.1, fun rc hmem => ?_⟩
      rcases mem_set_or r.receiverChains idx _ rc hmem with rfl | hmem0
      · dsimp only; set keys1 := key :: c.messageKeys
        have hk1_elem : ∀ mk ∈ keys1, mk.seed.length = 32 := fun mk hmk =>
          (List.mem_cons.mp hmk).elim (fun e => e ▸ hkey) (hc_ok.2 mk)
        have hk1_len : keys1.length ≤ maxMessageKeys + 1 := by
          simp only [keys1, List.length_cons]; exact Nat.add_le_add_right hc_ok.1 1
        by_cases hlt : maxMessageKeys < keys1.length
        · simp only [hlt, ↓reduceIte]
          exact ⟨by rw [List.length_dropLast]; omega,
            fun mk hmk => hk1_elem mk (mem_of_mem_dropLast keys1 mk hmk)⟩
        · simp only [hlt, ↓reduceIte]; exact ⟨by omega, hk1_elem⟩
      · exact hr.2 rc hmem0

private theorem advanceChain_recvChainsOk (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) :
    ∀ (fuel : Nat) (ck ck' : ChainKey) (r r' : RatchetState), RecvChainsOk r.receiverChains →
      CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.advanceChain F their counter fuel ck) r = (.ok ck', r') →
      RecvChainsOk r'.receiverChains
  | 0, _, _, _, _, hr, h => by
    unfold CryptoGames.LibsignalSession.RatchetState.advanceChain at h
    simp only [mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
  | fuel + 1, ck, ck', r, r', hr, h => by
    unfold CryptoGames.LibsignalSession.RatchetState.advanceChain at h
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, mut_exec_bind] at h
      rcases hs : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨_ | u, r1⟩
      · rw [hs] at h; cases h
      · rw [hs] at h; dsimp only at h
        have hr1 := storeSkippedKey_recvChainsOk their (ck.messageKeys F) r r1 u
          (chainKey_messageKeys_seed_length F ck) hr hs
        rcases hn : ck.nextChainKey F with _ | ck1
        · simp [hn, mut_exec_liftE] at h
        · simp only [hn, mut_exec_liftE] at h
          exact advanceChain_recvChainsOk F their counter fuel ck1 ck' r1 r' hr1 h
    · simp only [hlt, ↓reduceIte, mut_exec_pure, Prod.mk.injEq] at h
      rcases h with ⟨-, rfl⟩; exact hr

private theorem setReceiverChainKey_recvChainsOk (their : PublicKey) (ck : ChainKey)
    (r r' : RatchetState) (u : Unit) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.setReceiverChainKey their ck) r = (.ok u, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.setReceiverChainKey at h; simp only [mut_exec_bind, mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp [hidx, mut_exec_throw] at h
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, mut_exec_throw] at h
    · simp only [hc, mut_exec_set, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
      have hc_ok := hr.2 c (List.mem_of_getElem? hc)
      refine ⟨by rw [List.length_set]; exact hr.1, fun rc hmem => ?_⟩
      exact (mem_set_or r.receiverChains idx _ rc hmem).elim
        (fun e => by rw [e]; exact hc_ok) (hr.2 rc)

private theorem consumeMessageKey_recvChainsOk (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType)
    (r r' : RatchetState) (mkg : MessageKeyGenerator) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.consumeMessageKey F their ck counter msgType) r = (.ok mkg, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.consumeMessageKey at h
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, mut_exec_bind] at h
    rcases htk : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.takeSkippedKey their counter) r with ⟨_ | (_ | k), r1⟩
    · rw [htk] at h; cases h
    · rw [htk] at h; simp [mut_exec_throw] at h
    · rw [htk] at h; simp only [mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
      exact takeSkippedKey_recvChainsOk their counter r r1 (some k) hr htk
  · simp only [hlt, ↓reduceIte, mut_exec_bind, mut_exec_get] at h
    split_ifs at h with hjump
    · simp [mut_exec_throw] at h
    · simp only [mut_exec_bind] at h
      rcases hadv : CryptoGames.LibsignalSession.Mut.exec
          (CryptoGames.LibsignalSession.RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r with
        ⟨_ | ck1, r1⟩
      · rw [hadv] at h; cases h
      · rw [hadv] at h; dsimp only at h
        have hr1 := advanceChain_recvChainsOk F their counter (counter - ck.index).toNat
          ck ck1 r r1 hr hadv
        rcases hn : ck1.nextChainKey F with _ | ck2
        · simp [hn, mut_exec_liftE] at h
        · simp only [hn, mut_exec_liftE] at h
          rcases hset : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.setReceiverChainKey their ck2) r1 with ⟨_ | u, r2⟩
          · rw [hset] at h; cases h
          · rw [hset] at h; simp only [mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
            exact setReceiverChainKey_recvChainsOk their ck2 r1 r2 u hr1 hset

private theorem onRatchet_ok {PQ α : Type} (m : Mut RatchetState α) (t t' : TripleRatchet PQ)
    (a : α) (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet m) t = (.ok a, t')) :
    CryptoGames.LibsignalSession.Mut.exec m t.ratchet = (.ok a, t'.ratchet) ∧ t'.pqrState = t.pqrState := by
  unfold CryptoGames.LibsignalSession.TripleRatchet.onRatchet CryptoGames.LibsignalSession.zoom at h
  simp only [mut_exec_bind, mut_exec_get] at h
  rcases hm : CryptoGames.LibsignalSession.Mut.exec m t.ratchet with ⟨_ | a0, r1⟩
  · simp [hm, mut_exec_set, mut_exec_liftE] at h
  · simp only [hm, mut_exec_set, mut_exec_liftE, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

private theorem messageEncrypt_ok_struct {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC) (addrs : Option Bytes)
    (ptext : Bytes) (coins : PQC) (record s : SessionState PQ) (msg : SignalMessage)
    (h : CryptoGames.LibsignalSession.SessionState.messageEncrypt C codec spqr addrs ptext coins record = (.ok msg, s)) :
    s.receiverChains = record.receiverChains ∧ s.remoteIdentity = record.remoteIdentity ∧
    ∃ salt pm, spqr.send record.pqRatchetState coins = some (s.pqRatchetState, salt, pm) := by
  unfold CryptoGames.LibsignalSession.SessionState.messageEncrypt at h
  rcases hfrom : CryptoGames.LibsignalSession.Mut.exec CryptoGames.LibsignalSession.OutgoingTripleRatchet.fromSessionState record with ⟨_ | o, taken⟩
  · rw [hfrom] at h; cases h
  · rw [hfrom] at h; dsimp only at h
    have htaken : taken.receiverChains = record.receiverChains ∧
        taken.remoteIdentity = record.remoteIdentity ∧ o.pqrState = record.pqRatchetState := by
      revert hfrom; unfold CryptoGames.LibsignalSession.OutgoingTripleRatchet.fromSessionState CryptoGames.LibsignalSession.SessionState.takePqRatchetState
      rcases hsc : record.senderChain with _ | sc
      · simp [mut_exec_bind, mut_exec_get, hsc, mut_exec_throw]
      · simp only [mut_exec_bind, mut_exec_get, hsc, mut_exec_modifyGet]
        split
        · simp [mut_exec_throw]
        · rcases hrem : record.remoteIdentity with _ | rem
          · simp [mut_exec_throw]
          · simp only [mut_exec_pure, Prod.mk.injEq, Except.ok.injEq]
            rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    rcases henc : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C codec spqr ptext
        (record.encryptAddresses addrs) coins) o with ⟨_ | msg', o'⟩
    · rw [henc] at h; cases h
    · rw [henc] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt at henc; simp only [mut_exec_bind, mut_exec_get] at henc
      cases hpan : spqr.sendPanics o.pqrState coins
      · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at henc
        rcases hspqr : spqr.send o.pqrState coins with _ | ⟨newPq, salt, pm⟩
        · simp [hspqr, mut_exec_throw] at henc
        · simp only [hspqr, mut_exec_bind] at henc
          rcases hn : o.senderChainKey.nextChainKey C.F with _ | nextCk
          · simp [hn, mut_exec_liftE] at henc
          · simp only [hn, mut_exec_liftE, mut_exec_set, mut_exec_pure, Prod.mk.injEq] at henc
            rcases henc with ⟨-, rfl⟩; rcases htaken with ⟨hrc, hrem, hpq⟩
            exact ⟨hrc, hrem, salt, pm,
              by simpa [CryptoGames.LibsignalSession.OutgoingTripleRatchet.applyToSessionState, hpq] using hspqr⟩
      · simp [hpan, mut_exec_throw] at henc

private theorem tryDecryptFromRecord_ok_struct {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record s : SessionState PQ) (pt : Bytes)
    (h : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord C spqr expected m msgType coins record = (.ok pt, s)) :
    (RecvChainsOk record.receiverChains → RecvChainsOk s.receiverChains) ∧
    s.remoteIdentity = record.remoteIdentity ∧
    ∃ salt, spqr.recv record.pqRatchetState m.pqRatchet = .ok (s.pqRatchetState, salt) := by
  unfold CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord at h; split_ifs at h
  · cases h
  · rcases hd : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.SessionState.tryDecryptWithState C spqr expected m msgType coins)
        record with ⟨_ | pt', upd⟩
    · rw [hd] at h; cases h
    · rw [hd] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold CryptoGames.LibsignalSession.SessionState.tryDecryptWithState CryptoGames.LibsignalSession.TripleRatchet.fromSessionState
        CryptoGames.LibsignalSession.SessionState.takeRatchetState CryptoGames.LibsignalSession.SessionState.takePqRatchetState at hd
      simp only [mut_exec_bind, mut_exec_get, mut_exec_modifyGet] at hd
      rcases hrem : record.remoteIdentity with _ | rem
      · simp [hrem, mut_exec_throw] at hd
      · simp only [hrem, mut_exec_pure] at hd
        set tr0 : TripleRatchet PQ := ⟨⟨record.rootKey, record.senderChain, record.receiverChains,
          record.previousCounter, maxForwardJumps⟩, record.pqRatchetState, record.localIdentity,
          rem⟩
        rcases hdec : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.decrypt C spqr expected m msgType coins) tr0 with
          ⟨_ | pt0, tr'⟩
        · simp [hdec, mut_exec_liftE] at hd
        · simp only [hdec, mut_exec_liftE, mut_exec_modify, Prod.mk.injEq] at hd
          rcases hd with ⟨-, rfl⟩; unfold CryptoGames.LibsignalSession.TripleRatchet.decrypt at hdec
          simp only [mut_exec_bind] at hdec
          rcases hens : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet
              (CryptoGames.LibsignalSession.RatchetState.ensureReceiverChain C m.senderRatchetKey coins)) tr0 with ⟨_ | ck, tr1⟩
          · rw [hens] at hdec; cases hdec
          · rw [hens] at hdec; dsimp only at hdec
            rcases onRatchet_ok _ tr0 tr1 ck hens with ⟨hens_r, hpq1⟩
            rcases hcons : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet
                (CryptoGames.LibsignalSession.RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType)) tr1
                with ⟨_ | mkg, tr2⟩
            · rw [hcons] at hdec; cases hdec
            · rw [hcons] at hdec; dsimp only at hdec
              rcases onRatchet_ok _ tr1 tr2 mkg hcons with ⟨hcons_r, hpq2⟩
              simp only [mut_exec_get] at hdec
              cases hpan : spqr.recvPanics tr2.pqrState m.pqRatchet
              · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
                rcases hspqr : spqr.recv tr2.pqrState m.pqRatchet with err | ⟨newPq, salt⟩
                · cases err <;> simp [hspqr, mut_exec_throw] at hdec
                · simp only [hspqr, mut_exec_bind, mut_exec_pure] at hdec; split_ifs at hdec
                  · simp [mut_exec_throw] at hdec
                  · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F salt).cipherKey
                        (mkg.generateKeys C.F salt).iv m.ciphertext with _ | ptext
                    · simp [haes, mut_exec_throw] at hdec
                    · simp only [haes, mut_exec_bind, mut_exec_modify, mut_exec_pure,
                        Prod.mk.injEq] at hdec
                      rcases hdec with ⟨-, rfl⟩
                      refine ⟨fun hrc0 => consumeMessageKey_recvChainsOk C.F m.senderRatchetKey ck
                        m.counter msgType tr1.ratchet tr2.ratchet mkg
                        (ensureReceiverChain_recvChainsOk C m.senderRatchetKey coins tr0.ratchet
                          tr1.ratchet ck hrc0 hens_r) hcons_r, rfl, salt, ?_⟩
                      simpa [CryptoGames.LibsignalSession.TripleRatchet.applyToSessionState,
                        CryptoGames.LibsignalSession.SessionState.clearUnacknowledgedPreKeyMessage, hpq2, hpq1, tr0] using hspqr
              · simp [hpan, mut_exec_throw] at hdec

private theorem reachPq_invariants {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    RecvChainsOk g.session.receiverChains ∧
    (∃ rem, g.session.remoteIdentity = some rem) ∧
    x.aliceBaseKey.length = 33 ∧
    (∀ k, x.kyber = some k → k.ciphertext.length = 1569) ∧
    TopStateTight W.C.F W.Q.K g.session.pqRatchetState := by
  induction hR with
  | initiate X' _ me' b t _ _ hi =>
    unfold initiateState at hi
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X' W) (initiateInput W me' b t) with
      _ | ⟨dk, _⟩
    · simp [hinit] at hi
    · rw [hinit] at hi; dsimp only at hi; unfold initializeInitiatorSession at hi
      dsimp only [bind, Except.bind, pure, Except.pure] at hi
      rcases hrc : rootCreateChain W.C (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (CryptoGames.LibsignalSession.KeyPair.generate W.C (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨_, _⟩
      · simp [hrc] at hi
      · rw [hrc] at hi; simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩
        refine ⟨recvChainsOk_addReceiverChain
          (CryptoGames.LibsignalSession.SessionState.new currentVersion ⟨(keyPairOf W.C me'.idPriv).publicKey⟩
            ⟨⟨b.idPub⟩⟩ _ _) ⟨b.spkPub⟩ ⟨_, 0⟩ recvChainsOk_nil,
          ⟨⟨⟨b.idPub⟩⟩, rfl⟩, publicKey_serialize_length _, ?_,
          topStateTight_init W.C.F W.Q.K .a2b _⟩
        intro k hk
        simp only [initiatorRecordExtras, Option.some.injEq] at hk
        subst hk; simp [kyberKey]
  | recvPrekey X' P me' k m rc _ _ _ hr =>
    unfold recvPrekeyState at hr
    rcases htf : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htf] at hr
    · rw [htf] at hr; dsimp only at hr
      by_cases hids : m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId
      · simp only [hids, ↓reduceIte] at hr; cases hr
      · simp only [hids, ↓reduceIte] at hr
        rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X' W) (acceptInput W me' k m) with
          _ | dk
        · simp [hacc] at hr
        · rw [hacc] at hr; dsimp only at hr
          set st0 : SessionState Bytes :=
            initializeRecipientSession (pqxdhSpqrSession W) ⟨(keyPairOf W.C me'.idPriv).publicKey⟩
              ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey)) (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          rcases hd : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with ⟨err | pt', st⟩
          · rw [hd] at hr; cases err <;> cases hr
          · rw [hd] at hr; simp only [Option.some.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨rfl, rfl, rfl⟩
            obtain ⟨hrc_fn, hrem, salt, hspqr⟩ := tryDecryptFromRecord_ok_struct W.C
              (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc
              st0 st pt' hd
            exact ⟨hrc_fn recvChainsOk_nil, ⟨⟨⟨m.idPub⟩⟩, hrem⟩,
              by simp [responderRecordExtras, djbKey],
              fun _ hky => by simp [responderRecordExtras] at hky,
              topStateTight_recv W.C.F W.Q.K (topStateTight_init W.C.F W.Q.K .b2a _) hspqr⟩
  | @send _ _ g_s m r _ _ ih =>
    unfold CryptoGames.LibsignalSession.Params.send
    rcases hm : CryptoGames.LibsignalSession.SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session
        with ⟨_ | msg, s⟩
    · exact ih
    · dsimp only
      obtain ⟨hrc_eq, hrem_eq, salt, pm, hspqr⟩ := messageEncrypt_ok_struct
        (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hm
      rcases ih with ⟨hrc, ⟨rem, hrem⟩, habk, hky, htop⟩
      exact ⟨hrc_eq.symm ▸ hrc, ⟨rem, hrem_eq.trans hrem⟩, habk, hky,
        topStateTight_send W.C.F W.Q.K htop hspqr⟩
  | @recv _ _ g_r _ c rc _ _ _ hrec ih =>
    unfold CryptoGames.LibsignalSession.Params.receive at hrec
    rcases htf : CryptoGames.LibsignalSession.SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper
          rc g_r.session with ⟨_ | pt, s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec; simp only [Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, -⟩
        obtain ⟨hrc_fn, hrem_eq, salt, hspqr⟩ := tryDecryptFromRecord_ok_struct
          (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session s pt hd
        rcases ih with ⟨hrc, ⟨rem, hrem⟩, habk, hky, htop⟩
        exact ⟨hrc_fn hrc, ⟨rem, hrem_eq.trans hrem⟩, habk, hky,
          topStateTight_recv W.C.F W.Q.K htop hspqr⟩

private theorem lenField_len_le (tag : Nat) (payload : Bytes) :
    (lenField tag payload).length ≤ 20 + payload.length := by
  unfold lenField; simp only [List.length_append]
  have h1 := encodeKey_len_le tag .lengthDelimited; have h2 := encodeVarint_len_le (BitVec.ofNat 64 payload.length); omega

private theorem bytesField_len_le (tag : Nat) (v : Bytes) : (bytesField tag v).length ≤ 20 + v.length := by
  unfold bytesField; split_ifs <;> [simp; exact lenField_len_le tag v]

private theorem uint32Field_len_le (tag : Nat) (v : BitVec 32) : (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field; split_ifs
  · simp
  · rw [List.length_append]; have h1 := encodeKey_len_le tag .varint; have h2 := encodeVarint_len_le (v.setWidth 64); omega

private theorem uint64FieldX_len_le (tag : Nat) (v : BitVec 64) : (uint64FieldX tag v).length ≤ 20 := by
  unfold uint64FieldX; split_ifs
  · simp
  · rw [List.length_append]; have h1 := encodeKey_len_le tag .varint; have h2 := encodeVarint_len_le v; omega

private theorem int32FieldX_len_le (tag : Nat) (v : BitVec 32) : (int32FieldX tag v).length ≤ 20 := by
  unfold int32FieldX; split_ifs
  · simp
  · rw [List.length_append]; have h1 := encodeKey_len_le tag .varint; have h2 := encodeVarint_len_le (v.signExtend 64); omega

private theorem optUint32FieldX_len_le (tag : Nat) (ov : Option (BitVec 32)) : (optUint32FieldX tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [optUint32FieldX]
  | some v => unfold optUint32FieldX; rw [List.length_append]; have h1 := encodeKey_len_le tag .varint; have h2 := encodeVarint_len_le (v.setWidth 64); omega

private theorem msgField_len_le (tag : Nat) (ob : Option Bytes) (B : Nat)
    (hB : ∀ b, ob = some b → b.length ≤ B) : (msgField tag ob).length ≤ 20 + B := by
  cases ob with
  | none => simp [msgField]
  | some b => dsimp only [msgField]; have h1 := lenField_len_le tag b; have h2 := hB b rfl; omega

private theorem length_flatten_map_le {α : Type} :
    ∀ (l : List α) (f : α → Bytes) (B : Nat),
      (∀ a ∈ l, (f a).length ≤ B) → ((l.map f).flatten).length ≤ B * l.length
  | [], _, _, _ => by simp
  | a :: tl, f, B, hf => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have ha := hf a (List.mem_cons_self ..)
    have htl := length_flatten_map_le tl f B (fun y hy => hf y (List.mem_cons_of_mem a hy))
    rw [Nat.mul_add, Nat.mul_one]; omega

private theorem encChainKey_len_le (ck : ChainKey) : (encChainKey ck).length ≤ 72 := by
  unfold encChainKey; rw [List.length_append]
  have h1 := uint32Field_len_le 1 ck.index
  have h2 := bytesField_len_le 2 (CryptoGames.HMAC.keyToBytes32 ck.key)
  rw [keyToBytes32_length] at h2; omega

private theorem encSenderChain_len_le (c : SenderChain) : (encSenderChain c).length ≤ 197 := by
  unfold encSenderChain; simp only [List.length_append]
  have h1 := bytesField_len_le 1 c.ratchetKey.publicKey.serialize
  rw [publicKey_serialize_length] at h1
  have h2 := bytesField_len_le 2 c.ratchetKey.privateKey.bytes.toList
  rw [privateKey_bytes_length] at h2
  have h3 := msgField_len_le 3 (some (encChainKey c.chainKey)) 72
    (fun _ hb => Option.some.inj hb ▸ encChainKey_len_le c.chainKey)
  omega

private theorem encReceiverChain_len_le (c : ReceiverChain)
    (hlen : c.messageKeys.length ≤ maxMessageKeys)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32) :
    (encReceiverChain c).length ≤ 184145 := by
  unfold encReceiverChain; simp only [List.length_append]
  have h1 := bytesField_len_le 1 c.senderRatchetKey.serialize
  rw [publicKey_serialize_length] at h1
  have h2 := msgField_len_le 3 (c.chainKey.map encChainKey) 72 (by
    intro b hb; rcases hck : c.chainKey with _ | ck <;> rw [hck] at hb
    · cases hb
    · injection hb with hb'; subst hb'; exact encChainKey_len_le ck)
  have h3 := length_flatten_map_le c.messageKeys (fun mk => lenField 4 (encMessageKey mk)) 92 (by
    intro mk hmk
    have hmk_len : (encMessageKey mk).length ≤ 72 := by
      unfold encMessageKey; rw [List.length_append]
      have hu := uint32Field_len_le 1 mk.counter
      have hb := bytesField_len_le 5 mk.seed
      rw [hseeds mk hmk] at hb; omega
    have hl := lenField_len_le 4 (encMessageKey mk); omega)
  have hm : maxMessageKeys = 2000 := rfl; omega

/-- Every `ReachablePqxdhSession` record encodes within `fileCapBytes`. -/
theorem reachable_sessionRecord_le_fileCap {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ 1_209_331 ∧
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes := by
  obtain ⟨hrc, ⟨rem, hrem⟩, habk, hky, htop⟩ := reachPq_invariants hR
  have hpq : g.session.pqRatchetState.length ≤ 286196 :=
    topStateTight_length_le W.C.F W.Q.K htop
  dsimp only [encodeRecordUnderExtras, msgField]
  have houter := lenField_len_le 1 (encStateUnderExtras x g.session)
  have henc : (encStateUnderExtras x g.session).length ≤ g.session.pqRatchetState.length + 923115 := by
    unfold encStateUnderExtras; simp only [List.length_append]
    have hf1 := uint32Field_len_le 1 g.session.sessionVersion
    have hf2 := bytesField_len_le 2 g.session.localIdentity.serialize
    rw [identityKey_serialize_length] at hf2
    have hf3 : (bytesField 3 ((g.session.remoteIdentity.map CryptoGames.LibsignalSession.IdentityKey.serialize).getD [])).length ≤
        53 := by
      rw [hrem]; dsimp only [Option.map, Option.getD]
      have h := bytesField_len_le 3 rem.serialize
      rw [identityKey_serialize_length] at h; omega
    have hf4 := bytesField_len_le 4 (CryptoGames.HMAC.keyToBytes32 g.session.rootKey)
    rw [keyToBytes32_length] at hf4
    have hf5 := uint32Field_len_le 5 g.session.previousCounter
    have hf6 := msgField_len_le 6 (g.session.senderChain.map encSenderChain) 197 (by
      intro b hb; rcases hsc : g.session.senderChain with _ | sc <;> rw [hsc] at hb
      · cases hb
      · injection hb with hb'; subst hb'; exact encSenderChain_len_le sc)
    have hf7 := length_flatten_map_le g.session.receiverChains
      (fun c => lenField 7 (encReceiverChain c)) 184165 (by
        intro rc hrc_mem
        have hl := lenField_len_le 7 (encReceiverChain rc)
        have he := encReceiverChain_len_le rc (hrc.2 rc hrc_mem).1 (hrc.2 rc hrc_mem).2
        omega)
    have hrc_max : g.session.receiverChains.length ≤ 5 := hrc.1
    have hf9 := msgField_len_le 9
      (if g.session.pendingPreKey then some (encPendingPreKeyX x.pending) else none) 113 (by
        intro b hb; split_ifs at hb
        injection hb with hb'; subst hb'
        unfold encPendingPreKeyX; simp only [List.length_append]
        have p1 := optUint32FieldX_len_le 1 x.pending.preKeyId
        have p2 := bytesField_len_le 2 x.pending.baseKey.serialize
        rw [publicKey_serialize_length] at p2
        have p3 := int32FieldX_len_le 3 x.pending.signedPreKeyId
        have p4 := uint64FieldX_len_le 4 x.pending.timestamp; omega)
    have hf10 := uint32Field_len_le 10 x.remoteRegistrationId
    have hf11 := uint32Field_len_le 11 x.localRegistrationId
    have hf13 := bytesField_len_le 13 x.aliceBaseKey; rw [habk] at hf13
    have hf14 := msgField_len_le 14
      (if g.session.pendingPreKey then x.kyber.map encPendingKyberX else none) 1609 (by
        intro b hb; split_ifs at hb
        rcases hky0 : x.kyber with _ | ky <;> rw [hky0] at hb
        · cases hb
        · injection hb with hb'; subst hb'
          unfold encPendingKyberX; rw [List.length_append]
          have k1 := uint32Field_len_le 1 ky.preKeyId
          have k2 := bytesField_len_le 2 ky.ciphertext
          rw [hky ky hky0] at k2; omega)
    have hf15 := bytesField_len_le 15 g.session.pqRatchetState
    omega
  unfold fileCapBytes
  omega

/-! ## Ciphertext wire length bound -/

private theorem addrs_len_36 (s r : Party) (a : Bytes)
    (h : serializedPartyAddresses CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse s r =
      some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  rcases hs : CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
      (CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName s)) with
    _ | vs <;> rw [hs] at h
  · cases h
  · dsimp only [bind, Option.bind] at h
    rcases hr : CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse
        CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
        (CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName r)) with
      _ | vr <;> rw [hr] at h
    · cases h
    · simp only [pure, Option.some.injEq] at h; subst h
      simp only [CryptoVerification.LibsignalTripleRatchetRepr.addrBytes, List.length_append,
        List.length_cons, List.Vector.toList_length, List.length_nil]

private theorem messageEncrypt_serialized_len_le (W : PEParams) (g : GhostState Bytes)
    (m r : Bytes) (msg : SignalMessage) (s : SessionState Bytes)
    (hm : CryptoGames.LibsignalSession.SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) m r g.session = (.ok msg, s)) :
    msg.serialized.length ≤ m.length + 300 := by
  unfold CryptoGames.LibsignalSession.SessionState.messageEncrypt CryptoGames.LibsignalSession.OutgoingTripleRatchet.fromSessionState
    CryptoGames.LibsignalSession.SessionState.takePqRatchetState at hm
  simp only [mut_exec_bind, mut_exec_get] at hm
  rcases hsc : g.session.senderChain with _ | sc
  · simp [hsc, mut_exec_throw] at hm
  · simp only [hsc, mut_exec_bind, mut_exec_modifyGet, mut_exec_get] at hm
    split_ifs at hm
    · simp [mut_exec_throw] at hm
    · rcases hrem : g.session.remoteIdentity with _ | remote
      · simp [hrem, mut_exec_throw] at hm
      · simp only [hrem, mut_exec_pure] at hm
        unfold CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt CryptoGames.LibsignalSession.OutgoingTripleRatchet.applyToSessionState at hm
        simp only [mut_exec_bind, mut_exec_get] at hm
        cases hpan : (pqxdhSpqrSession W).sendPanics g.session.pqRatchetState r
        case true => simp [hpan, mut_exec_throw] at hm
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hm
        rcases hs : (pqxdhSpqrSession W).send g.session.pqRatchetState r with _ | ⟨pq', key, pm⟩
        · simp [hs, mut_exec_throw] at hm
        · have hpmlen : pm.length ≤ 64 := by
            have hs' : (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).send
                g.session.pqRatchetState r = some (pq', key, pm) := hs
            exact spqrV1Send_msg_len_le W.C.F W.Q.K g.session.pqRatchetState r pq' key pm hs'
          simp only [hs, mut_exec_pure, mut_exec_bind] at hm
          rcases hn : sc.chainKey.nextChainKey W.C.F with _ | next
          · simp [hn, mut_exec_liftE] at hm
          · simp only [hn, mut_exec_liftE,
              mut_exec_set, Prod.mk.injEq, Except.ok.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩
            have hblk : ∀ l : List (BitVec 128),
                (l.flatMap CryptoGames.CBC.blockToBytesLE).length = 16 * l.length := by
              intro l; induction l with
              | nil => rfl
              | cons b t ih =>
                have hb : (CryptoGames.CBC.blockToBytesLE b).length = 16 := by simp [CryptoGames.CBC.blockToBytesLE]
                simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, hb]; omega
            have hct : ∀ k iv, (aesCbcEncrypt W.C.E k iv m).length = 16 * (m.length / 16 + 1) := by
              intro k iv; unfold aesCbcEncrypt; rw [hblk, List.Vector.toList_length]; rfl
            have had6 : (encodeBytesField 6
                (g.session.encryptAddresses ((pqxdhSessionParams W).sendAddrs g.party))).length ≤
                56 := by
              unfold CryptoGames.LibsignalSession.SessionState.encryptAddresses pqxdhSessionParams CryptoGames.LibsignalSession.Params.sendAddrs
              split_ifs
              · cases g.party <;> {
                  dsimp only
                  cases had : serializedPartyAddresses
                      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse _ _ with
                  | none => simp [encodeBytesField]
                  | some ad =>
                    have h1 := encodeBytesField_some_len_le 6 ad
                    have h2 := addrs_len_36 _ _ ad had; omega }
              · simp [encodeBytesField]
            have hrk : sc.ratchetKey.publicKey.serialize.length = 33 :=
              publicKey_serialize_length _
            have h5 : (encodeBytesField 5 (if pm.isEmpty then none else some pm)).length ≤
                20 + pm.length := by
              split <;> [simp [encodeBytesField]; exact encodeBytesField_some_len_le 5 pm]
            dsimp only [CryptoGames.LibsignalSession.SignalMessage.new]; rw [List.length_append]
            refine Nat.le_trans (Nat.add_le_add_left (List.length_take_le 8 _) _) ?_
            dsimp only [serializeContent, protoSignalCodec,
              CryptoVerification.LibsignalProtoCodec.encode]
            simp only [List.length_append, List.length_cons]
            have h1 := encodeBytesField_some_len_le 1 sc.ratchetKey.publicKey.serialize
            have h2 := encodeUint32Field_len_le 2 (some sc.chainKey.index)
            have h3 := encodeUint32Field_len_le 3 (some g.session.previousCounter)
            have h4 := encodeBytesField_some_len_le 4 (aesCbcEncrypt W.C.E
              ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F key).cipherKey
              ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F key).iv m)
            have h4' := hct ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F key).cipherKey
              ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F key).iv
            omega

private theorem preKeyWire_len_le (x : RecordExtras) (st : SessionState Bytes) (msg : SignalMessage)
    (hky : ∀ k, x.kyber = some k → k.ciphertext.length = 1569)
    (hmsg : msg.serialized.length < 2 ^ 32) :
    (wirePrekey :: firstMessageBody x st msg).length ≤ msg.serialized.length + 1717 := by
  unfold firstMessageBody CryptoGames.LibsignalSessionApi.PreKeySignalMessage.new CryptoGames.LibsignalSessionApi.ProtoPreKeySignalMessage.encode
  dsimp only
  simp only [List.length_cons, List.length_append]
  have hf1 := prost_uint32Field_len_le (tag := 1) (by omega) x.pending.preKeyId
  have hf2 := prost_bytesField_opt_len_le (tag := 2) (by omega)
    (some x.pending.baseKey.serialize) 33 (by
      intro bs hbs; injection hbs with hbs'; subst hbs'
      rw [publicKey_serialize_length]; omega)
  have hf3 := prost_bytesField_opt_len_le (tag := 3) (by omega)
    (some st.localIdentity.serialize) 33 (by
      intro bs hbs; injection hbs with hbs'; subst hbs'
      rw [identityKey_serialize_length]; omega)
  have hf4 := prost_bytesField_opt_len_le (tag := 4) (by omega)
    (some msg.serialized) msg.serialized.length (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; exact ⟨Nat.le_refl _, hmsg⟩)
  have hf5 := prost_uint32Field_len_le (tag := 5) (by omega) (some x.localRegistrationId)
  have hf6 := prost_uint32Field_len_le (tag := 6) (by omega) (some x.pending.signedPreKeyId)
  have hf7 := prost_uint32Field_len_le (tag := 7) (by omega)
    ((x.kyber.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)).map (·.preKeyId))
  have hf8 := prost_bytesField_opt_len_le (tag := 8) (by omega)
    ((x.kyber.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)).map (·.ciphertext))
    1569 (by
      intro bs hbs; rcases hk : x.kyber with _ | k <;> rw [hk] at hbs
      · cases hbs
      · simp only [Option.map_some, Option.some.injEq] at hbs; subst hbs
        have hlen := hky k hk; omega)
  omega

/-- Every ciphertext wire emitted by `pqSendModel` on `m.length ≤ maxPlaintextBytes` from a
reachable session has length at most `stdinCapBytes`. -/
theorem honest_send_ciphertext_le_stdinCap {W : PEParams} {st st' : PqParty}
    {m r wire : List (BitVec 8)}
    (hreach : ∀ x g, st.session = some (x, g) →
      ∃ g₀ : GhostState Bytes, ReachablePqxdhSession W st.me x g₀ ∧ g₀.session = g.session)
    (hm : m.length ≤ maxPlaintextBytes)
    (hsend : pqSendModel W st m r = some (some (st', wire))) :
    wire.length ≤ 1_002_030 ∧ wire.length ≤ stdinCapBytes := by
  unfold pqSendModel at hsend
  rcases hsess : st.session with _ | ⟨x, g⟩ <;> rw [hsess] at hsend
  · cases hsend
  · dsimp only at hsend
    rcases henc : CryptoGames.LibsignalSession.SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with ⟨err | msg, s⟩ <;>
      rw [henc] at hsend
    · cases err <;> simp at hsend
    · dsimp only at hsend
      rcases hrem : g.session.remoteIdentity with _ | k <;> rw [hrem] at hsend
      · cases hsend
      · dsimp only at hsend
        by_cases htr : (!st.trusts k) = true
        · simp [htr] at hsend
        · simp only [htr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hsend
          rcases hsend with ⟨-, hwire⟩; subst hwire
          have hinner := messageEncrypt_serialized_len_le W g m r msg s henc
          obtain ⟨g₀, hR, _⟩ := hreach x g hsess
          have hky := (reachPq_invariants hR).2.2.2.1
          have hcap : stdinCapBytes = 1_048_576 := rfl
          unfold maxPlaintextBytes at hm
          by_cases hpend : g.session.pendingPreKey = true
          · simp only [hpend, ↓reduceIte]
            have hpk := preKeyWire_len_le x g.session msg hky (by omega); omega
          · simp only [hpend, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega

/-! ## Coins tape length bound -/

/-- Number of coin bytes drawn by `keygen n`. -/
def cliKeygenCoinsNeeded (n : Nat) : Nat := 260 + 160 * n

/-- Maximum coin bytes required by a single CLI invocation with `keygen` count `n`. -/
def cliCoinsNeeded (n : Nat) : Nat := max initiateTapeLen (cliKeygenCoinsNeeded n)

/-- Every honest CLI coins tape (`n ≤ 100`) fits within `fileCapBytes`. -/
theorem honest_coins_le_fileCap {n : Nat} (hn : n ≤ 100) :
    cliCoinsNeeded n ≤ fileCapBytes ∧
    initiateTapeLen ≤ fileCapBytes ∧ 64 ≤ fileCapBytes ∧ 32 ≤ fileCapBytes := by
  unfold cliCoinsNeeded cliKeygenCoinsNeeded initiateTapeLen fileCapBytes
  omega

/-! ## Bundle and party store file bounds -/

/-- Every bundle file in `(publicBundleOf b).files dir` fits within `fileCapBytes`, with `bundleDir`
paths shorter than `cliPathMaxBytes`. -/
theorem publicBundleOf_files_le_fileCap (b : PreKeyBundleFields) (dir : String) :
    (∀ p bs, (p, bs) ∈ (publicBundleOf b).files dir → bs.length ≤ 1637 ∧ bs.length ≤ fileCapBytes) ∧
    (∀ p bs, (p, bs) ∈ (publicBundleOf b).files bundleDir → p.utf8ByteSize < cliPathMaxBytes) := by
  refine ⟨?_, ?_⟩
  · intro p bs hmem
    unfold CryptoVerification.SignalSession.PublicBundle.files publicBundleOf at hmem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    unfold fileCapBytes
    rcases hmem with (h1 | h2 | h3 | h4) | hopk
    · injection h1 with _ hbs; subst hbs; simp [djbKey]
    · injection h2 with _ hbs; subst hbs; simp [le32]
    · injection h3 with _ hbs; subst hbs; simp [le32, djbKey]
    · injection h4 with _ hbs; subst hbs; simp [le32, kyberKey]
    · cases hb : b.opk with
      | none => simp [hb] at hopk
      | some ik =>
        rcases ik with ⟨id, k⟩
        simp only [hb, Option.map_some, List.mem_singleton, Prod.mk.injEq] at hopk
        rcases hopk with ⟨-, rfl⟩
        simp [le32, djbKey]
  · intro p bs hmem
    unfold CryptoVerification.SignalSession.PublicBundle.files publicBundleOf at hmem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with (h1 | h2 | h3 | h4) | hopk
    · injection h1 with hp _; subst hp; decide
    · injection h2 with hp _; subst hp; decide
    · injection h3 with hp _; subst hp; decide
    · injection h4 with hp _; subst hp; decide
    · cases hb : b.opk with
      | none => simp [hb] at hopk
      | some ik =>
        rcases ik with ⟨id, k⟩
        simp only [hb, Option.map_some, List.mem_singleton, Prod.mk.injEq] at hopk
        rcases hopk with ⟨rfl, -⟩; decide

private theorem baseKeysBytes_len_eq :
    ∀ seen : List (BitVec 32 × List.Vector (BitVec 8) 32),
      (baseKeysBytes seen).length = 37 * seen.length
  | [] => rfl
  | (s, b) :: tl => by
    change ((le32 s ++ djbKey b) ++ baseKeysBytes tl).length = 37 * ((s, b) :: tl).length
    rw [List.length_append, List.length_append, baseKeysBytes_len_eq tl]
    have hs : (le32 s).length = 4 := by simp [le32]
    have hb : (djbKey b).length = 33 := by simp [djbKey]
    simp only [List.length_cons]; omega

private theorem byteArray_loop_len (bs : ByteArray) (i : Nat) (acc : List UInt8) (hi : i ≤ bs.size) :
    (ByteArray.toList.loop bs i acc).length = acc.length + (bs.size - i) := by
  unfold ByteArray.toList.loop
  split
  · rw [byteArray_loop_len bs (i + 1) _ (by omega)]; simp; omega
  · simp; omega
termination_by bs.size - i
decreasing_by
  have : i < bs.size := ‹_›; omega

private theorem textBytes_partyAddress_len_le (P : Party) :
    (textBytes (partyAddress P).text).length ≤ fileCapBytes := by
  have h1 : ∀ s : String, (textBytes s).length = s.utf8ByteSize := by
    intro s
    unfold textBytes CryptoVerification.LibsignalTripleRatchetRepr.utf8 ByteArray.toList
    rw [List.length_map, byteArray_loop_len _ 0 [] (Nat.zero_le _), String.toUTF8_eq_toByteArray]
    have hsz : s.toByteArray.size = s.utf8ByteSize := String.size_toByteArray
    simp [hsz]
  rw [h1]
  have hn : (partyAddressName P).utf8ByteSize ≤ 64 := by cases P <;> decide
  have hd : ".".utf8ByteSize = 1 := by decide
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hc := Char.utf8Size_le_four (Nat.digitChar 1)
  simp only [CryptoVerification.SignalSession.Address.text, partyAddress, ht1, String.utf8ByteSize_append,
    String.utf8ByteSize_singleton, fileCapBytes]
  omega

private theorem signedRecordBytes_len_le (C : Crypto) (id : BitVec 32) (k : PqSignedKey) :
    (signedRecordBytes C id k).length ≤ 227 := by
  dsimp only [signedRecordBytes, CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode]
  simp only [List.length_append]
  have a1 := encodeProto3Uint32_len_le 1 id
  have a2 := encodeProto3Bytes_len_le 2 (djbKey (keyPairOf C k.priv).publicKey.bytes)
  have a3 := encodeProto3Bytes_len_le 3 k.priv.toList
  have a4 := encodeProto3Bytes_len_le 4 k.sig.toList
  have a5 := encodeProto3Fixed64_len_le 5 k.timestamp
  have l2 : (djbKey (keyPairOf C k.priv).publicKey.bytes).length = 33 := by simp [djbKey]
  have l3 : k.priv.toList.length = 32 := k.priv.2
  have l4 : k.sig.toList.length = 64 := k.sig.2
  omega

private theorem kyberRecordBytes_len_le (id : BitVec 32) (k : PqKyberKey) :
    (kyberRecordBytes id k).length ≤ 4900 := by
  dsimp only [kyberRecordBytes, CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode]
  simp only [List.length_append]
  have a1 := encodeProto3Uint32_len_le 1 id
  have a2 := encodeProto3Bytes_len_le 2 (kyberKey k.pub)
  have a3 := encodeProto3Bytes_len_le 3 (0x08#8 :: k.sec.toList)
  have a4 := encodeProto3Bytes_len_le 4 k.sig.toList
  have a5 := encodeProto3Fixed64_len_le 5 k.timestamp
  have l2 : (kyberKey k.pub).length = 1569 := by simp [kyberKey]
  have l3 : (0x08#8 :: k.sec.toList).length = 3169 := by simp
  have l4 : k.sig.toList.length = 64 := k.sig.2
  omega

private theorem oneTimeRecordBytes_len_le (C : Crypto) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    (oneTimeRecordBytes C id sk).length ≤ 125 := by
  dsimp only [oneTimeRecordBytes, CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode]
  simp only [List.length_append]
  have a1 := encodeProto3Uint32_len_le 1 id
  have a2 := encodeProto3Bytes_len_le 2 (djbKey (keyPairOf C sk).publicKey.bytes)
  have a3 := encodeProto3Bytes_len_le 3 sk.toList
  have l2 : (djbKey (keyPairOf C sk).publicKey.bytes).length = 33 := by simp [djbKey]
  have l3 : sk.toList.length = 32 := sk.2
  omega

/-- Every bundle file in `(publicBundleOf b).files dir` and every honest store file in
`encodeDir W st` fits within `fileCapBytes`. -/
theorem honest_party_and_bundle_files_le_fileCap {W : PEParams} {st : PqParty}
    {b : PreKeyBundleFields} {dir : String}
    (hreach : ∀ x g, st.session = some (x, g) →
      ∃ g₀ : GhostState Bytes, ReachablePqxdhSession W st.me x g₀ ∧ g₀.session = g.session)
    (hseen : ∀ i k seen, (i, k, seen) ∈ st.kyberLastResort → seen.length ≤ 56_679) :
    (∀ p bs, (p, bs) ∈ (publicBundleOf b).files dir → bs.length ≤ fileCapBytes) ∧
    (∀ p bs, (p, bs) ∈ encodeDir W st → bs.length ≤ fileCapBytes) := by
  refine ⟨fun p bs h => ((publicBundleOf_files_le_fileCap b dir).1 p bs h).2, ?_⟩
  intro p bs hf
  unfold encodeDir at hf
  simp only [List.mem_append] at hf
  rcases hf with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h1 | h2 | h3
    · injection h1 with _ hbs; subst hbs; exact textBytes_partyAddress_len_le st.party
    · injection h2 with _ hbs; subst hbs
      dsimp only [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode]; simp only [List.length_append]
      have h_pk := encodeProto3Bytes_len_le 1 (djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes)
      have h_sk := encodeProto3Bytes_len_le 2 st.me.idPriv.toList
      have hdjb : (djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes).length = 33 := by
        simp [djbKey]
      have hpriv : st.me.idPriv.toList.length = 32 := st.me.idPriv.2
      unfold fileCapBytes; omega
    · injection h3 with _ hbs; subst hbs; simp [le32, fileCapBytes]
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton, Prod.mk.injEq] at hf_peer
      rcases hf_peer with ⟨-, rfl⟩; rw [identityKey_serialize_length]; unfold fileCapBytes; omega
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨x, g⟩
      simp only [hs, List.mem_singleton, Prod.mk.injEq] at hf_sess; rcases hf_sess with ⟨-, rfl⟩
      obtain ⟨g₀, hR, hgs⟩ := hreach x g hs
      have heq : encodeRecordUnderExtras (fun _ => x) g =
          encodeRecordUnderExtras (fun _ => x) g₀ := by simp [encodeRecordUnderExtras, hgs]
      rw [heq]; exact (reachable_sessionRecord_le_fileCap hR).2
  · rw [List.mem_map] at hf_sig; rcases hf_sig with ⟨⟨i, k⟩, _, heq⟩
    dsimp only at heq; injection heq with _ hbs; subst hbs
    have h := signedRecordBytes_len_le W.C i k; unfold fileCapBytes; omega
  · rw [List.mem_map] at hf_ot; rcases hf_ot with ⟨⟨i, k'⟩, _, heq⟩
    dsimp only at heq; injection heq with _ hbs; subst hbs
    cases k' with
    | none => simp
    | some sk => dsimp only; have h := oneTimeRecordBytes_len_le W.C i sk; unfold fileCapBytes; omega
  · rw [List.mem_map] at hf_kot; rcases hf_kot with ⟨⟨i, k'⟩, _, heq⟩
    dsimp only at heq; injection heq with _ hbs; subst hbs
    cases k' with
    | none => simp
    | some k => dsimp only; have h := kyberRecordBytes_len_le i k; unfold fileCapBytes; omega
  · rw [List.mem_flatten] at hf_klr; rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub; rcases hsub with ⟨⟨i, k, seen⟩, hm, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with hkey | hbk
    · injection hkey with _ hbs; subst hbs
      have h := kyberRecordBytes_len_le i k; unfold fileCapBytes; omega
    · injection hbk with _ hbs; subst hbs
      rw [baseKeysBytes_len_eq]; have hs_le := hseen i k seen hm; unfold fileCapBytes; omega

/-- In `cliPqExp`, every last-resort `.base-keys` list has at most one entry and is never rejected
by `fileCapBytes`. -/
theorem cliPqExp_lastResort_never_cap_rejected {S : SignalPqxdh.Setup} {l : Nat}
    (bi : ModelDriverInstance S l) (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (s : BinState) :
    ∀ i k seen, (i, k, seen) ∈ (cliPqDirOf bi sigs s).kyberLastResort →
      seen.length ≤ 1 ∧ 37 * seen.length ≤ fileCapBytes ∧
      decide (37 * seen.length > fileCapBytes) = false := by
  have hseen1 : ∀ i k seen, (i, k, seen) ∈ (cliPqDirOf bi sigs s).kyberLastResort →
      seen.length ≤ 1 := by
    intro i k seen hmem; unfold cliPqDirOf at hmem
    rcases hp : s.party with _ | _ <;> simp only [hp] at hmem
    · simp [cliPqDirA] at hmem
    · by_cases he : s.bytes.isEmpty = true
      · simp only [he, ↓reduceIte, cliPqxdhDirBobBeforeAccept, List.mem_singleton,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨-, -, rfl⟩; simp
      · simp only [he, Bool.false_eq_true, ↓reduceIte, cliPqxdhDirBobAfterAccept] at hmem
        set m0 := bhExpectedPreKeyMsg bi.meA.regId bi.hdr []
        set d0 := cliPqxdhDirBobBeforeAccept bi sigs
        have hrm_klr : ∀ st0 : PqParty, (removeOpk st0 m0).kyberLastResort = st0.kyberLastResort := by
          intro st0; unfold removeOpk; cases m0.opkId <;> rfl
        rw [hrm_klr] at hmem; unfold markKyberUsed at hmem
        have hkot : List.lookup m0.kpkId d0.kyberOneTime = none := by
          simp [d0, cliPqxdhDirBobBeforeAccept]
        rw [hkot] at hmem
        by_cases hk : (m0.kpkId == bi.keysB.kpkId) = true
        · have hklr : List.lookup m0.kpkId d0.kyberLastResort =
              some ({ pub := bi.keysB.kpkPub, sec := bi.keysB.kpkSec, sig := sigs.2,
                      timestamp := 0#64 }, []) := by
            simp [d0, cliPqxdhDirBobBeforeAccept, List.lookup, hk]
          rw [hklr] at hmem
          simp only [List.length_nil, Nat.mul_zero, fileCapBytes, gt_iff_lt,
            Nat.not_lt_zero, List.not_mem_nil, or_self, ↓reduceIte, Option.getD_some, d0,
            cliPqxdhDirBobBeforeAccept, List.map_cons, List.map_nil] at hmem
          split_ifs at hmem <;>
            (simp only [List.mem_singleton, Prod.mk.injEq] at hmem; rcases hmem with ⟨-, -, rfl⟩; simp)
        · have hk_f : (m0.kpkId == bi.keysB.kpkId) = false := Bool.eq_false_iff.mpr hk
          have hklr : List.lookup m0.kpkId d0.kyberLastResort = none := by
            simp [d0, cliPqxdhDirBobBeforeAccept, List.lookup, hk_f]
          rw [hklr] at hmem
          simp only [d0, cliPqxdhDirBobBeforeAccept, Option.getD_none, List.mem_singleton,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨-, -, rfl⟩; simp
  intro i k seen hmem; have h1 := hseen1 i k seen hmem
  exact ⟨h1, by unfold fileCapBytes; omega, by rw [decide_eq_false_iff_not]; unfold fileCapBytes; omega⟩

/-- Every file in `cliPqDirRaw W (cliPqDirOf bi sigs s) rec` fits within `fileCapBytes` whenever
`rec.length ≤ fileCapBytes`. -/
theorem cliPqExp_dir_files_le_fileCap {S : SignalPqxdh.Setup} {l : Nat}
    (W : PEParams) (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (s : BinState) (rec : List (BitVec 8)) (hrec : rec.length ≤ fileCapBytes)
    (b : PreKeyBundleFields) :
    ∀ p bs, (p, bs) ∈ cliPqDirRaw W (cliPqDirOf bi sigs s) rec → bs.length ≤ fileCapBytes := by
  have hseen_of : ∀ i k seen, (i, k, seen) ∈ (cliPqDirOf bi sigs s).kyberLastResort →
      seen.length ≤ 56_679 := fun i k seen hmem =>
    Nat.le_trans (cliPqExp_lastResort_never_cap_rejected bi sigs s i k seen hmem).1 (by decide)
  set st := cliPqDirOf bi sigs s
  intro p bs hf
  unfold cliPqDirRaw at hf
  simp only [List.mem_append] at hf
  rcases hf with (hf_hdr | hf_rec) | hf_tail
  · have hsub := (honest_party_and_bundle_files_le_fileCap (W := W)
      (st := { st with session := none, signed := [], oneTime := [], kyberOneTime := [],
                       kyberLastResort := [] })
      (b := b) (dir := bundleDir) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)).2
    exact hsub p bs hf_hdr
  · split_ifs at hf_rec
    · simp at hf_rec
    · simp only [List.mem_singleton, Prod.mk.injEq] at hf_rec
      rcases hf_rec with ⟨-, rfl⟩; exact hrec
  · have hm := mem_of_mem_drop 3 (encodeDir W { st with session := none, peerId := none })
      (p, bs) hf_tail
    have hsub := (honest_party_and_bundle_files_le_fileCap (W := W)
      (st := { st with session := none, peerId := none })
      (b := b) (dir := bundleDir) (fun _ _ h => nomatch h) hseen_of).2
    exact hsub p bs hm

end Computational.Proofs.LibsignalCli.CliCapsCompleteness
