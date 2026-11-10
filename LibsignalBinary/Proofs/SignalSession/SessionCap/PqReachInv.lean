/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.PqStep
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow

/-!
# `ReachablePqxdhSession` Invariant and Non-PQ Record Overhead Bound (`≤ 923,135` B)

Proves that every `ReachablePqxdhSession W me x g` satisfies `ReachPqInvCli` and that
`encodeRecordUnderExtras (fun _ => x) g` exceeds `g.session.pqRatchetState.length` by at most
`923,135` bytes (`encodeRecordX_length_le_pq_add_923135`).
-/

@[expose] public section

set_option autoImplicit false

open CryptoGames.LibsignalSession (ChainKey Crypto GhostState IdentityKey MessageKeyGenerator MessageType Mut PrivateKey PublicKey RatchetState ReceiverChain SenderChain SessionState ShaCompress SignalMessage SignalMessageProtoCodec SignalProtocolError Spqr TripleRatchet aesCbcDecrypt currentVersion initializeInitiatorSession initializeRecipientSession liftE maxForwardJumps maxMessageKeys maxReceiverChains rootCreateChain zoom)
open CryptoVerification.E2E (Bytes LocalIdentity PEParams ReachablePqxdhSession RecordExtras acceptInput bytesField djbKey encChainKey encMessageKey encPendingKyberX encPendingPreKeyX encReceiverChain encSenderChain encStateUnderExtras encodeRecordUnderExtras initiateInput initiateState initiatorRecordExtras int32FieldX keyPairOf kyberKey lenField modelPrims msgField ofU8 optUint32FieldX pqxdhSessionParams pqxdhSpqrSession recvPrekeyState responderRecordExtras uint32Field uint64FieldX)
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey encodeVarint encodeVarintAux protoSignalCodec)

namespace LibsignalBinary.Proofs.SignalSession.SessionCap.PqReachInv

open CryptoGames.HKDF (Salt)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1 spqrV1Init spqrV1Session)

/-! ## `Mut` Execution & Elementary List Helpers -/

private theorem Mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (m >>= f) s =
      match CryptoGames.LibsignalSession.Mut.exec m s with | (.ok a, s') => CryptoGames.LibsignalSession.Mut.exec (f a) s' | (.error e, s') => (.error e, s') := by
  cases h : m s with | mk r s' =>
    cases r <;> (simp [CryptoGames.LibsignalSession.Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
      StateT.run, ExceptT.run]; try rfl)
private theorem Mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl
private theorem Mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
private theorem Mut_exec_get {σ : Type} (s : σ) : CryptoGames.LibsignalSession.Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
private theorem Mut_exec_set {σ : Type} (s' s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl
private theorem Mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl
private theorem Mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
private theorem Mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (liftE r : Mut σ α) s = (r, s) := by cases r <;> rfl

private theorem mem_set_or {α : Type} : ∀ (l : List α) (i : ℕ) (v y : α), y ∈ l.set i v → y = v ∨ y ∈ l
  | [], _, _, _, h => by simp at h
  | a :: _, 0, v, y, h => by
    simp only [List.set_cons_zero, List.mem_cons] at h
    exact h.elim Or.inl (Or.inr ∘ List.mem_cons_of_mem a)
  | a :: tl, i + 1, v, y, h => by
    simp only [List.set_cons_succ, List.mem_cons] at h
    exact h.elim (fun hy => hy ▸ Or.inr (List.mem_cons_self ..)) fun htl =>
      (mem_set_or tl i v y htl).elim Or.inl (Or.inr ∘ List.mem_cons_of_mem a)
private theorem length_eraseIdx_le {α : Type} : ∀ (l : List α) (i : ℕ), (l.eraseIdx i).length ≤ l.length
  | [], _ => Nat.le_refl 0 | _ :: _, 0 => by simp
  | _ :: tl, i + 1 => by
    simp only [List.eraseIdx_cons_succ, List.length_cons]
    exact Nat.add_le_add_right (length_eraseIdx_le tl i) 1
private theorem mem_of_mem_eraseIdx {α : Type} :
    ∀ (l : List α) (i : ℕ) (y : α), y ∈ l.eraseIdx i → y ∈ l
  | [], _, _, h => by simp at h | a :: _, 0, _, h => List.mem_cons_of_mem a h
  | a :: tl, i + 1, y, h => by
    simp only [List.eraseIdx_cons_succ, List.mem_cons] at h
    exact h.elim (fun hy => hy ▸ List.mem_cons_self ..)
      (List.mem_cons_of_mem a ∘ mem_of_mem_eraseIdx tl i y)
private theorem mem_of_mem_dropLast {α : Type} : ∀ (l : List α) (y : α), y ∈ l.dropLast → y ∈ l
  | [], _, h => by simp at h | [_], _, h => by simp at h
  | a :: b :: tl, y, h => by
    simp only [List.dropLast_cons_cons, List.mem_cons] at h
    exact h.elim (fun hy => hy ▸ List.mem_cons_self ..)
      (List.mem_cons_of_mem a ∘ mem_of_mem_dropLast (b :: tl) y)
private theorem mem_of_mem_drop {α : Type} : ∀ (n : ℕ) (l : List α) (y : α), y ∈ l.drop n → y ∈ l
  | 0, _, _, h => h | _ + 1, [], _, h => by simp at h
  | n + 1, a :: tl, y, h => List.mem_cons_of_mem a (mem_of_mem_drop n tl y h)

private theorem keyToBytes32_length (k : BitVec 256) : (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by
  simp [CryptoGames.HMAC.keyToBytes32]
private theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [CryptoGames.LibsignalSession.PublicKey.serialize]
private theorem identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 := by
  simp [CryptoGames.LibsignalSession.IdentityKey.serialize, CryptoGames.LibsignalSession.PublicKey.serialize]
private theorem privateKey_bytes_length (sk : PrivateKey) : sk.bytes.toList.length = 32 :=
  sk.bytes.toList_length
private theorem chainKey_messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 :=
  CryptoVerification.LibsignalSpqrV1.length_hmacWith F (CryptoGames.HMAC.keyToBytes32 ck.key) [CryptoGames.Ratchet.messageKeySeed]

/-! ## 1. `ReachPqInvCli` & `reachPq_invCli` -/

/-- Session-and-extras representation invariant for `ReachablePqxdhSession W me x g`. -/
structure ReachPqInvCli (W : PEParams) (me : LocalIdentity) (x : RecordExtras)
    (g : GhostState Bytes) : Prop where
  rootKey_len : (CryptoGames.HMAC.keyToBytes32 g.session.rootKey).length = 32
  senderChain_inv : ∀ sc, g.session.senderChain = some sc →
    sc.ratchetKey.publicKey.serialize.length = 33 ∧
    sc.ratchetKey.privateKey.bytes.toList.length = 32 ∧
    (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key).length = 32
  receiverChains_len : g.session.receiverChains.length ≤ maxReceiverChains
  receiverChains_inv : ∀ rc ∈ g.session.receiverChains,
    rc.senderRatchetKey.serialize.length = 33 ∧
    (∀ ck, rc.chainKey = some ck → (CryptoGames.HMAC.keyToBytes32 ck.key).length = 32) ∧
    rc.messageKeys.length ≤ maxMessageKeys ∧
    (∀ mk ∈ rc.messageKeys, mk.seed.length = 32)
  sessionVersion_eq : g.session.sessionVersion = 4
  localIdentity_eq : g.session.localIdentity = ⟨(keyPairOf W.C me.idPriv).publicKey⟩
  localIdentity_len : g.session.localIdentity.serialize.length = 33
  remoteIdentity_some : ∃ rem, g.session.remoteIdentity = some rem
  remoteIdentity_len : ∀ rem, g.session.remoteIdentity = some rem → rem.serialize.length = 33
  localRegistrationId_eq : x.localRegistrationId = me.regId
  pending_timestamp_eq : x.pending.timestamp = 0#64
  pending_baseKey_serialize : x.pending.baseKey.serialize = x.aliceBaseKey
  pending_baseKey_len : x.pending.baseKey.serialize.length = 33
  aliceBaseKey_len : x.aliceBaseKey.length = 33
  kyber_ciphertext_len : ∀ k, x.kyber = some k → k.ciphertext.length = 1569

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
  · simp [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_throw] at h
  · simp only [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_modifyGet] at h
    rcases h1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with _ | ⟨rk1, rck⟩
    · simp [h1, Mut_exec_liftE] at h
    · simp only [h1, Mut_exec_liftE] at h
      rcases h2 : rootCreateChain C rk1 their (CryptoGames.LibsignalSession.KeyPair.generate C coins).privateKey with _ | ⟨rk2, sck⟩
      · simp [h2] at h
      · simp only [h2, Mut_exec_modify, Mut_exec_pure, Prod.mk.injEq] at h
        rcases h with ⟨-, rfl⟩; exact recvChainsOk_evict_push r.receiverChains their rck hr

private theorem ensureReceiverChain_recvChainsOk (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r' : RatchetState) (ck : ChainKey) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.ensureReceiverChain at h; simp only [Mut_exec_bind, Mut_exec_get] at h
  rcases hf : r.findReceiverChainKey their with _ | (_ | ck0)
  · simp [hf, Mut_exec_liftE] at h
  · simp only [hf, Mut_exec_liftE] at h; exact dhRatchetStep_recvChainsOk C their coins r r' ck hr h
  · simp only [hf, Mut_exec_liftE, Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr

private theorem takeSkippedKey_recvChainsOk (their : PublicKey) (counter : BitVec 32)
    (r r' : RatchetState) (opt : Option MessageKeyGenerator) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.takeSkippedKey their counter) r = (.ok opt, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.takeSkippedKey at h; simp only [Mut_exec_bind, Mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp only [hidx, Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, Mut_exec_throw] at h
    · simp only [hc] at h
      rcases hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp only [hpos, Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
      · simp only [hpos] at h
        rcases hk : c.messageKeys[pos]? with _ | key
        · simp [hk, Mut_exec_throw] at h
        · simp only [hk, Mut_exec_bind, Mut_exec_set, Mut_exec_pure, Prod.mk.injEq] at h
          rcases h with ⟨-, rfl⟩; have hc_ok := hr.2 c (List.mem_of_getElem? hc)
          refine ⟨by rw [List.length_set]; exact hr.1, fun rc hmem => ?_⟩
          rcases mem_set_or r.receiverChains idx _ rc hmem with rfl | hmem0
          · exact ⟨Nat.le_trans (length_eraseIdx_le c.messageKeys pos) hc_ok.1,
              fun mk hmk => hc_ok.2 mk (mem_of_mem_eraseIdx c.messageKeys pos mk hmk)⟩
          · exact hr.2 rc hmem0

private theorem storeSkippedKey_recvChainsOk (their : PublicKey) (key : MessageKeyGenerator)
    (r r' : RatchetState) (u : Unit) (hkey : key.seed.length = 32) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.storeSkippedKey their key) r = (.ok u, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.storeSkippedKey at h; simp only [Mut_exec_bind, Mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp [hidx, Mut_exec_throw] at h
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, Mut_exec_throw] at h
    · simp only [hc, Mut_exec_set, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
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

private theorem advanceChain_recvChainsOk (F : ShaCompress) (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck ck' : ChainKey) (r r' : RatchetState), RecvChainsOk r.receiverChains →
      CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.advanceChain F their counter fuel ck) r = (.ok ck', r') →
      RecvChainsOk r'.receiverChains
  | 0, _, _, _, _, hr, h => by
    unfold CryptoGames.LibsignalSession.RatchetState.advanceChain at h
    simp only [Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
  | fuel + 1, ck, ck', r, r', hr, h => by
    unfold CryptoGames.LibsignalSession.RatchetState.advanceChain at h
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, Mut_exec_bind] at h
      rcases hs : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.storeSkippedKey their (ck.messageKeys F)) r with ⟨_ | u, r1⟩
      · rw [hs] at h; cases h
      · rw [hs] at h; dsimp only at h
        have hr1 := storeSkippedKey_recvChainsOk their (ck.messageKeys F) r r1 u
          (chainKey_messageKeys_seed_length F ck) hr hs
        rcases hn : ck.nextChainKey F with _ | ck1
        · simp [hn, Mut_exec_liftE] at h
        · simp only [hn, Mut_exec_liftE] at h
          exact advanceChain_recvChainsOk F their counter fuel ck1 ck' r1 r' hr1 h
    · simp only [hlt, ↓reduceIte, Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr

private theorem setReceiverChainKey_recvChainsOk (their : PublicKey) (ck : ChainKey)
    (r r' : RatchetState) (u : Unit) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.setReceiverChainKey their ck) r = (.ok u, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.setReceiverChainKey at h; simp only [Mut_exec_bind, Mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp [hidx, Mut_exec_throw] at h
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, Mut_exec_throw] at h
    · simp only [hc, Mut_exec_set, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
      have hc_ok := hr.2 c (List.mem_of_getElem? hc)
      refine ⟨by rw [List.length_set]; exact hr.1, fun rc hmem => ?_⟩
      exact (mem_set_or r.receiverChains idx _ rc hmem).elim (fun e => by rw [e]; exact hc_ok) (hr.2 rc)

private theorem consumeMessageKey_recvChainsOk (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType)
    (r r' : RatchetState) (mkg : MessageKeyGenerator) (hr : RecvChainsOk r.receiverChains)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.consumeMessageKey F their ck counter msgType) r = (.ok mkg, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold CryptoGames.LibsignalSession.RatchetState.consumeMessageKey at h
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, Mut_exec_bind] at h
    rcases htk : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.takeSkippedKey their counter) r with ⟨_ | (_ | k), r1⟩
    · rw [htk] at h; cases h
    · rw [htk] at h; simp [Mut_exec_throw] at h
    · rw [htk] at h; simp only [Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
      exact takeSkippedKey_recvChainsOk their counter r r1 (some k) hr htk
  · simp only [hlt, ↓reduceIte, Mut_exec_bind, Mut_exec_get] at h
    split_ifs at h with hjump
    · simp [Mut_exec_throw] at h
    · simp only [Mut_exec_bind] at h
      rcases hadv : CryptoGames.LibsignalSession.Mut.exec
          (CryptoGames.LibsignalSession.RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r with ⟨_ | ck1, r1⟩
      · rw [hadv] at h; cases h
      · rw [hadv] at h; dsimp only at h
        have hr1 := advanceChain_recvChainsOk F their counter (counter - ck.index).toNat ck ck1 r r1 hr hadv
        rcases hn : ck1.nextChainKey F with _ | ck2
        · simp [hn, Mut_exec_liftE] at h
        · simp only [hn, Mut_exec_liftE] at h
          rcases hset : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.RatchetState.setReceiverChainKey their ck2) r1 with ⟨_ | u, r2⟩
          · rw [hset] at h; cases h
          · rw [hset] at h; simp only [Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
            exact setReceiverChainKey_recvChainsOk their ck2 r1 r2 u hr1 hset

private theorem onRatchet_ok {PQ α : Type} (m : Mut RatchetState α) (t t' : TripleRatchet PQ) (a : α)
    (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet m) t = (.ok a, t')) :
    CryptoGames.LibsignalSession.Mut.exec m t.ratchet = (.ok a, t'.ratchet) ∧ t'.pqrState = t.pqrState ∧
      t'.localIdentityKey = t.localIdentityKey ∧ t'.remoteIdentityKey = t.remoteIdentityKey := by
  unfold CryptoGames.LibsignalSession.TripleRatchet.onRatchet zoom at h; simp only [Mut_exec_bind, Mut_exec_get] at h
  rcases hm : CryptoGames.LibsignalSession.Mut.exec m t.ratchet with ⟨_ | a0, r1⟩
  · simp [hm, Mut_exec_set, Mut_exec_liftE] at h
  · simp only [hm, Mut_exec_set, Mut_exec_liftE, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem messageEncrypt_ok_struct {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC) (addrs : Option Bytes)
    (ptext : Bytes) (coins : PQC) (record s : SessionState PQ) (msg : SignalMessage)
    (h : CryptoGames.LibsignalSession.SessionState.messageEncrypt C codec spqr addrs ptext coins record = (.ok msg, s)) :
    s.receiverChains = record.receiverChains ∧ s.localIdentity = record.localIdentity ∧
    s.remoteIdentity = record.remoteIdentity ∧ s.sessionVersion = record.sessionVersion ∧
    ∃ salt pm, spqr.send record.pqRatchetState coins = some (s.pqRatchetState, salt, pm) := by
  unfold CryptoGames.LibsignalSession.SessionState.messageEncrypt at h
  rcases hfrom : CryptoGames.LibsignalSession.Mut.exec CryptoGames.LibsignalSession.OutgoingTripleRatchet.fromSessionState record with ⟨_ | o, taken⟩
  · rw [hfrom] at h; cases h
  · rw [hfrom] at h; dsimp only at h
    have htaken : taken.receiverChains = record.receiverChains ∧
        taken.localIdentity = record.localIdentity ∧ taken.remoteIdentity = record.remoteIdentity ∧
        taken.sessionVersion = record.sessionVersion ∧ o.pqrState = record.pqRatchetState := by
      revert hfrom; unfold CryptoGames.LibsignalSession.OutgoingTripleRatchet.fromSessionState CryptoGames.LibsignalSession.SessionState.takePqRatchetState
      rcases hsc : record.senderChain with _ | sc
      · simp [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_throw]
      · simp only [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_modifyGet]
        split
        · simp [Mut_exec_throw]
        · rcases hrem : record.remoteIdentity with _ | rem
          · simp [Mut_exec_throw]
          · simp only [Mut_exec_pure, Prod.mk.injEq, Except.ok.injEq]
            rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    rcases henc : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C codec spqr ptext
        (record.encryptAddresses addrs) coins) o with ⟨_ | msg', o'⟩
    · rw [henc] at h; cases h
    · rw [henc] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt at henc; simp only [Mut_exec_bind, Mut_exec_get] at henc
      cases hpan : spqr.sendPanics o.pqrState coins
      · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at henc
        rcases hspqr : spqr.send o.pqrState coins with _ | ⟨newPq, salt, pm⟩
        · simp [hspqr, Mut_exec_throw] at henc
        · simp only [hspqr, Mut_exec_bind] at henc
          rcases hn : o.senderChainKey.nextChainKey C.F with _ | nextCk
          · simp [hn, Mut_exec_liftE] at henc
          · simp only [hn, Mut_exec_liftE, Mut_exec_set, Mut_exec_pure, Prod.mk.injEq] at henc
            rcases henc with ⟨-, rfl⟩; rcases htaken with ⟨hrc, hloc, hrem, hver, hpq⟩
            exact ⟨hrc, hloc, hrem, hver, salt, pm,
              by simpa [CryptoGames.LibsignalSession.OutgoingTripleRatchet.applyToSessionState, hpq] using hspqr⟩
      · simp [hpan, Mut_exec_throw] at henc

private theorem tryDecryptFromRecord_ok_struct {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record s : SessionState PQ) (pt : Bytes)
    (h : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord C spqr expected m msgType coins record = (.ok pt, s)) :
    (RecvChainsOk record.receiverChains → RecvChainsOk s.receiverChains) ∧
    s.localIdentity = record.localIdentity ∧ s.remoteIdentity = record.remoteIdentity ∧
    s.sessionVersion = record.sessionVersion ∧
    ∃ salt, spqr.recv record.pqRatchetState m.pqRatchet = .ok (s.pqRatchetState, salt) := by
  unfold CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord at h; split_ifs at h
  · cases h
  · rcases hd : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.SessionState.tryDecryptWithState C spqr expected m msgType coins) record with
      ⟨_ | pt', upd⟩
    · rw [hd] at h; cases h
    · rw [hd] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold CryptoGames.LibsignalSession.SessionState.tryDecryptWithState CryptoGames.LibsignalSession.TripleRatchet.fromSessionState
        CryptoGames.LibsignalSession.SessionState.takeRatchetState CryptoGames.LibsignalSession.SessionState.takePqRatchetState at hd
      simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_modifyGet] at hd
      rcases hrem : record.remoteIdentity with _ | rem
      · simp [hrem, Mut_exec_throw] at hd
      · simp only [hrem, Mut_exec_pure] at hd
        set tr0 : TripleRatchet PQ := ⟨⟨record.rootKey, record.senderChain, record.receiverChains,
          record.previousCounter, maxForwardJumps⟩, record.pqRatchetState, record.localIdentity, rem⟩
        rcases hdec : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.decrypt C spqr expected m msgType coins) tr0 with
          ⟨_ | pt0, tr'⟩
        · simp [hdec, Mut_exec_liftE] at hd
        · simp only [hdec, Mut_exec_liftE, Mut_exec_modify, Prod.mk.injEq] at hd
          rcases hd with ⟨-, rfl⟩; unfold CryptoGames.LibsignalSession.TripleRatchet.decrypt at hdec; simp only [Mut_exec_bind] at hdec
          rcases hens : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet
              (CryptoGames.LibsignalSession.RatchetState.ensureReceiverChain C m.senderRatchetKey coins)) tr0 with ⟨_ | ck, tr1⟩
          · rw [hens] at hdec; cases hdec
          · rw [hens] at hdec; dsimp only at hdec
            rcases onRatchet_ok _ tr0 tr1 ck hens with ⟨hens_r, hpq1, _, _⟩
            rcases hcons : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet
                (CryptoGames.LibsignalSession.RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType)) tr1 with
              ⟨_ | mkg, tr2⟩
            · rw [hcons] at hdec; cases hdec
            · rw [hcons] at hdec; dsimp only at hdec
              rcases onRatchet_ok _ tr1 tr2 mkg hcons with ⟨hcons_r, hpq2, _, _⟩
              simp only [Mut_exec_get] at hdec; cases hpan : spqr.recvPanics tr2.pqrState m.pqRatchet
              · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
                rcases hspqr : spqr.recv tr2.pqrState m.pqRatchet with err | ⟨newPq, salt⟩
                · cases err <;> simp [hspqr, Mut_exec_throw] at hdec
                · simp only [hspqr, Mut_exec_bind, Mut_exec_pure] at hdec; split_ifs at hdec
                  · simp [Mut_exec_throw] at hdec
                  · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F salt).cipherKey
                        (mkg.generateKeys C.F salt).iv m.ciphertext with _ | ptext
                    · simp [haes, Mut_exec_throw] at hdec
                    · simp only [haes, Mut_exec_bind, Mut_exec_modify, Mut_exec_pure,
                        Prod.mk.injEq] at hdec
                      rcases hdec with ⟨-, rfl⟩
                      refine ⟨fun hrc0 => consumeMessageKey_recvChainsOk C.F m.senderRatchetKey ck
                        m.counter msgType tr1.ratchet tr2.ratchet mkg
                        (ensureReceiverChain_recvChainsOk C m.senderRatchetKey coins tr0.ratchet
                          tr1.ratchet ck hrc0 hens_r) hcons_r, rfl, rfl, rfl, salt, ?_⟩
                      simpa [CryptoGames.LibsignalSession.TripleRatchet.applyToSessionState,
                        CryptoGames.LibsignalSession.SessionState.clearUnacknowledgedPreKeyMessage, hpq2, hpq1, tr0] using hspqr
              · simp [hpan, Mut_exec_throw] at hdec

private theorem mk_reachPqInvCli {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (hrc : RecvChainsOk g.session.receiverChains) (hver : g.session.sessionVersion = 4)
    (hloc : g.session.localIdentity = ⟨(keyPairOf W.C me.idPriv).publicKey⟩)
    (hrem : ∃ rem, g.session.remoteIdentity = some rem) (hreg : x.localRegistrationId = me.regId)
    (hts : x.pending.timestamp = 0#64) (hbk : x.pending.baseKey.serialize = x.aliceBaseKey)
    (habk : x.aliceBaseKey.length = 33) (hky : ∀ k, x.kyber = some k → k.ciphertext.length = 1569) :
    ReachPqInvCli W me x g :=
  ⟨keyToBytes32_length _,
   fun _ _ => ⟨publicKey_serialize_length _, privateKey_bytes_length _, keyToBytes32_length _⟩,
   hrc.1,
   fun rc hm => ⟨publicKey_serialize_length _, fun _ _ => keyToBytes32_length _,
     (hrc.2 rc hm).1, (hrc.2 rc hm).2⟩,
   hver, hloc, identityKey_serialize_length _, hrem, fun rem _ => identityKey_serialize_length rem,
   hreg, hts, hbk, publicKey_serialize_length _, habk, hky⟩

private theorem recvChainsOk_of_invCli {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachPqInvCli W me x g) : RecvChainsOk g.session.receiverChains :=
  ⟨h.receiverChains_len, fun rc hm =>
    ⟨(h.receiverChains_inv rc hm).2.2.1, (h.receiverChains_inv rc hm).2.2.2⟩⟩

/-- Every reachable PQXDH session (`ReachablePqxdhSession W me x g`) satisfies `ReachPqInvCli W me x g`. -/
theorem reachPq_invCli {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (hR : ReachablePqxdhSession W me x g) : ReachPqInvCli W me x g := by
  induction hR with
  | initiate X' P me' b t _ _ hi =>
    unfold initiateState at hi
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X' W) (initiateInput W me' b t) with
      _ | ⟨dk, hdr⟩
    · simp [hinit] at hi
    · rw [hinit] at hi; dsimp only at hi; unfold initializeInitiatorSession at hi
      dsimp only [bind, Except.bind, pure, Except.pure] at hi
      rcases hrc : rootCreateChain W.C (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (CryptoGames.LibsignalSession.KeyPair.generate W.C (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨rk', ck'⟩
      · simp [hrc] at hi
      · rw [hrc] at hi; simp only [Option.some.injEq, Prod.mk.injEq] at hi; rcases hi with ⟨rfl, rfl⟩
        refine mk_reachPqInvCli ?_ rfl rfl ⟨⟨⟨b.idPub⟩⟩, rfl⟩ rfl rfl rfl
          (publicKey_serialize_length _) ?_
        · exact recvChainsOk_addReceiverChain
            (CryptoGames.LibsignalSession.SessionState.new currentVersion ⟨(keyPairOf W.C me'.idPriv).publicKey⟩
              ⟨⟨b.idPub⟩⟩ _ _) ⟨b.spkPub⟩ ⟨_, 0⟩ recvChainsOk_nil
        · intro k hk; simp only [initiatorRecordExtras, Option.some.injEq] at hk; subst hk; simp [kyberKey]
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
            obtain ⟨hrc_fn, hloc, hrem, hver, _, _⟩ :=
              tryDecryptFromRecord_ok_struct W.C (pqxdhSpqrSession W)
                ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 st pt' hd
            exact mk_reachPqInvCli (hrc_fn recvChainsOk_nil) hver hloc ⟨⟨⟨m.idPub⟩⟩, hrem⟩
              rfl rfl rfl (by simp [responderRecordExtras, djbKey]) (fun _ hky => nomatch hky)
  | @send _ _ g_s m r _ _ ih =>
    unfold CryptoGames.LibsignalSession.Params.send
    rcases hm : CryptoGames.LibsignalSession.SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with
      ⟨_ | msg, s⟩
    · exact ih
    · dsimp only
      obtain ⟨hrc_eq, hloc_eq, hrem_eq, hver_eq, _, _, _⟩ :=
        messageEncrypt_ok_struct (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hm
      rcases ih.remoteIdentity_some with ⟨rem, hrem⟩
      exact mk_reachPqInvCli (hrc_eq.symm ▸ recvChainsOk_of_invCli ih)
        (hver_eq.trans ih.sessionVersion_eq) (hloc_eq.trans ih.localIdentity_eq)
        ⟨rem, hrem_eq.trans hrem⟩ ih.localRegistrationId_eq ih.pending_timestamp_eq
        ih.pending_baseKey_serialize ih.aliceBaseKey_len ih.kyber_ciphertext_len
  | @recv _ _ g_r _ c rc _ _ _ hrec ih =>
    unfold CryptoGames.LibsignalSession.Params.receive at hrec
    rcases htf : CryptoGames.LibsignalSession.SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session with ⟨_ | pt, s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec; simp only [Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, -⟩
        obtain ⟨hrc_fn, hloc_eq, hrem_eq, hver_eq, _, _⟩ :=
          tryDecryptFromRecord_ok_struct (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
            ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session s pt hd
        rcases ih.remoteIdentity_some with ⟨rem, hrem⟩
        exact mk_reachPqInvCli (hrc_fn (recvChainsOk_of_invCli ih))
          (hver_eq.trans ih.sessionVersion_eq) (hloc_eq.trans ih.localIdentity_eq)
          ⟨rem, hrem_eq.trans hrem⟩ ih.localRegistrationId_eq ih.pending_timestamp_eq
          ih.pending_baseKey_serialize ih.aliceBaseKey_len ih.kyber_ciphertext_len

/-! ## 2. Non-PQ Record Overhead Bound (`≤ 923,135` B) -/

private theorem encodeVarintAux_length_le :
    ∀ (k : ℕ) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux; split_ifs
    · simp
    · simp only [List.length_cons]; exact Nat.add_le_add_right (encodeVarintAux_length_le k (v >>> 7)) 1

private theorem encodeVarint_length_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v
private theorem encodeKey_length_le (tag : ℕ) (wt : WireType) : (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le _

private theorem lenField_length_le (tag : ℕ) (payload : Bytes) :
    (lenField tag payload).length ≤ 20 + payload.length := by
  unfold lenField; simp only [List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 payload.length); omega

private theorem bytesField_length_le (tag : ℕ) (v : Bytes) :
    (bytesField tag v).length ≤ 20 + v.length := by
  unfold bytesField; split_ifs <;> [simp; exact lenField_length_le tag v]

private theorem uint32Field_length_le (tag : ℕ) (v : BitVec 32) :
    (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field; split_ifs
  · simp
  · rw [List.length_append]
    have h1 := encodeKey_length_le tag .varint; have h2 := encodeVarint_length_le (v.setWidth 64)
    omega

private theorem uint64FieldX_length_le (tag : ℕ) (v : BitVec 64) :
    (uint64FieldX tag v).length ≤ 20 := by
  unfold uint64FieldX; split_ifs
  · simp
  · rw [List.length_append]
    have h1 := encodeKey_length_le tag .varint; have h2 := encodeVarint_length_le v; omega

private theorem int32FieldX_length_le (tag : ℕ) (v : BitVec 32) :
    (int32FieldX tag v).length ≤ 20 := by
  unfold int32FieldX; split_ifs
  · simp
  · rw [List.length_append]
    have h1 := encodeKey_length_le tag .varint; have h2 := encodeVarint_length_le (v.signExtend 64)
    omega

private theorem optUint32FieldX_length_le (tag : ℕ) (ov : Option (BitVec 32)) :
    (optUint32FieldX tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [optUint32FieldX]
  | some v =>
    unfold optUint32FieldX; rw [List.length_append]
    have h1 := encodeKey_length_le tag .varint; have h2 := encodeVarint_length_le (v.setWidth 64)
    omega

private theorem msgField_length_le (tag : ℕ) (ob : Option Bytes) (B : ℕ)
    (hB : ∀ b, ob = some b → b.length ≤ B) : (msgField tag ob).length ≤ 20 + B := by
  cases ob with
  | none => simp [msgField]
  | some b =>
    dsimp only [msgField]; have h1 := lenField_length_le tag b; have h2 := hB b rfl; omega

private theorem length_flatten_map_le {α : Type} :
    ∀ (l : List α) (f : α → Bytes) (B : ℕ),
      (∀ a ∈ l, (f a).length ≤ B) → ((l.map f).flatten).length ≤ B * l.length
  | [], _, _, _ => by simp
  | a :: tl, f, B, hf => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have ha := hf a (List.mem_cons_self ..)
    have htl := length_flatten_map_le tl f B (fun y hy => hf y (List.mem_cons_of_mem a hy))
    rw [Nat.mul_add, Nat.mul_one]; omega

private theorem encChainKey_length_le (ck : ChainKey) : (encChainKey ck).length ≤ 72 := by
  unfold encChainKey; rw [List.length_append]
  have h1 := uint32Field_length_le 1 ck.index
  have h2 := bytesField_length_le 2 (CryptoGames.HMAC.keyToBytes32 ck.key); rw [keyToBytes32_length] at h2; omega

private theorem encSenderChain_length_le (c : SenderChain) : (encSenderChain c).length ≤ 197 := by
  unfold encSenderChain; simp only [List.length_append]
  have h1 := bytesField_length_le 1 c.ratchetKey.publicKey.serialize; rw [publicKey_serialize_length] at h1
  have h2 := bytesField_length_le 2 c.ratchetKey.privateKey.bytes.toList; rw [privateKey_bytes_length] at h2
  have h3 := msgField_length_le 3 (some (encChainKey c.chainKey)) 72
    (fun _ hb => Option.some.inj hb ▸ encChainKey_length_le c.chainKey)
  omega

private theorem encReceiverChain_length_le (c : ReceiverChain)
    (hlen : c.messageKeys.length ≤ maxMessageKeys)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32) :
    (encReceiverChain c).length ≤ 184145 := by
  unfold encReceiverChain; simp only [List.length_append]
  have h1 := bytesField_length_le 1 c.senderRatchetKey.serialize; rw [publicKey_serialize_length] at h1
  have h2 := msgField_length_le 3 (c.chainKey.map encChainKey) 72 (by
    intro b hb; rcases hck : c.chainKey with _ | ck <;> rw [hck] at hb
    · cases hb
    · injection hb with hb'; subst hb'; exact encChainKey_length_le ck)
  have h3 := length_flatten_map_le c.messageKeys (fun mk => lenField 4 (encMessageKey mk)) 92 (by
    intro mk hmk
    have hmk_len : (encMessageKey mk).length ≤ 72 := by
      unfold encMessageKey; rw [List.length_append]
      have hu := uint32Field_length_le 1 mk.counter; have hb := bytesField_length_le 5 mk.seed
      rw [hseeds mk hmk] at hb; omega
    have hl := lenField_length_le 4 (encMessageKey mk); omega)
  have hm : maxMessageKeys = 2000 := rfl; omega

/-- Tight non-PQ overhead bound on `encodeRecordUnderExtras`: under `ReachablePqxdhSession W me x g`,
the encoded record exceeds `g.session.pqRatchetState.length` by at most `923,135` bytes. -/
theorem encodeRecordX_length_le_pq_add_923135
    {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (hR : ReachablePqxdhSession W me x g) :
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ g.session.pqRatchetState.length + 923135 := by
  have inv := reachPq_invCli hR; dsimp only [encodeRecordUnderExtras, msgField]
  have houter := lenField_length_le 1 (encStateUnderExtras x g.session)
  have henc : (encStateUnderExtras x g.session).length ≤ g.session.pqRatchetState.length + 923115 := by
    unfold encStateUnderExtras; simp only [List.length_append]
    have hf1 := uint32Field_length_le 1 g.session.sessionVersion
    have hf2 := bytesField_length_le 2 g.session.localIdentity.serialize; rw [inv.localIdentity_len] at hf2
    have hf3 : (bytesField 3 ((g.session.remoteIdentity.map CryptoGames.LibsignalSession.IdentityKey.serialize).getD [])).length ≤
        53 := by
      rcases inv.remoteIdentity_some with ⟨rem, hrem⟩; rw [hrem]; dsimp only [Option.map, Option.getD]
      have h := bytesField_length_le 3 rem.serialize; rw [inv.remoteIdentity_len rem hrem] at h; omega
    have hf4 := bytesField_length_le 4 (CryptoGames.HMAC.keyToBytes32 g.session.rootKey); rw [inv.rootKey_len] at hf4
    have hf5 := uint32Field_length_le 5 g.session.previousCounter
    have hf6 := msgField_length_le 6 (g.session.senderChain.map encSenderChain) 197 (by
      intro b hb; rcases hsc : g.session.senderChain with _ | sc <;> rw [hsc] at hb
      · cases hb
      · injection hb with hb'; subst hb'; exact encSenderChain_length_le sc)
    have hf7 := length_flatten_map_le g.session.receiverChains
      (fun c => lenField 7 (encReceiverChain c)) 184165 (by
        intro rc hrc; have hl := lenField_length_le 7 (encReceiverChain rc)
        have he := encReceiverChain_length_le rc
          (inv.receiverChains_inv rc hrc).2.2.1 (inv.receiverChains_inv rc hrc).2.2.2
        omega)
    have hrc_max : g.session.receiverChains.length ≤ 5 := inv.receiverChains_len
    have hf9 := msgField_length_le 9
      (if g.session.pendingPreKey then some (encPendingPreKeyX x.pending) else none) 113 (by
        intro b hb; split_ifs at hb
        injection hb with hb'; subst hb'; unfold encPendingPreKeyX; simp only [List.length_append]
        have p1 := optUint32FieldX_length_le 1 x.pending.preKeyId
        have p2 := bytesField_length_le 2 x.pending.baseKey.serialize; rw [inv.pending_baseKey_len] at p2
        have p3 := int32FieldX_length_le 3 x.pending.signedPreKeyId
        have p4 := uint64FieldX_length_le 4 x.pending.timestamp; omega)
    have hf10 := uint32Field_length_le 10 x.remoteRegistrationId
    have hf11 := uint32Field_length_le 11 x.localRegistrationId
    have hf13 := bytesField_length_le 13 x.aliceBaseKey; rw [inv.aliceBaseKey_len] at hf13
    have hf14 := msgField_length_le 14
      (if g.session.pendingPreKey then x.kyber.map encPendingKyberX else none) 1609 (by
        intro b hb; split_ifs at hb
        rcases hky : x.kyber with _ | ky <;> rw [hky] at hb
        · cases hb
        · injection hb with hb'; subst hb'; unfold encPendingKyberX; rw [List.length_append]
          have k1 := uint32Field_length_le 1 ky.preKeyId
          have k2 := bytesField_length_le 2 ky.ciphertext
          rw [inv.kyber_ciphertext_len ky hky] at k2; omega)
    have hf15 := bytesField_length_le 15 g.session.pqRatchetState
    omega
  omega

end LibsignalBinary.Proofs.SignalSession.SessionCap.PqReachInv
