/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
public import LibsignalBinary.Proofs.SignalSession.PqStep
import Computational.Proofs.E2E.BhAdapterIjHelpersV1Core
import LibsignalBinary.Proofs.SignalSession.PqClosure
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-!
# Reachable PQXDH session invariants, SPQR-V1 state growth, and spec-domain closure

Proves session representation invariants (`ReachPqInvCli`) and SPQR-V1 `ValidState` preservation
for `ReachablePqxdhSession`, bounds non-PQ `SessionRecord` encoding overhead by `923,135` bytes,
and establishes multi-step `PqxdhPartyInSpecDomain` closure across `PqSteps`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalCli.Entry

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoGames.HKDF (Salt)
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec CryptoVerification.SignalSession
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1 spqrV1Init spqrV1Session)
open CryptoVerification.SpqrV1.Top.StateSize (ValidState validState_spqrV1Init spqrV1_send_validState_length_le spqrV1_recv_validState_length_le)
open CryptoVerification.E2E.BhAdapterIjHelpersV1 (spqrV1_send_validState_length_le_tight spqrV1_recv_validState_length_le_tight)

private theorem Mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with | (.ok a, s') => Mut.exec (f a) s' | (.error e, s') => (.error e, s') := by
  cases h : m s with | mk r s' =>
    cases r <;> (simp [Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
      StateT.run, ExceptT.run]; try rfl)
private theorem Mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl
private theorem Mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
private theorem Mut_exec_get {σ : Type} (s : σ) : Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
private theorem Mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl
private theorem Mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl
private theorem Mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
private theorem Mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by cases r <;> rfl

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

private theorem keyToBytes32_length (k : BitVec 256) : (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]
private theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]
private theorem identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 := by
  simp [IdentityKey.serialize, PublicKey.serialize]
private theorem privateKey_bytes_length (sk : PrivateKey) : sk.bytes.toList.length = 32 :=
  sk.bytes.toList_length
private theorem chainKey_messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 :=
  LibsignalSpqrV1.length_hmacWith F (HMAC.keyToBytes32 ck.key) [Ratchet.messageKeySeed]

/-! ## Representation invariant `ReachPqInvCli` -/

/-- Session and extras representation invariant for `ReachablePqxdhSession W me x g`. -/
structure ReachPqInvCli (W : PEParams) (me : LocalIdentity) (x : RecordExtras)
    (g : GhostState Bytes) : Prop where
  rootKey_len : (HMAC.keyToBytes32 g.session.rootKey).length = 32
  senderChain_inv : ∀ sc, g.session.senderChain = some sc →
    sc.ratchetKey.publicKey.serialize.length = 33 ∧
    sc.ratchetKey.privateKey.bytes.toList.length = 32 ∧
    (HMAC.keyToBytes32 sc.chainKey.key).length = 32
  receiverChains_len : g.session.receiverChains.length ≤ maxReceiverChains
  receiverChains_inv : ∀ rc ∈ g.session.receiverChains,
    rc.senderRatchetKey.serialize.length = 33 ∧
    (∀ ck, rc.chainKey = some ck → (HMAC.keyToBytes32 ck.key).length = 32) ∧
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
  unfold SessionState.addReceiverChain; dsimp only
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
    RecvChainsOk (RatchetState.evictReceiverChains (cs ++ [⟨their, some ck, []⟩])) := by
  unfold RatchetState.evictReceiverChains
  set cs1 := cs ++ [⟨their, some ck, []⟩]
  refine ⟨by rw [List.length_drop]; omega, fun rc hmem => ?_⟩
  have hmem1 := mem_of_mem_drop (cs1.length - maxReceiverChains) cs1 rc hmem
  rw [List.mem_append] at hmem1; rcases hmem1 with hmem1 | hmem1
  · exact h.2 rc hmem1
  · rw [List.mem_singleton] at hmem1; subst hmem1; exact ⟨Nat.zero_le _, fun _ hm => nomatch hm⟩

private theorem dhRatchetStep_recvChainsOk (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r r' : RatchetState) (ck : ChainKey) (hr : RecvChainsOk r.receiverChains)
    (h : Mut.exec (RatchetState.dhRatchetStep C their coins) r = (.ok ck, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey at h
  rcases hsc : r.senderChain with _ | sc
  · simp [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_throw] at h
  · simp only [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_modifyGet] at h
    rcases h1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with _ | ⟨rk1, rck⟩
    · simp [h1, Mut_exec_liftE] at h
    · simp only [h1, Mut_exec_liftE] at h
      rcases h2 : rootCreateChain C rk1 their (KeyPair.generate C coins).privateKey with _ | ⟨rk2, sck⟩
      · simp [h2] at h
      · simp only [h2, Mut_exec_modify, Mut_exec_pure, Prod.mk.injEq] at h
        rcases h with ⟨-, rfl⟩; exact recvChainsOk_evict_push r.receiverChains their rck hr

private theorem ensureReceiverChain_recvChainsOk (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r' : RatchetState) (ck : ChainKey) (hr : RecvChainsOk r.receiverChains)
    (h : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold RatchetState.ensureReceiverChain at h; simp only [Mut_exec_bind, Mut_exec_get] at h
  rcases hf : r.findReceiverChainKey their with _ | (_ | ck0)
  · simp [hf, Mut_exec_liftE] at h
  · simp only [hf, Mut_exec_liftE] at h; exact dhRatchetStep_recvChainsOk C their coins r r' ck hr h
  · simp only [hf, Mut_exec_liftE, Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr

private theorem takeSkippedKey_recvChainsOk (their : PublicKey) (counter : BitVec 32)
    (r r' : RatchetState) (opt : Option MessageKeyGenerator) (hr : RecvChainsOk r.receiverChains)
    (h : Mut.exec (RatchetState.takeSkippedKey their counter) r = (.ok opt, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold RatchetState.takeSkippedKey at h; simp only [Mut_exec_bind, Mut_exec_get] at h
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
    (h : Mut.exec (RatchetState.storeSkippedKey their key) r = (.ok u, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold RatchetState.storeSkippedKey at h; simp only [Mut_exec_bind, Mut_exec_get] at h
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
      Mut.exec (RatchetState.advanceChain F their counter fuel ck) r = (.ok ck', r') →
      RecvChainsOk r'.receiverChains
  | 0, _, _, _, _, hr, h => by
    unfold RatchetState.advanceChain at h
    simp only [Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
  | fuel + 1, ck, ck', r, r', hr, h => by
    unfold RatchetState.advanceChain at h
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, Mut_exec_bind] at h
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with ⟨_ | u, r1⟩
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
    (h : Mut.exec (RatchetState.setReceiverChainKey their ck) r = (.ok u, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold RatchetState.setReceiverChainKey at h; simp only [Mut_exec_bind, Mut_exec_get] at h
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
    (h : Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r = (.ok mkg, r')) :
    RecvChainsOk r'.receiverChains := by
  unfold RatchetState.consumeMessageKey at h
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, Mut_exec_bind] at h
    rcases htk : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨_ | (_ | k), r1⟩
    · rw [htk] at h; cases h
    · rw [htk] at h; simp [Mut_exec_throw] at h
    · rw [htk] at h; simp only [Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
      exact takeSkippedKey_recvChainsOk their counter r r1 (some k) hr htk
  · simp only [hlt, ↓reduceIte, Mut_exec_bind, Mut_exec_get] at h
    split_ifs at h with hjump
    · simp [Mut_exec_throw] at h
    · simp only [Mut_exec_bind] at h
      rcases hadv : Mut.exec
          (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r with ⟨_ | ck1, r1⟩
      · rw [hadv] at h; cases h
      · rw [hadv] at h; dsimp only at h
        have hr1 := advanceChain_recvChainsOk F their counter (counter - ck.index).toNat ck ck1 r r1 hr hadv
        rcases hn : ck1.nextChainKey F with _ | ck2
        · simp [hn, Mut_exec_liftE] at h
        · simp only [hn, Mut_exec_liftE] at h
          rcases hset : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨_ | u, r2⟩
          · rw [hset] at h; cases h
          · rw [hset] at h; simp only [Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩
            exact setReceiverChainKey_recvChainsOk their ck2 r1 r2 u hr1 hset

private theorem onRatchet_ok {PQ α : Type} (m : Mut RatchetState α) (t t' : TripleRatchet PQ) (a : α)
    (h : Mut.exec (TripleRatchet.onRatchet m) t = (.ok a, t')) :
    Mut.exec m t.ratchet = (.ok a, t'.ratchet) ∧ t'.pqrState = t.pqrState ∧
      t'.localIdentityKey = t.localIdentityKey ∧ t'.remoteIdentityKey = t.remoteIdentityKey := by
  unfold TripleRatchet.onRatchet zoom at h; simp only [Mut_exec_bind, Mut_exec_get] at h
  rcases hm : Mut.exec m t.ratchet with ⟨_ | a0, r1⟩
  · simp [hm, Mut_exec_set, Mut_exec_liftE] at h
  · simp only [hm, Mut_exec_set, Mut_exec_liftE, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem messageEncrypt_ok_struct {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC) (addrs : Option Bytes)
    (ptext : Bytes) (coins : PQC) (record s : SessionState PQ) (msg : SignalMessage)
    (h : SessionState.messageEncrypt C codec spqr addrs ptext coins record = (.ok msg, s)) :
    s.receiverChains = record.receiverChains ∧ s.localIdentity = record.localIdentity ∧
    s.remoteIdentity = record.remoteIdentity ∧ s.sessionVersion = record.sessionVersion ∧
    ∃ salt pm, spqr.send record.pqRatchetState coins = some (s.pqRatchetState, salt, pm) := by
  unfold SessionState.messageEncrypt at h
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState record with ⟨_ | o, taken⟩
  · rw [hfrom] at h; cases h
  · rw [hfrom] at h; dsimp only at h
    have htaken : taken.receiverChains = record.receiverChains ∧
        taken.localIdentity = record.localIdentity ∧ taken.remoteIdentity = record.remoteIdentity ∧
        taken.sessionVersion = record.sessionVersion ∧ o.pqrState = record.pqRatchetState := by
      revert hfrom; unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
      rcases hsc : record.senderChain with _ | sc
      · simp [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_throw]
      · simp only [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_modifyGet]
        split
        · simp [Mut_exec_throw]
        · rcases hrem : record.remoteIdentity with _ | rem
          · simp [Mut_exec_throw]
          · simp only [Mut_exec_pure, Prod.mk.injEq, Except.ok.injEq]
            rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    rcases henc : Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext
        (record.encryptAddresses addrs) coins) o with ⟨_ | msg', o'⟩
    · rw [henc] at h; cases h
    · rw [henc] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold OutgoingTripleRatchet.encrypt at henc; simp only [Mut_exec_bind, Mut_exec_get] at henc
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
              by simpa [OutgoingTripleRatchet.applyToSessionState, hpq] using hspqr⟩
      · simp [hpan, Mut_exec_throw] at henc

private theorem tryDecryptFromRecord_ok_struct {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record s : SessionState PQ) (pt : Bytes)
    (h : SessionState.tryDecryptFromRecord C spqr expected m msgType coins record = (.ok pt, s)) :
    (RecvChainsOk record.receiverChains → RecvChainsOk s.receiverChains) ∧
    s.localIdentity = record.localIdentity ∧ s.remoteIdentity = record.remoteIdentity ∧
    s.sessionVersion = record.sessionVersion ∧
    ∃ salt, spqr.recv record.pqRatchetState m.pqRatchet = .ok (s.pqRatchetState, salt) := by
  unfold SessionState.tryDecryptFromRecord at h; split_ifs at h
  · cases h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) record with
      ⟨_ | pt', upd⟩
    · rw [hd] at h; cases h
    · rw [hd] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_modifyGet] at hd
      rcases hrem : record.remoteIdentity with _ | rem
      · simp [hrem, Mut_exec_throw] at hd
      · simp only [hrem, Mut_exec_pure] at hd
        set tr0 : TripleRatchet PQ := ⟨⟨record.rootKey, record.senderChain, record.receiverChains,
          record.previousCounter, maxForwardJumps⟩, record.pqRatchetState, record.localIdentity, rem⟩
        rcases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins) tr0 with
          ⟨_ | pt0, tr'⟩
        · simp [hdec, Mut_exec_liftE] at hd
        · simp only [hdec, Mut_exec_liftE, Mut_exec_modify, Prod.mk.injEq] at hd
          rcases hd with ⟨-, rfl⟩; unfold TripleRatchet.decrypt at hdec; simp only [Mut_exec_bind] at hdec
          rcases hens : Mut.exec (TripleRatchet.onRatchet
              (RatchetState.ensureReceiverChain C m.senderRatchetKey coins)) tr0 with ⟨_ | ck, tr1⟩
          · rw [hens] at hdec; cases hdec
          · rw [hens] at hdec; dsimp only at hdec
            rcases onRatchet_ok _ tr0 tr1 ck hens with ⟨hens_r, hpq1, _, _⟩
            rcases hcons : Mut.exec (TripleRatchet.onRatchet
                (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType)) tr1 with
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
                      simpa [TripleRatchet.applyToSessionState,
                        SessionState.clearUnacknowledgedPreKeyMessage, hpq2, hpq1, tr0] using hspqr
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

/-! ## SPQR-V1 `ValidState` and additive growth bounds -/

private theorem length_le_lenField (tag : ℕ) (payload : Bytes) :
    payload.length ≤ (lenField tag payload).length := by
  unfold lenField; simp only [List.length_append]; omega

private theorem length_le_bytesField (tag : ℕ) (v : Bytes) :
    v.length ≤ (bytesField tag v).length := by
  unfold bytesField; split_ifs with h <;> [simp [h]; exact length_le_lenField tag v]

theorem pqLength_le_encodeRecordX (x : RecordExtras) (g : GhostState Bytes) :
    g.session.pqRatchetState.length ≤ (encodeRecordUnderExtras (fun _ => x) g).length := by
  have h1 := length_le_bytesField 15 g.session.pqRatchetState
  have h2 : (bytesField 15 g.session.pqRatchetState).length ≤ (encStateUnderExtras x g.session).length := by
    unfold encStateUnderExtras; simp only [List.length_append]; omega
  have h3 : (encStateUnderExtras x g.session).length ≤ (encodeRecordUnderExtras (fun _ => x) g).length :=
    length_le_lenField 1 (encStateUnderExtras x g.session)
  omega

theorem pqLength_lt_2_64_of_encodeRecordX {x : RecordExtras} {g : GhostState Bytes}
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31) :
    g.session.pqRatchetState.length < 2 ^ 64 := by
  have h := pqLength_le_encodeRecordX x g; omega

private theorem isEmpty_false_of_length_32 {bs : Bytes} (h : bs.length = 32) :
    bs.isEmpty = false := by cases bs with | nil => cases h | cons _ _ => rfl

private theorem spqr_encodeBytesField_of_length_32 {tag : BitVec 32} {bs : Bytes}
    (h : bs.length = 32) :
    LibsignalSpqrV1.Proto.encodeBytesField tag bs =
      LibsignalSpqrV1.Proto.encodeKey tag .lengthDelimited ++ [0x20#8] ++ bs := by
  simp only [LibsignalSpqrV1.Proto.encodeBytesField, isEmpty_false_of_length_32 h,
    Bool.false_eq_true, ↓reduceIte, LibsignalSpqrV1.Proto.encodeBytesUncond, h]; rfl

private theorem auth_new_lengths (F : ShaCompress) (ak : Bytes) :
    (LibsignalSpqrV1.Authenticator.new F ak 1#64).rootKey.length = 32 ∧
    (LibsignalSpqrV1.Authenticator.new F ak 1#64).macKey.length = 32 := by
  unfold LibsignalSpqrV1.Authenticator.new LibsignalSpqrV1.Authenticator.update; dsimp only
  have h64 : (LibsignalSpqrV1.hkdfToVecUnchecked F (List.replicate 32 0)
      (List.replicate 32 0 ++ ak)
      (LibsignalSpqrV1.Authenticator.updateLabel ++ HMAC.toBEBytes 8 1#64) 64).length = 64 := by
    simp [LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked]
  exact ⟨by simp only [List.length_take, h64]; omega, by simp only [List.length_drop, h64]⟩

theorem spqrV1Init_length_le (F : ShaCompress) (K : MlKem) (dir : SpqrDirection)
    (k : BitVec 256) : (spqrV1Init F K dir k).length ≤ 640 := by
  have hak : (HMAC.keyToBytes32 k).length = 32 := keyToBytes32_length k
  obtain ⟨hrk, hmk⟩ := auth_new_lengths F (HMAC.keyToBytes32 k)
  let auth0 := LibsignalSpqrV1.Authenticator.new F (HMAC.keyToBytes32 k) 1#64
  have hrk' : auth0.rootKey.length = 32 := hrk
  have hmk' : auth0.macKey.length = 32 := hmk
  have hAuthLen : (LibsignalSpqrV1.ProtoAuthenticator.encodeRaw
      { rootKey := auth0.rootKey, macKey := auth0.macKey }).length = 68 := by
    have hk1 : LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
    have hk2 : LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl
    simp [LibsignalSpqrV1.ProtoAuthenticator.encodeRaw, spqr_encodeBytesField_of_length_32 hrk',
      spqr_encodeBytesField_of_length_32 hmk', hk1, hk2, hrk', hmk']
  cases dir with
  | a2b =>
    have hInit : spqrV1Init F K .a2b k = (LibsignalSpqrV1.spqrDeps F K).encodeState {
        inner := some { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } } }) },
        versionNegotiation := some {
          authKey := HMAC.keyToBytes32 k, direction := 0#32, minVersion := 1#32,
          chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } },
        chain := none } := rfl
    have hVnLen : (LibsignalSpqrV1.VersionNegotiationPB.encodeRaw {
        authKey := HMAC.keyToBytes32 k, direction := 0#32, minVersion := 1#32,
        chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }).length = 38 := by
      have hk1 : LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
      have hdir : LibsignalSpqrV1.Proto.encodeInt32Field 2#32 0#32 = [] := rfl
      simp [LibsignalSpqrV1.VersionNegotiationPB.encodeRaw, spqr_encodeBytesField_of_length_32 hak,
        hk1, hdir, hak]; rfl
    have hUcLen : (LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.encodeRaw
        { epoch := 1#64, auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } }).length = 72 := by
      simp [LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.encodeRaw,
        LibsignalSpqrV1.Proto.encodeOptMessage, LibsignalSpqrV1.Proto.encodeMessage, hAuthLen]; rfl
    have hChkLen : (LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.encodeRaw
        { uc := some { epoch := 1#64, auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } } }).length = 74 := by
      simp [LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.encodeRaw,
        LibsignalSpqrV1.Proto.encodeOptMessage, LibsignalSpqrV1.Proto.encodeMessage, hUcLen]; rfl
    have hV1Len : (LibsignalSpqrV1.V1State.encodeRaw { innerState := some (.keysUnsampled
        { uc := some { epoch := 1#64, auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } } }) }).length = 76 := by
      simp [LibsignalSpqrV1.V1State.encodeRaw, LibsignalSpqrV1.V1State.InnerState.encode,
        LibsignalSpqrV1.Proto.encodeMessage, hChkLen]; rfl
    have hLen : (spqrV1Init F K .a2b k).length = 118 := by
      rw [hInit]; simp [LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.pbToPqRatchetState,
        LibsignalSpqrV1.Proto.encodeState, LibsignalSpqrV1.PqRatchetState.encode,
        LibsignalSpqrV1.PqRatchetState.encodeRaw, LibsignalSpqrV1.Proto.encodeOptMessage,
        LibsignalSpqrV1.PqRatchetState.Inner.encode, LibsignalSpqrV1.Proto.encodeMessage,
        hVnLen, hV1Len]; rfl
    omega
  | b2a =>
    let pd0 : LibsignalSpqrV1.PolynomialDecoder :=
      { ptsNeeded := 48#32, polys := 16#32, pts := List.replicate 16 [], isComplete := false }
    have hInit : spqrV1Init F K .b2a k = (LibsignalSpqrV1.spqrDeps F K).encodeState {
        inner := some { innerState := some (.noHeaderReceived {
          uc := some { epoch := 1#64, auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } },
          receivingHdr := some pd0 }) },
        versionNegotiation := some {
          authKey := HMAC.keyToBytes32 k, direction := 1#32, minVersion := 1#32,
          chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } },
        chain := none } := rfl
    have hVnLen : (LibsignalSpqrV1.VersionNegotiationPB.encodeRaw {
        authKey := HMAC.keyToBytes32 k, direction := 1#32, minVersion := 1#32,
        chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }).length = 40 := by
      have hk1 : LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
      have hdir : LibsignalSpqrV1.Proto.encodeInt32Field 2#32 1#32 = [0x10#8, 0x01#8] := rfl
      simp [LibsignalSpqrV1.VersionNegotiationPB.encodeRaw, spqr_encodeBytesField_of_length_32 hak,
        hk1, hdir, hak]; rfl
    have hUcLen : (LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
        { epoch := 1#64, auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } }).length = 72 := by
      simp [LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw,
        LibsignalSpqrV1.Proto.encodeOptMessage, LibsignalSpqrV1.Proto.encodeMessage, hAuthLen]; rfl
    have hPdLen : (LibsignalSpqrV1.PolynomialDecoder.encodeRaw pd0).length = 36 := rfl
    have hChkLen : (LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw {
        uc := some { epoch := 1#64, auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } },
        receivingHdr := some pd0 }).length = 112 := by
      simp [LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw,
        LibsignalSpqrV1.Proto.encodeOptMessage, LibsignalSpqrV1.Proto.encodeMessage,
        hUcLen, hPdLen]; rfl
    have hV1Len : (LibsignalSpqrV1.V1State.encodeRaw { innerState := some (.noHeaderReceived {
        uc := some { epoch := 1#64, auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } },
        receivingHdr := some pd0 }) }).length = 114 := by
      simp [LibsignalSpqrV1.V1State.encodeRaw, LibsignalSpqrV1.V1State.InnerState.encode,
        LibsignalSpqrV1.Proto.encodeMessage, hChkLen]; rfl
    have hLen : (spqrV1Init F K .b2a k).length = 158 := by
      rw [hInit]; simp [LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.pbToPqRatchetState,
        LibsignalSpqrV1.Proto.encodeState, LibsignalSpqrV1.PqRatchetState.encode,
        LibsignalSpqrV1.PqRatchetState.encodeRaw, LibsignalSpqrV1.Proto.encodeOptMessage,
        LibsignalSpqrV1.PqRatchetState.Inner.encode, LibsignalSpqrV1.Proto.encodeMessage,
        hVnLen, hV1Len]; rfl
    omega

private theorem initiateState_props
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {P : Party} {me : LocalIdentity} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {x : RecordExtras} {g : GhostState Bytes}
    (h : initiateState X W P me b t = some (x, g)) :
    ReachPqInvCli W me x g ∧ ValidState g.session.pqRatchetState ∧
      g.session.pqRatchetState.length ≤ 640 := by
  unfold initiateState at h
  rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
    _ | ⟨dk, hdr⟩
  · simp [hinit] at h
  · rw [hinit] at h; dsimp only at h; unfold initializeInitiatorSession at h
    dsimp only [bind, Except.bind, pure, Except.pure] at h
    rcases hrc : rootCreateChain W.C (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
        (KeyPair.generate W.C (HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
      _ | ⟨rk', ck'⟩
    · simp [hrc] at h
    · rw [hrc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
      refine ⟨mk_reachPqInvCli ?_ rfl rfl ⟨⟨⟨b.idPub⟩⟩, rfl⟩ rfl rfl rfl
        (publicKey_serialize_length _) ?_, validState_spqrV1Init W.C.F W.Q.K .a2b _,
        spqrV1Init_length_le W.C.F W.Q.K .a2b _⟩
      · exact recvChainsOk_addReceiverChain
          (SessionState.new currentVersion ⟨(keyPairOf W.C me.idPriv).publicKey⟩
            ⟨⟨b.idPub⟩⟩ _ _) ⟨b.spkPub⟩ ⟨_, 0⟩ recvChainsOk_nil
      · intro k hk; simp only [initiatorRecordExtras, Option.some.injEq] at hk; subst hk; simp [kyberKey]

private theorem recvPrekeyState_props
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {P : Party} {me : LocalIdentity} {k : ResponderPreKeySecrets} {m : PreKeyMessageFields}
    {rc : BitVec 256} {x : RecordExtras} {g : GhostState Bytes} {pt : Bytes}
    (h : recvPrekeyState X W P me k m rc = some (some (x, g, pt))) :
    ReachPqInvCli W me x g ∧ ValidState g.session.pqRatchetState ∧
      g.session.pqRatchetState.length ≤ 640 + 80000 := by
  unfold recvPrekeyState at h
  rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    by_cases hids : m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId
    · simp only [hids, ↓reduceIte] at h; cases h
    · simp only [hids, ↓reduceIte] at h
      rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
        _ | dk
      · simp [hacc] at h
      · rw [hacc] at h; dsimp only at h
        set st0 : SessionState Bytes :=
          initializeRecipientSession (pqxdhSpqrSession W) ⟨(keyPairOf W.C me.idPriv).publicKey⟩
            ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
            (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        rcases hd : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with ⟨err | pt', st⟩
        · rw [hd] at h; cases err <;> cases h
        · rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          obtain ⟨hrc_fn, hloc, hrem, hver, salt, hspqr⟩ :=
            tryDecryptFromRecord_ok_struct W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P)
              inner .preKey rc st0 st pt' hd
          have hval0 : ValidState st0.pqRatchetState := validState_spqrV1Init W.C.F W.Q.K .b2a _
          have hlen0 : st0.pqRatchetState.length ≤ 640 := spqrV1Init_length_le W.C.F W.Q.K .b2a _
          obtain ⟨hval', hle'⟩ := spqrV1_recv_validState_length_le_tight W.C.F W.Q.K st0.pqRatchetState
            inner.pqRatchet st.pqRatchetState salt hval0 (by omega) hspqr
          refine ⟨mk_reachPqInvCli (hrc_fn recvChainsOk_nil) hver hloc ⟨⟨⟨m.idPub⟩⟩, hrem⟩
            rfl rfl rfl (by simp [responderRecordExtras, djbKey]) (fun _ hky => nomatch hky), hval', ?_⟩
          dsimp only; omega

private theorem reachPq_props {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (hR : ReachablePqxdhSession W me x g) : ReachPqInvCli W me x g ∧ ValidState g.session.pqRatchetState := by
  induction hR with
  | initiate _ _ _ _ _ _ _ hi => exact ⟨(initiateState_props hi).1, (initiateState_props hi).2.1⟩
  | recvPrekey _ _ _ _ _ _ _ _ _ hr =>
    exact ⟨(recvPrekeyState_props hr).1, (recvPrekeyState_props hr).2.1⟩
  | @send _ _ g_s m r _ hlen ih =>
    unfold Params.send
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with ⟨_ | msg, s⟩
    · exact ih
    · dsimp only
      obtain ⟨hrc_eq, hloc_eq, hrem_eq, hver_eq, salt, pm, hspqr⟩ :=
        messageEncrypt_ok_struct (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hm
      rcases ih.1.remoteIdentity_some with ⟨rem, hrem⟩
      exact ⟨mk_reachPqInvCli (hrc_eq.symm ▸ recvChainsOk_of_invCli ih.1)
        (hver_eq.trans ih.1.sessionVersion_eq) (hloc_eq.trans ih.1.localIdentity_eq)
        ⟨rem, hrem_eq.trans hrem⟩ ih.1.localRegistrationId_eq ih.1.pending_timestamp_eq
        ih.1.pending_baseKey_serialize ih.1.aliceBaseKey_len ih.1.kyber_ciphertext_len,
        (spqrV1_send_validState_length_le W.C.F W.Q.K g_s.session.pqRatchetState r
          s.pqRatchetState salt pm ih.2 (pqLength_lt_2_64_of_encodeRecordX hlen) hspqr).1⟩
  | @recv _ _ g_r _ c rc _ _ hlen hrec ih =>
    unfold Params.receive at hrec
    rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session with ⟨_ | pt, s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec; simp only [Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, -⟩
        obtain ⟨hrc_fn, hloc_eq, hrem_eq, hver_eq, salt, hspqr⟩ :=
          tryDecryptFromRecord_ok_struct (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
            ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session s pt hd
        rcases ih.1.remoteIdentity_some with ⟨rem, hrem⟩
        exact ⟨mk_reachPqInvCli (hrc_fn (recvChainsOk_of_invCli ih.1))
          (hver_eq.trans ih.1.sessionVersion_eq) (hloc_eq.trans ih.1.localIdentity_eq)
          ⟨rem, hrem_eq.trans hrem⟩ ih.1.localRegistrationId_eq ih.1.pending_timestamp_eq
          ih.1.pending_baseKey_serialize ih.1.aliceBaseKey_len ih.1.kyber_ciphertext_len,
          (spqrV1_recv_validState_length_le W.C.F W.Q.K g_r.session.pqRatchetState
            msg.pqRatchet s.pqRatchetState salt ih.2
            (pqLength_lt_2_64_of_encodeRecordX hlen) hspqr).1⟩

/-- Every reachable PQXDH session satisfies `ReachPqInvCli`. -/
theorem reachPq_invCli {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (hR : ReachablePqxdhSession W me x g) : ReachPqInvCli W me x g := (reachPq_props hR).1

/-- Every reachable PQXDH session has a valid SPQR-V1 state. -/
theorem reachPq_validState_cli {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (hR : ReachablePqxdhSession W me x g) : ValidState g.session.pqRatchetState := (reachPq_props hR).2

theorem initiateState_pqLength_le {X : UnreachedPqxdhPrimitives} {W : PEParams} {P : Party} {me : LocalIdentity}
    {b : PreKeyBundleFields} {t : List.Vector (BitVec 8) initiateTapeLen} {x : RecordExtras}
    {g : GhostState Bytes} (h : initiateState X W P me b t = some (x, g)) :
    g.session.pqRatchetState.length ≤ 640 := (initiateState_props h).2.2

theorem recvPrekeyState_pqLength_le {X : UnreachedPqxdhPrimitives} {W : PEParams} {P : Party} {me : LocalIdentity}
    {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} {rc : BitVec 256} {x : RecordExtras} {g : GhostState Bytes}
    {pt : Bytes} (h : recvPrekeyState X W P me k m rc = some (some (x, g, pt))) :
    g.session.pqRatchetState.length ≤ 640 + 80000 := (recvPrekeyState_props h).2.2

private theorem removeOpk_me (st : PqParty) (m : PreKeyMessageFields) : (removeOpk st m).me = st.me := by
  unfold removeOpk; cases m.opkId <;> rfl
private theorem markKyberUsed_me {st st1 : PqParty} {m : PreKeyMessageFields}
    (h : markKyberUsed st m = some st1) : st1.me = st.me := by
  unfold markKyberUsed at h
  split at h
  · injection h with h'; subst h'; rfl
  · split at h <;> [cases h; (split at h <;> [cases h; (injection h with h'; subst h'; rfl)])]
private theorem encodeRecordX_eq_of_session_eq (x : RecordExtras) (g₁ g₂ : GhostState Bytes)
    (hs : g₁.session = g₂.session) :
    encodeRecordUnderExtras (fun _ => x) g₁ = encodeRecordUnderExtras (fun _ => x) g₂ := by unfold encodeRecordUnderExtras; rw [hs]

private theorem pqStep_session_step
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {st st' : PqParty}
    {x' : RecordExtras} {g' : GhostState Bytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hstep : PqStep X W st st') (hs' : st'.session = some (x', g')) :
    (∃ g₀' : GhostState Bytes,
      ReachablePqxdhSession W st'.me x' g₀' ∧ g₀'.party = g'.party ∧ g₀'.session = g'.session) ∧
    (st.session = none → g'.session.pqRatchetState.length ≤ 640 + 80000) ∧
    (∀ x g, st.session = some (x, g) →
      g'.session.pqRatchetState.length ≤ g.session.pqRatchetState.length + 80000) := by
  cases hstep with
  | init b t _ out hnone hinit =>
    unfold pqInitModel at hinit
    cases ht : st.trusts ⟨⟨b.idPub⟩⟩
    · rw [ht] at hinit; cases hinit
    · rw [ht] at hinit; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinit
      rcases hi : initiateState X W st.party st.me b t with _ | ⟨x, g⟩
      · rw [hi] at hinit; cases hinit
      · rw [hi] at hinit; simp only [Option.some.injEq, Prod.mk.injEq] at hinit
        rcases hinit with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
        rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
        have h640 := initiateState_pqLength_le hi
        refine ⟨⟨g, ReachablePqxdhSession.initiate X st.party st.me b t x g hi, rfl, rfl⟩, ?_, ?_⟩
        · intro _; omega
        · intro _ _ hs; rw [hnone] at hs; cases hs
  | send m r _ out _ hsend =>
    unfold pqSendModel at hsend
    rcases hsess : st.session with _ | ⟨x, g⟩
    · rw [hsess] at hsend; cases hsend
    · rw [hsess] at hsend; dsimp only at hsend
      rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).sendAddrs g.party) m r.toList g.session with ⟨err | msg, s⟩
      · rw [henc] at hsend; cases err <;> cases hsend
      · rw [henc] at hsend; dsimp only at hsend
        rcases hk : g.session.remoteIdentity with _ | k
        · rw [hk] at hsend; cases hsend
        · rw [hk] at hsend; dsimp only at hsend
          cases ht : st.trusts k
          · rw [ht] at hsend; cases hsend
          · rw [ht] at hsend
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Option.some.injEq, Prod.mk.injEq] at hsend
            rcases hsend with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
            rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
            obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, -, hlen⟩ := hwf.1 x g hsess
            have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
              rw [encodeRecordX_eq_of_session_eq x g₀ g hs₀]; exact hlen
            have hval : ValidState g.session.pqRatchetState := by
              rw [← hs₀]; exact reachPq_validState_cli hR₀
            have hpq := pqLength_lt_2_64_of_encodeRecordX hlen
            obtain ⟨-, -, -, -, salt, pm, hspqr⟩ := messageEncrypt_ok_struct W.C protoSignalCodec
              (pqxdhSpqrSession W) ((pqxdhSessionParams W).sendAddrs g.party) m r.toList g.session s msg henc
            have hle := (spqrV1_send_validState_length_le_tight W.C.F W.Q.K g.session.pqRatchetState
              r.toList s.pqRatchetState salt pm hval hpq hspqr).2
            refine ⟨⟨((pqxdhSessionParams W).send g₀ m r.toList).1, ReachablePqxdhSession.send m r.toList hR₀ hlen₀, ?_⟩,
              ?_, ?_⟩
            · unfold Params.send
              have hC : (pqxdhSessionParams W).C = W.C := rfl
              have hcodec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
              have hspqr' : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
              rw [hC, hcodec, hspqr', hp₀, hs₀, henc]; exact ⟨rfl, rfl⟩
            · intro hnone; cases hnone
            · intro x1 g1 hs1; simp only [Option.some.injEq, Prod.mk.injEq] at hs1
              rcases hs1 with ⟨_, hg1⟩; rw [← hg1]; dsimp only; omega
  | recvWhisper c rc _ out _ hrecv =>
    unfold pqRecvWhisperModel at hrecv
    rcases hsess : st.session with _ | ⟨x, g⟩
    · rw [hsess] at hrecv; cases hrecv
    · rw [hsess] at hrecv; dsimp only at hrecv
      rcases htry : SignalMessage.tryFrom protoSignalCodec c with _ | msg
      · rw [htry] at hrecv; cases hrecv
      · rw [htry] at hrecv; dsimp only [pqxdhSessionDecryptModel] at hrecv
        rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨err | pt, s⟩
        · rw [hdec] at hrecv; cases err <;> cases hrecv
        · rw [hdec] at hrecv; dsimp only at hrecv
          rcases hk : s.remoteIdentity with _ | k
          · rw [hk] at hrecv; cases hrecv
          · rw [hk] at hrecv; dsimp only at hrecv
            cases ht : st.trusts k
            · rw [ht] at hrecv; cases hrecv
            · rw [ht] at hrecv
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                Option.some.injEq, Prod.mk.injEq] at hrecv
              rcases hrecv with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
              rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
              obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, -, hlen⟩ := hwf.1 x g hsess
              have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
                rw [encodeRecordX_eq_of_session_eq x g₀ g hs₀]; exact hlen
              have hval : ValidState g.session.pqRatchetState := by
                rw [← hs₀]; exact reachPq_validState_cli hR₀
              have hpq := pqLength_lt_2_64_of_encodeRecordX hlen
              obtain ⟨-, -, -, -, salt, hspqr⟩ := tryDecryptFromRecord_ok_struct W.C (pqxdhSpqrSession W)
                ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session s pt hdec
              have hle := (spqrV1_recv_validState_length_le_tight W.C.F W.Q.K g.session.pqRatchetState
                msg.pqRatchet s.pqRatchetState salt hval hpq hspqr).2
              have hrec₀ : ∃ g₁ res, (pqxdhSessionParams W).receive g₀ c rc = some (g₁, res) ∧
                  g₁.party = g.party ∧ g₁.session = s := by
                unfold Params.receive
                have hC : (pqxdhSessionParams W).C = W.C := rfl
                have hcodec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
                have hspqr' : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
                rw [hcodec, htry, hC, hspqr', hp₀, hs₀]; dsimp only; rw [hdec]
                exact ⟨_, _, rfl, rfl, rfl⟩
              rcases hrec₀ with ⟨g₁, res, hrec₁, hp₁, hs₁⟩
              refine ⟨⟨g₁, ReachablePqxdhSession.recv hR₀ hlen₀ hrec₁, hp₁, hs₁⟩, ?_, ?_⟩
              · intro hnone; cases hnone
              · intro x1 g1 hs1; simp only [Option.some.injEq, Prod.mk.injEq] at hs1
                rcases hs1 with ⟨_, hg1⟩; rw [← hg1]; exact hle
  | recvPrekey m rc _ out _ _ hrecv =>
    unfold pqRecvPrekeyModel at hrecv
    rcases htry : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · rw [htry] at hrecv; cases hrecv
    · rw [htry] at hrecv; dsimp only at hrecv
      cases ht : st.trusts ⟨⟨m.idPub⟩⟩
      · rw [ht] at hrecv; cases hrecv
      · rw [ht] at hrecv; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrecv
        rcases hsess : st.session with _ | ⟨x, g⟩
        · rw [hsess] at hrecv; dsimp only at hrecv
          rcases hk : preKeysNamedBy st m with _ | k
          · rw [hk] at hrecv; cases hrecv
          · rw [hk] at hrecv; dsimp only at hrecv
            rcases hrp : recvPrekeyState X W st.party st.me k m rc with _ | _ | ⟨x1, g1, pt⟩
            · rw [hrp] at hrecv; cases hrecv
            · rw [hrp] at hrecv; cases hrecv
            · rw [hrp] at hrecv; dsimp only at hrecv
              rcases hmk : markKyberUsed st m with _ | st1
              · rw [hmk] at hrecv; cases hrecv
              · rw [hmk] at hrecv; simp only [Option.some.injEq, Prod.mk.injEq] at hrecv
                rcases hrecv with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
                rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
                have hme : (removeOpk st1 m).me = st.me :=
                  (removeOpk_me st1 m).trans (markKyberUsed_me hmk)
                refine ⟨?_, ?_, ?_⟩
                · dsimp only; rw [hme]
                  exact ⟨g1, ReachablePqxdhSession.recvPrekey X st.party st.me k m rc x1 g1 pt hrp, rfl, rfl⟩
                · intro _; exact recvPrekeyState_pqLength_le hrp
                · intro _ _ hs1; cases hs1
        · rw [hsess] at hrecv; dsimp only at hrecv
          by_cases hm_match : PqSessionMatches x g m
          · simp only [hm_match, ↓reduceIte] at hrecv
            split_ifs at hrecv
            · cases hrecv
            · rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                  ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session with
                ⟨err | pt, s⟩
              · rw [hdec] at hrecv; cases err <;> cases hrecv
              · rw [hdec] at hrecv; simp only [Option.some.injEq, Prod.mk.injEq] at hrecv
                rcases hrecv with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
                rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
                obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, -, hlen⟩ := hwf.1 x g hsess
                have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
                  rw [encodeRecordX_eq_of_session_eq x g₀ g hs₀]; exact hlen
                have hval : ValidState g.session.pqRatchetState := by
                  rw [← hs₀]; exact reachPq_validState_cli hR₀
                have hpq := pqLength_lt_2_64_of_encodeRecordX hlen
                obtain ⟨-, -, -, -, salt, hspqr⟩ := tryDecryptFromRecord_ok_struct W.C (pqxdhSpqrSession W)
                  ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session s pt hdec
                have hle := (spqrV1_recv_validState_length_le_tight W.C.F W.Q.K g.session.pqRatchetState
                  inner.pqRatchet s.pqRatchetState salt hval hpq hspqr).2
                have hdec₀ : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                    ((pqxdhSessionParams W).expectedAddrs g₀.party) inner .preKey rc g₀.session =
                    (.ok pt, s) := by rw [hp₀, hs₀]; exact hdec
                obtain ⟨g₁, hR₁, hp₁, hs₁⟩ :=
                  reachPq_promote W st.me x g₀ m.inner inner rc pt s hR₀ hlen₀ htry hdec₀
                refine ⟨⟨g₁, hR₁, hp₁.trans hp₀, hs₁⟩, ?_, ?_⟩
                · intro hnone; cases hnone
                · intro x1 g1 hs1; simp only [Option.some.injEq, Prod.mk.injEq] at hs1
                  rcases hs1 with ⟨_, hg1⟩; rw [← hg1]; exact hle
          · simp only [hm_match, ↓reduceIte] at hrecv; cases hrecv

/-- One-step SPQR state length bound across any accepted `PqStep` from `PqxdhPartyInSpecDomain W st`. -/
theorem pqStep_pqLength_le
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {st st' : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) (hstep : PqStep X W st st') :
    (st.session = none →
      ∀ x' g', st'.session = some (x', g') →
        g'.session.pqRatchetState.length ≤ 640 + 80000) ∧
    (∀ x g, st.session = some (x, g) →
      ∀ x' g', st'.session = some (x', g') →
        g'.session.pqRatchetState.length ≤ g.session.pqRatchetState.length + 80000) :=
  ⟨fun hnone _ _ hs' => (pqStep_session_step hwf hstep hs').2.1 hnone,
   fun x g hs _ _ hs' => (pqStep_session_step hwf hstep hs').2.2 x g hs⟩

/-! ## Non-PQ record overhead and multi-step spec-domain closure -/

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
  have h2 := bytesField_length_le 2 (HMAC.keyToBytes32 ck.key); rw [keyToBytes32_length] at h2; omega

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

/-- For any reachable PQXDH session, `encodeRecordUnderExtras` exceeds `pqRatchetState.length` by
at most `923,135` bytes. -/
theorem encodeRecordX_length_le_pq_add_923135_cli
    {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (hR : ReachablePqxdhSession W me x g) :
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ g.session.pqRatchetState.length + 923135 := by
  have inv := reachPq_invCli hR; dsimp only [encodeRecordUnderExtras, msgField]
  have houter := lenField_length_le 1 (encStateUnderExtras x g.session)
  have henc : (encStateUnderExtras x g.session).length ≤ g.session.pqRatchetState.length + 923115 := by
    unfold encStateUnderExtras; simp only [List.length_append]
    have hf1 := uint32Field_length_le 1 g.session.sessionVersion
    have hf2 := bytesField_length_le 2 g.session.localIdentity.serialize; rw [inv.localIdentity_len] at hf2
    have hf3 : (bytesField 3 ((g.session.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤
        53 := by
      rcases inv.remoteIdentity_some with ⟨rem, hrem⟩; rw [hrem]; dsimp only [Option.map, Option.getD]
      have h := bytesField_length_le 3 rem.serialize; rw [inv.remoteIdentity_len rem hrem] at h; omega
    have hf4 := bytesField_length_le 4 (HMAC.keyToBytes32 g.session.rootKey); rw [inv.rootKey_len] at hf4
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

theorem encodeRecordX_length_lt_of_pq_add_2100000_lt_cli
    {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (hR : ReachablePqxdhSession W me x g) (hpq : g.session.pqRatchetState.length + 2100000 < 2 ^ 31) :
    (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := by
  have hle := encodeRecordX_length_le_pq_add_923135_cli hR; omega

/-- One-step `PqxdhPartyInSpecDomain` and `< 2 ^ 31` record-size closure from an additive
`pqRatchetState` budget. -/
theorem wfPq_step_of_pqBudget
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {st st' : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) (hstep : PqStep X W st st') (hlr : lastResortUses st' < 2 ^ 25)
    (hbud : ∀ x g, st.session = some (x, g) →
      g.session.pqRatchetState.length + 80000 + 2100000 < 2 ^ 31) :
    PqxdhPartyInSpecDomain W st' ∧
      ∀ x' g', st'.session = some (x', g') → (encodeRecordUnderExtras (fun _ => x') g').length < 2 ^ 31 := by
  have hrec : ∀ x' g', st'.session = some (x', g') →
      (encodeRecordUnderExtras (fun _ => x') g').length < 2 ^ 31 := by
    intro x' g' hs'
    obtain ⟨⟨g₀', hR₀', -, hsess₀'⟩, hnone_bd, hsome_bd⟩ := pqStep_session_step hwf hstep hs'
    have hpq' : g'.session.pqRatchetState.length + 2100000 < 2 ^ 31 := by
      rcases hs : st.session with _ | ⟨x, g⟩
      · have hle := hnone_bd hs; omega
      · have hle := hsome_bd x g hs; have hb := hbud x g hs; omega
    have hpq₀' : g₀'.session.pqRatchetState.length + 2100000 < 2 ^ 31 := by
      rw [hsess₀']; exact hpq'
    rw [← encodeRecordX_eq_of_session_eq x' g₀' g' hsess₀']
    exact encodeRecordX_length_lt_of_pq_add_2100000_lt_cli hR₀' hpq₀'
  have hrec_cap : ∀ x' g', st'.session = some (x', g') →
      (encodeRecordUnderExtras (fun _ => x') g').length ≤ fileCapBytes := by
    intro x' g' hs'
    obtain ⟨⟨g₀', hR₀', -, hsess₀'⟩, -, -⟩ := pqStep_session_step hwf hstep hs'
    rw [← encodeRecordX_eq_of_session_eq x' g₀' g' hsess₀']
    exact LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.reachPq_encodeRecordX_length_le_fileCapBytes hR₀'
  exact ⟨wfPq_step X W st st' hwf hstep hlr hrec_cap, hrec⟩

/-- `n`-step reflexive-transitive closure of accepted `PqStep` transitions. -/
inductive PqSteps (X : UnreachedPqxdhPrimitives) (W : PEParams) : ℕ → PqParty → PqParty → Prop
  | refl (st : PqParty) : PqSteps X W 0 st st
  | step {n : ℕ} {st₀ st₁ st₂ : PqParty} :
      PqSteps X W n st₀ st₁ → PqStep X W st₁ st₂ → PqSteps X W (n + 1) st₀ st₂

theorem PqSteps.single {X : UnreachedPqxdhPrimitives} {W : PEParams} {st₀ st₁ : PqParty}
    (h : PqStep X W st₀ st₁) : PqSteps X W 1 st₀ st₁ := PqSteps.step (PqSteps.refl st₀) h

/-- Multi-step `PqxdhPartyInSpecDomain` and `< 2 ^ 31` record-size closure across `n` accepted CLI
calls under an additive `pqRatchetState` query budget. -/
theorem wfPq_of_pqSteps_budget
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {n : ℕ} {st₀ stₙ : PqParty}
    (hwf₀ : PqxdhPartyInSpecDomain W st₀) (hnone₀ : st₀.session = none) (hlr₀ : lastResortUses st₀ = 0)
    (hsteps : PqSteps X W n st₀ stₙ) (hbud : 80000 * (n + 1) + 2100000 < 2 ^ 31)
    (hn : n < 2 ^ 25) :
    PqxdhPartyInSpecDomain W stₙ ∧ lastResortUses stₙ ≤ n ∧
      (∀ x g, stₙ.session = some (x, g) →
        g.session.pqRatchetState.length ≤ 640 + 80000 * n) ∧
      (∀ x g, stₙ.session = some (x, g) →
        (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31) := by
  induction hsteps with
  | refl =>
    refine ⟨hwf₀, by omega, ?_, ?_⟩ <;> (intro _ _ hs; rw [hnone₀] at hs; cases hs)
  | @step m _ st₁ st₂ _ hlast ih =>
    obtain ⟨hwf₁, hlr₁, hpq₁, -⟩ := ih hwf₀ hnone₀ hlr₀ (by omega) (by omega)
    have hlr_step := pqStep_lastResortUses_le X W st₁ st₂ hwf₁.2.2.2.2.2 hlast
    have hbud₁ : ∀ x g, st₁.session = some (x, g) →
        g.session.pqRatchetState.length + 80000 + 2100000 < 2 ^ 31 := fun x g hs₁ => by
      have hle := hpq₁ x g hs₁; omega
    obtain ⟨hwf₂, hrec₂⟩ := wfPq_step_of_pqBudget hwf₁ hlast (by omega) hbud₁
    obtain ⟨hnone_bd, hsome_bd⟩ := pqStep_pqLength_le hwf₁ hlast
    refine ⟨hwf₂, by omega, ?_, hrec₂⟩
    intro x' g' hs₂
    rcases hs₁ : st₁.session with _ | ⟨x, g⟩
    · have hle := hnone_bd hs₁ x' g' hs₂
      have h1 := Nat.le_mul_of_pos_right 80000 (Nat.succ_pos m)
      exact Nat.le_trans hle (Nat.add_le_add_left h1 640)
    · calc g'.session.pqRatchetState.length
          ≤ g.session.pqRatchetState.length + 80000 := hsome_bd x g hs₁ x' g' hs₂
        _ ≤ (640 + 80000 * m) + 80000 := Nat.add_le_add_right (hpq₁ x g hs₁) 80000
        _ = 640 + 80000 * (m + 1) := by rw [Nat.mul_succ, Nat.add_assoc]

end CryptoVerification.LibsignalCli.Entry
