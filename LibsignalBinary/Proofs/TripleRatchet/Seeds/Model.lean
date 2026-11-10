/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionProofDefs

/-!
# Preservation of 32-Byte Skipped-Key Seeds (`SeedsLen32`)

Establishes and preserves the pure session-model invariant `SeedsLen32` required by `tryDecryptSpec`:
* Initial session states satisfy `SeedsLen32`.
* Every state transition (across both `Ok` and `Err` outcomes, accounting for in-place `Mut`
  mutations before error return and record-level rollback) preserves `SeedsLen32`.
* Any stored or freshly derived message key passed to `generate_keys` has a 32-byte HMAC-SHA256 seed.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Seeds

open CryptoGames CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchet

private def RatchetSeedsLen32 (r : RatchetState) : Prop :=
  ∀ c ∈ r.receiverChains, ∀ k ∈ c.messageKeys, k.seed.length = 32

private theorem flatMap_toBEBytes4_length :
    ∀ l : List (BitVec 32), (l.flatMap (HMAC.toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | hd :: tl => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      flatMap_toBEBytes4_length tl]
    have h4 : (HMAC.toBEBytes 4 hd).length = 4 := rfl
    omega

private theorem messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  unfold ChainKey.messageKeys Ratchet.chainHmac HMAC.hmacWith
  dsimp only
  unfold HMAC.sha256With
  rw [flatMap_toBEBytes4_length, List.Vector.toList_length]

private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl

private theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl

private theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

private theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  simp only [Bind.bind, ExceptT.bind, ExceptT.mk]
  unfold ExceptT.run StateT.run StateT.bind ExceptT.bindCont
  rcases m s with ⟨res, s'⟩
  cases res <;> rfl

private theorem exec_throw_bind {σ α β : Type} (e : SignalProtocolError)
    (f : α → Mut σ β) (s : σ) :
    Mut.exec (throw e >>= f) s = (.error e, s) := by
  rw [exec_bind, exec_throw]

private theorem exec_preserves_bind {σ α β : Type} {P : σ → Prop}
    (m : Mut σ α) (f : α → Mut σ β) (s : σ)
    (hm : P (Mut.exec m s).2)
    (hf : ∀ a s', Mut.exec m s = (.ok a, s') → P s' → P (Mut.exec (f a) s').2) :
    P (Mut.exec (m >>= f) s).2 := by
  rw [exec_bind]
  rcases h : Mut.exec m s with ⟨res, s'⟩
  rw [h] at hm
  cases res with
  | ok a => exact hf a s' h hm
  | error _ => exact hm

private theorem exec_onRatchet_snd {PQ α : Type} (m : Mut RatchetState α) (t : TripleRatchet PQ) :
    (Mut.exec (TripleRatchet.onRatchet m) t).2 =
      { t with ratchet := (Mut.exec m t.ratchet).2 } := by
  unfold TripleRatchet.onRatchet zoom
  rw [exec_bind, exec_get]
  dsimp only
  rw [exec_bind, exec_set]
  dsimp only
  rw [exec_liftE]

private theorem dhRatchetStep_preserves (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (hr : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.dhRatchetStep C their coins) r).2 := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey
  rw [exec_bind, exec_get]
  dsimp only
  cases r.senderChain with
  | none => rw [exec_throw]; exact hr
  | some sc =>
    dsimp only
    rw [exec_bind, exec_modifyGet]
    dsimp only
    rw [exec_bind, exec_liftE]
    cases rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
    | error _ => exact hr
    | ok p1 =>
      dsimp only
      rw [exec_bind, exec_liftE]
      cases rootCreateChain C p1.1 their (KeyPair.generate C coins).privateKey with
      | error _ => exact hr
      | ok p2 =>
        dsimp only
        rw [exec_bind, exec_modify]
        dsimp only
        rw [exec_pure]
        intro c hc k hk
        unfold RatchetState.evictReceiverChains at hc
        have hc' := List.mem_of_mem_drop hc
        rcases List.mem_append.mp hc' with hc_old | hc_new
        · exact hr c hc_old k hk
        · simp only [List.mem_singleton] at hc_new
          subst hc_new
          cases hk

private theorem ensureReceiverChain_preserves (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (hr : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.ensureReceiverChain C their coins) r).2 := by
  unfold RatchetState.ensureReceiverChain
  rw [exec_bind, exec_get]
  dsimp only
  rw [exec_bind, exec_liftE]
  cases r.findReceiverChainKey their with
  | error _ => exact hr
  | ok opt =>
    dsimp only
    cases opt with
    | some _ => rw [exec_pure]; exact hr
    | none => exact dhRatchetStep_preserves C their coins r hr

private theorem takeSkippedKey_preserves (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) (hr : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.takeSkippedKey their counter) r).2 := by
  unfold RatchetState.takeSkippedKey
  rw [exec_bind, exec_get]
  dsimp only
  cases r.findReceiverChainIndex their with
  | none => rw [exec_pure]; exact hr
  | some chainIdx =>
    dsimp only
    cases hrc : r.receiverChains[chainIdx]? with
    | none => rw [exec_throw]; exact hr
    | some c =>
      dsimp only
      cases c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
      | none => rw [exec_pure]; exact hr
      | some pos =>
        dsimp only
        cases c.messageKeys[pos]? with
        | none => rw [exec_throw]; exact hr
        | some _ =>
          dsimp only
          rw [exec_bind, exec_set]
          dsimp only
          rw [exec_pure]
          intro c' hc' k hk
          rcases List.mem_or_eq_of_mem_set hc' with hc_old | rfl
          · exact hr c' hc_old k hk
          · exact hr c (List.mem_of_getElem? hrc) k (List.mem_of_mem_eraseIdx hk)

private theorem storeSkippedKey_preserves (their : PublicKey) (key : MessageKeyGenerator)
    (hkey : key.seed.length = 32) (r : RatchetState) (hr : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.storeSkippedKey their key) r).2 := by
  unfold RatchetState.storeSkippedKey
  rw [exec_bind, exec_get]
  dsimp only
  cases r.findReceiverChainIndex their with
  | none => rw [exec_throw]; exact hr
  | some chainIdx =>
    dsimp only
    cases hrc : r.receiverChains[chainIdx]? with
    | none => rw [exec_throw]; exact hr
    | some c =>
      dsimp only
      rw [exec_set]
      intro c' hc' k hk
      rcases List.mem_or_eq_of_mem_set hc' with hc_old | rfl
      · exact hr c' hc_old k hk
      · dsimp only at hk
        have hk' : k ∈ key :: c.messageKeys := by
          split at hk
          · exact (List.dropLast_sublist _).subset hk
          · exact hk
        rcases List.mem_cons.mp hk' with rfl | hk_old
        · exact hkey
        · exact hr c (List.mem_of_getElem? hrc) k hk_old

private theorem setReceiverChainKey_preserves (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) (hr : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2 := by
  unfold RatchetState.setReceiverChainKey
  rw [exec_bind, exec_get]
  dsimp only
  cases r.findReceiverChainIndex their with
  | none => rw [exec_throw]; exact hr
  | some chainIdx =>
    dsimp only
    cases hrc : r.receiverChains[chainIdx]? with
    | none => rw [exec_throw]; exact hr
    | some c =>
      dsimp only
      rw [exec_set]
      intro c' hc' k hk
      rcases List.mem_or_eq_of_mem_set hc' with hc_old | rfl
      · exact hr c' hc_old k hk
      · exact hr c (List.mem_of_getElem? hrc) k hk

private theorem advanceChain_preserves (F : ShaCompress) (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck : ChainKey) (r : RatchetState), RatchetSeedsLen32 r →
      RatchetSeedsLen32 (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2
  | 0, ck, r, hr => by
    unfold RatchetState.advanceChain
    rw [exec_pure]
    exact hr
  | fuel + 1, ck, r, hr => by
    unfold RatchetState.advanceChain
    split
    · refine exec_preserves_bind _ _ r
        (storeSkippedKey_preserves their (ck.messageKeys F) (messageKeys_seed_length F ck) r hr) ?_
      intro _ r1 _ hr1
      refine exec_preserves_bind _ _ r1 (by rw [exec_liftE]; exact hr1) ?_
      intro ck' r2 hlift hr2
      rw [exec_liftE] at hlift
      rcases Prod.mk.inj hlift with ⟨_, rfl⟩
      exact advanceChain_preserves F their counter fuel ck' r1 hr2
    · rw [exec_pure]
      exact hr

private theorem consumeMessageKey_preserves (F : ShaCompress) (their : PublicKey)
    (chainKey : ChainKey) (counter : BitVec 32) (msgType : MessageType)
    (r : RatchetState) (hr : RatchetSeedsLen32 r) :
    RatchetSeedsLen32
      (Mut.exec (RatchetState.consumeMessageKey F their chainKey counter msgType) r).2 := by
  unfold RatchetState.consumeMessageKey
  dsimp only
  split
  · refine exec_preserves_bind _ _ r (takeSkippedKey_preserves their counter r hr) ?_
    intro opt r1 _ hr1
    cases opt with
    | some k => dsimp only; rw [exec_pure]; exact hr1
    | none => dsimp only; rw [exec_throw_bind]; exact hr1
  · refine exec_preserves_bind (get : Mut RatchetState RatchetState) _ r
      (by rw [exec_get]; exact hr) ?_
    intro s r1 hget hr1
    rw [exec_get] at hget
    cases hget
    split
    · rw [exec_throw_bind]; exact hr1
    · refine exec_preserves_bind _ _ r
        (advanceChain_preserves F their counter (counter - chainKey.index).toNat chainKey r hr1) ?_
      intro ck' r2 _ hr2
      refine exec_preserves_bind _ _ r2 (by rw [exec_liftE]; exact hr2) ?_
      intro nextCk r3 hlift hr3
      rw [exec_liftE] at hlift
      rcases Prod.mk.inj hlift with ⟨_, rfl⟩
      refine exec_preserves_bind _ _ r2 (setReceiverChainKey_preserves their nextCk r2 hr3) ?_
      intro _ r4 _ hr4
      rw [exec_pure]
      exact hr4

private theorem tripleRatchetDecrypt_preserves {PQ PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (m : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (t : TripleRatchet PQ) (ht : RatchetSeedsLen32 t.ratchet) :
    RatchetSeedsLen32 (Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins) t).2.ratchet := by
  unfold TripleRatchet.decrypt
  dsimp only
  refine exec_preserves_bind (P := fun x => RatchetSeedsLen32 x.ratchet) _ _ t
    (by rw [exec_onRatchet_snd]; exact ensureReceiverChain_preserves C m.senderRatchetKey coins t.ratchet ht) ?_
  intro ck t1 _ ht1
  refine exec_preserves_bind (P := fun x => RatchetSeedsLen32 x.ratchet) _ _ t1
    (by rw [exec_onRatchet_snd]
        exact consumeMessageKey_preserves C.F m.senderRatchetKey ck m.counter msgType t1.ratchet ht1) ?_
  intro mkg t2 _ ht2
  rw [exec_bind, exec_get]
  dsimp only
  split
  · rw [exec_throw_bind]; exact ht2
  · cases spqr.recv t2.pqrState m.pqRatchet with
    | error b =>
      cases b <;> (dsimp only; rw [exec_throw_bind]; exact ht2)
    | ok pqPair =>
      dsimp only
      rw [exec_bind, exec_pure]
      dsimp only
      split
      · rw [exec_throw_bind]; exact ht2
      · cases aesCbcDecrypt C.D (mkg.generateKeys C.F pqPair.2).cipherKey
            (mkg.generateKeys C.F pqPair.2).iv m.ciphertext with
        | none => dsimp only; rw [exec_throw]; exact ht2
        | some ptext =>
          dsimp only
          rw [exec_bind, exec_modify]
          dsimp only
          rw [exec_pure]
          exact ht2

/-- `tryDecryptFromRecord` preserves `SeedsLen32` across all outcomes (rolling back state on error). -/
theorem tryDecryptFromRecord_preserves {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8))) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (st : SessionState PQ) (h : SeedsLen32 st) :
    SeedsLen32 (SessionState.tryDecryptFromRecord C spqr expected m msgType coins st).2 := by
  unfold SessionState.tryDecryptFromRecord
  split
  · exact h
  · rcases hexec : Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) st
      with ⟨res, updated⟩
    cases res with
    | error _ => exact h
    | ok ptext =>
      dsimp only
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hexec
      rw [exec_bind, exec_bind, exec_modifyGet] at hexec
      dsimp only at hexec
      rw [exec_bind, exec_modifyGet] at hexec
      dsimp only at hexec
      rw [exec_bind, exec_get] at hexec
      dsimp only at hexec
      cases hrem : st.remoteIdentity with
      | none =>
        rw [hrem] at hexec
        dsimp only at hexec
        rw [exec_throw] at hexec
        dsimp only at hexec
        cases hexec
      | some remote =>
        rw [hrem] at hexec
        dsimp only at hexec
        rw [exec_pure] at hexec
        dsimp only at hexec
        rw [exec_bind, exec_liftE] at hexec
        rcases htr : Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
             st.pqRatchetState, st.localIdentity, remote⟩ with ⟨rDec, session'⟩
        rw [htr] at hexec
        cases rDec with
        | error _ => cases hexec
        | ok pt =>
          dsimp only at hexec
          rw [exec_bind, exec_modify] at hexec
          dsimp only at hexec
          rw [exec_pure] at hexec
          rcases Prod.mk.inj hexec with ⟨_, rfl⟩
          have hpres := tripleRatchetDecrypt_preserves C spqr expected m msgType coins
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
             st.pqRatchetState, st.localIdentity, remote⟩ h
          rw [htr] at hpres
          exact hpres

end CryptoVerification.LibsignalTripleRatchet.Seeds
