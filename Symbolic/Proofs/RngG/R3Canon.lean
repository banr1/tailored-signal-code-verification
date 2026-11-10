/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import Symbolic.Proofs.SR.ModelW
import Symbolic.Proofs.SpecLemmas.CliPureBytes

/-!
# State invariants preserved by `SessionState.tryDecryptFromRecordW`

Establishes preservation of `RatchetRepr`, `SessRepr`, 32-byte message-key seed lengths,
receiver-chain count bounds, and empty SPQR state across a successful
`SessionState.tryDecryptFromRecordW` call (`tryDecryptFromRecordW_ok_state_props`).
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.RngG.R3

open CryptoVerification
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.E2E.Record
open CryptoVerification.E2E.Reach
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Seeds
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Proofs.libsignal.SR

/-! ## `Mut.exec` and list helpers -/

@[local simp] private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

@[local simp] private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

@[local simp] private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] private theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

@[local simp] private theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl

@[local simp] private theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

@[local simp] private theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

@[local simp] private theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

@[local simp] private theorem exec_onRatchet {PQ α : Type} (m : Mut RatchetState α)
    (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      ((Mut.exec m t.ratchet).1, { t with ratchet := (Mut.exec m t.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  simp

private theorem mem_set_cases {α : Type} {l : List α} {i : Nat} {x y : α}
    (h : y ∈ l.set i x) : y = x ∨ y ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.set, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a h)
    | succ i =>
      simp only [List.set, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases ih h with rfl | h'
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem a h')

private theorem mem_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : x ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      exact List.mem_cons_of_mem a (ih h)

private theorem length_eraseIdx_le {α : Type} (l : List α) (i : Nat) :
    (l.eraseIdx i).length ≤ l.length := by
  induction l generalizing i with
  | nil => simp [List.eraseIdx]
  | cons a l ih =>
    cases i with
    | zero => simp [List.eraseIdx]
    | succ i =>
      simp only [List.eraseIdx, List.length_cons]
      exact Nat.succ_le_succ (ih i)

/-! ## `RatchetRepr` preservation -/

/-- Ratchet-state invariant bounding skipped message keys by `maxMessageKeys` per receiver chain
and requiring a clamped sender ratchet private key. -/
def RatchetRepr (r : RatchetState) : Prop :=
  (∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) ∧
    (∀ sc, r.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)

/-- Session-state counterpart of `RatchetRepr`. -/
def SessRepr {PQ : Type} (st : SessionState PQ) : Prop :=
  (∀ c ∈ st.receiverChains, c.messageKeys.length ≤ maxMessageKeys) ∧
    (∀ sc, st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)

private theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  apply List.Vector.ext
  intro j
  by_cases h31 : j = 31
  · subst h31
    simp only [Ratchet.clampScalar, List.Vector.get_set_same]
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, BitVec.or_assoc]
    rfl
  · by_cases h0 : j = 0
    · subst h0
      simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_same]
      rw [BitVec.and_assoc, BitVec.and_self]
    · simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_of_ne (Ne.symm h0)]

private theorem clampScalar_keyPair_generate (C : Crypto) (coins : BitVec 256) :
    Ratchet.clampScalar (KeyPair.generate C coins).privateKey.bytes =
      (KeyPair.generate C coins).privateKey.bytes :=
  clampScalar_idem (Ratchet.keyToBytesVec32 coins)

theorem takeSkippedKey_ratchetRepr (their : PublicKey) (counter : BitVec 32) (r : RatchetState)
    (h : RatchetRepr r) :
    RatchetRepr (Mut.exec (RatchetState.takeSkippedKey their counter) r).2 := by
  unfold RatchetState.takeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simpa [h1] using h
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simpa [h1, h2] using h
    · rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simpa [h1, h2, h3] using h
      · rcases h4 : c.messageKeys[pos]? with _ | key
        · simpa [h1, h2, h3, h4] using h
        · simp only [h1, h2, h3, h4, exec_bind, exec_get, exec_set, exec_pure]
          refine ⟨?_, h.2⟩
          intro c' hc'
          rcases mem_set_cases hc' with rfl | hc'
          · exact (length_eraseIdx_le c.messageKeys pos).trans (h.1 c (mem_of_getElem? h2))
          · exact h.1 c' hc'

theorem storeSkippedKey_ratchetRepr (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) (h : RatchetRepr r) :
    RatchetRepr (Mut.exec (RatchetState.storeSkippedKey their key) r).2 := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simpa [h1] using h
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simpa [h1, h2] using h
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      refine ⟨?_, h.2⟩
      intro c' hc'
      rcases mem_set_cases hc' with rfl | hc'
      · have hc_len := h.1 c (mem_of_getElem? h2)
        dsimp only
        split_ifs with hlt
        · simp only [List.length_dropLast, List.length_cons]
          omega
        · simp only [List.length_cons] at hlt ⊢
          omega
      · exact h.1 c' hc'

theorem setReceiverChainKey_ratchetRepr (their : PublicKey) (ck : ChainKey) (r : RatchetState)
    (h : RatchetRepr r) :
    RatchetRepr (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2 := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simpa [h1] using h
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simpa [h1, h2] using h
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      refine ⟨?_, h.2⟩
      intro c' hc'
      rcases mem_set_cases hc' with rfl | hc'
      · exact h.1 c (mem_of_getElem? h2)
      · exact h.1 c' hc'

theorem advanceChain_ratchetRepr (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : Nat) (ck : ChainKey) (r : RatchetState) (h : RatchetRepr r) :
    RatchetRepr (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2 := by
  induction fuel generalizing ck r with
  | zero => exact h
  | succ fuel ih =>
    unfold RatchetState.advanceChain
    split
    · rw [exec_bind]
      have h1 := storeSkippedKey_ratchetRepr their (ck.messageKeys F) r h
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨e | _, r1⟩
      · rw [hs] at h1
        exact h1
      · rw [hs] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck.nextChainKey F with _ | ck'
        · exact h1
        · exact ih ck' r1 h1
    · exact h

theorem consumeMessageKey_ratchetRepr (F : ShaCompress) (their : PublicKey) (ck : ChainKey)
    (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) (h : RatchetRepr r) :
    RatchetRepr (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2 := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    have h1 := takeSkippedKey_ratchetRepr their counter r h
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨e | opt, r1⟩
    · rw [ht] at h1
      exact h1
    · rw [ht] at h1
      cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    split
    · simpa using h
    · rw [exec_bind]
      have h1 := advanceChain_ratchetRepr F their counter (counter - ck.index).toNat ck r h
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨e | ck1, r1⟩
      · rw [ha] at h1
        exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_ratchetRepr their ck2 r1 h1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨e | _, r2⟩ <;>
            · rw [hs] at h2
              exact h2

theorem dhRatchetStep_ratchetRepr (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : RatchetRepr r) :
    RatchetRepr (Mut.exec (RatchetState.dhRatchetStep C their coins) r).2 := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey
  simp only [exec_bind, exec_get]
  rcases hsc : r.senderChain with _ | sc
  · simpa using h
  · simp only [exec_bind, exec_modifyGet, exec_liftE]
    rcases hrc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
      _ | ⟨newRootKey, receiverChainKey⟩
    · exact h
    · simp only [exec_modify, exec_pure]
      rcases hrc2 : rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey with
        _ | ⟨finalRootKey, senderChainKey⟩
      · exact h
      · refine ⟨?_, ?_⟩
        · intro c hc
          unfold RatchetState.evictReceiverChains at hc
          have hc' := List.mem_of_mem_drop hc
          rcases List.mem_append.mp hc' with hc0 | hc0
          · exact h.1 c hc0
          · simp only [List.mem_singleton] at hc0
            subst hc0
            simp
        · intro sc' hsc'
          simp only [Option.some.injEq] at hsc'
          subst hsc'
          exact clampScalar_keyPair_generate C coins

theorem ensureReceiverChain_ratchetRepr (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : RatchetRepr r) :
    RatchetRepr (Mut.exec (RatchetState.ensureReceiverChain C their coins) r).2 := by
  unfold RatchetState.ensureReceiverChain
  simp only [exec_bind, exec_get, exec_liftE]
  rcases hf : r.findReceiverChainKey their with _ | (_ | ck)
  · exact h
  · exact dhRatchetStep_ratchetRepr C their coins r h
  · simpa using h

/-! ## Receiver-chain length bounds -/

theorem length_evictReceiverChains_le (cs : List ReceiverChain) :
    (RatchetState.evictReceiverChains cs).length ≤ maxReceiverChains := by
  unfold RatchetState.evictReceiverChains maxReceiverChains
  rw [List.length_drop]
  omega

theorem takeSkippedKey_receiverChains_length (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.takeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp [h1, h2, h3]
      · rcases h4 : c.messageKeys[pos]? with _ | key
        · simp [h1, h2, h3, h4]
        · simp only [h1, h2, h3, h4, exec_bind, exec_get, exec_set, exec_pure, List.length_set]

theorem storeSkippedKey_receiverChains_length (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c <;>
      simp [h1, h2, List.length_set]

theorem setReceiverChainKey_receiverChains_length (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c <;>
      simp [h1, h2, List.length_set]

theorem advanceChain_receiverChains_length (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : Nat) (ck : ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains.length =
      r.receiverChains.length := by
  induction fuel generalizing ck r with
  | zero => rfl
  | succ fuel ih =>
    unfold RatchetState.advanceChain
    split
    · rw [exec_bind]
      have h1 := storeSkippedKey_receiverChains_length their (ck.messageKeys F) r
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨e | _, r1⟩
      · rw [hs] at h1
        exact h1
      · rw [hs] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck.nextChainKey F with _ | ck'
        · exact h1
        · exact (ih ck' r1).trans h1
    · rfl

theorem consumeMessageKey_receiverChains_length (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    have h1 := takeSkippedKey_receiverChains_length their counter r
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨e | opt, r1⟩
    · rw [ht] at h1
      exact h1
    · rw [ht] at h1
      cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    split
    · rfl
    · rw [exec_bind]
      have h1 := advanceChain_receiverChains_length F their counter (counter - ck.index).toNat ck r
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨e | ck1, r1⟩
      · rw [ha] at h1
        exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_receiverChains_length their ck2 r1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨e | _, r2⟩ <;>
            · rw [hs] at h2
              exact h2.trans h1

theorem dhRatchetStep_receiverChains_lt (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : r.receiverChains.length < 2 ^ 32) :
    (Mut.exec (RatchetState.dhRatchetStep C their coins) r).2.receiverChains.length < 2 ^ 32 := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey
  simp only [exec_bind, exec_get]
  rcases hsc : r.senderChain with _ | sc
  · simpa using h
  · simp only [exec_bind, exec_modifyGet, exec_liftE]
    rcases hrc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
      _ | ⟨newRootKey, receiverChainKey⟩
    · exact h
    · simp only [exec_modify, exec_pure]
      rcases hrc2 : rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey with
        _ | ⟨finalRootKey, senderChainKey⟩
      · exact h
      · have hLe := length_evictReceiverChains_le
          (r.receiverChains ++ [⟨their, some receiverChainKey, []⟩])
        unfold maxReceiverChains at hLe
        dsimp only
        omega

theorem ensureReceiverChain_receiverChains_lt (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : r.receiverChains.length < 2 ^ 32) :
    (Mut.exec (RatchetState.ensureReceiverChain C their coins) r).2.receiverChains.length <
      2 ^ 32 := by
  unfold RatchetState.ensureReceiverChain
  simp only [exec_bind, exec_get, exec_liftE]
  rcases hf : r.findReceiverChainKey their with _ | (_ | ck)
  · exact h
  · exact dhRatchetStep_receiverChains_lt C their coins r h
  · simpa using h

theorem dhRatchetStep_receiverChains_le (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : r.receiverChains.length ≤ maxReceiverChains) :
    (Mut.exec (RatchetState.dhRatchetStep C their coins) r).2.receiverChains.length ≤
      maxReceiverChains := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey
  simp only [exec_bind, exec_get]
  rcases hsc : r.senderChain with _ | sc
  · simpa using h
  · simp only [exec_bind, exec_modifyGet, exec_liftE]
    rcases hrc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
      _ | ⟨newRootKey, receiverChainKey⟩
    · exact h
    · simp only [exec_modify, exec_pure]
      rcases hrc2 : rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey with
        _ | ⟨finalRootKey, senderChainKey⟩
      · exact h
      · exact length_evictReceiverChains_le _

theorem ensureReceiverChain_receiverChains_le (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : r.receiverChains.length ≤ maxReceiverChains) :
    (Mut.exec (RatchetState.ensureReceiverChain C their coins) r).2.receiverChains.length ≤
      maxReceiverChains := by
  unfold RatchetState.ensureReceiverChain
  simp only [exec_bind, exec_get, exec_liftE]
  rcases hf : r.findReceiverChainKey their with _ | (_ | ck)
  · exact h
  · exact dhRatchetStep_receiverChains_le C their coins r h
  · simpa using h

/-! ## Session-state properties of `tryDecryptFromRecordW` -/

private theorem tryDecryptWithStateW_ok_inv {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W : AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState PQ} {ptext : List (BitVec 8)}
    (hok : Mut.exec (SessionState.tryDecryptWithStateW C W spqr expected msg msgType coins) st =
      (.ok ptext, st')) :
    ∃ (remIk : IdentityKey) (tr_out : TripleRatchet PQ),
      st.remoteIdentity = some remIk ∧
      Mut.exec (TripleRatchet.decryptW C W spqr expected msg msgType coins)
        ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter,
          CryptoGames.LibsignalSession.maxForwardJumps⟩,
         st.pqRatchetState, st.localIdentity, remIk⟩ = (.ok ptext, tr_out) ∧
      st' = { st with
        rootKey := tr_out.ratchet.rootKey
        previousCounter := tr_out.ratchet.previousCounter
        senderChain := tr_out.ratchet.senderChain
        receiverChains := tr_out.ratchet.receiverChains
        pqRatchetState := tr_out.pqrState
        pendingPreKey := false } := by
  unfold SessionState.tryDecryptWithStateW TripleRatchet.fromSessionState
    SessionState.takeRatchetState SessionState.takePqRatchetState
    TripleRatchet.applyToSessionState SessionState.clearUnacknowledgedPreKeyMessage at hok
  rw [exec_bind, exec_bind, exec_modifyGet] at hok
  dsimp only at hok
  rw [exec_bind, exec_modifyGet] at hok
  dsimp only at hok
  rw [exec_bind, exec_get] at hok
  dsimp only at hok
  cases hrem : st.remoteIdentity with
  | none =>
    rw [hrem] at hok
    dsimp only at hok
    rw [exec_throw] at hok
    cases hok
  | some remIk =>
    rw [hrem] at hok
    dsimp only at hok
    rw [exec_pure] at hok
    dsimp only at hok
    rcases hdec :
      Mut.exec (TripleRatchet.decryptW C W spqr expected msg msgType coins)
        ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter,
          CryptoGames.LibsignalSession.maxForwardJumps⟩,
         st.pqRatchetState, st.localIdentity, remIk⟩ with ⟨res, tr_out⟩
    rw [hdec] at hok
    cases res with
    | error e =>
      dsimp only at hok
      rw [exec_bind, exec_liftE] at hok
      cases hok
    | ok pt =>
      dsimp only at hok
      rw [exec_bind, exec_liftE] at hok
      dsimp only at hok
      rw [exec_bind, exec_modify] at hok
      dsimp only at hok
      rw [exec_pure] at hok
      injection hok with h1 h2
      injection h1 with hpt
      subst hpt h2
      exact ⟨remIk, tr_out, rfl, hdec, rfl⟩

private theorem tripleRatchet_decryptW_ok_inv {PQ PQC : Type}
    {C : Crypto} {W : AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {tr0 tr_out : TripleRatchet PQ} {ptext : List (BitVec 8)}
    (hok : Mut.exec (TripleRatchet.decryptW C W spqr expected msg msgType coins) tr0 =
      (.ok ptext, tr_out)) :
    ∃ (ck : ChainKey) (r1 r2 : RatchetState) (mkGen : MessageKeyGenerator)
      (newPqrState : PQ) (pqrKey : CryptoGames.HKDF.Salt),
      Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins) tr0.ratchet =
        (.ok ck, r1) ∧
      Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType) r1 =
        (.ok mkGen, r2) ∧
      spqr.recv tr0.pqrState msg.pqRatchet = .ok (newPqrState, pqrKey) ∧
      tr_out = { tr0 with ratchet := r2, pqrState := newPqrState } := by
  unfold TripleRatchet.decryptW at hok
  rw [exec_bind, exec_onRatchet] at hok
  rcases hens : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins) tr0.ratchet
    with ⟨res1, r1⟩
  rw [hens] at hok
  cases res1 with
  | error e => cases hok
  | ok ck =>
    dsimp only at hok
    rw [exec_bind, exec_onRatchet] at hok
    dsimp only at hok
    rcases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
      msgType) r1 with ⟨res2, r2⟩
    rw [hcmk] at hok
    cases res2 with
    | error e => cases hok
    | ok mkGen =>
      dsimp only at hok
      rw [exec_bind, exec_get] at hok
      dsimp only at hok
      cases hpan : spqr.recvPanics tr0.pqrState msg.pqRatchet
      case true =>
        simp only [hpan, eq_self, ↓reduceIte] at hok; rw [exec_bind, exec_throw] at hok; cases hok
      simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hok
      cases hspqr : spqr.recv tr0.pqrState msg.pqRatchet with
      | error b =>
        rw [hspqr] at hok
        cases b <;> (dsimp only at hok; rw [exec_bind, exec_throw] at hok; cases hok)
      | ok pqrPair =>
        rcases pqrPair with ⟨newPqrState, pqrKey⟩
        rw [hspqr] at hok
        dsimp only at hok
        rw [exec_bind, exec_pure] at hok
        dsimp only at hok
        by_cases hmac : msg.verifyMacWithAddresses C.F expected tr0.remoteIdentityKey
            tr0.localIdentityKey (mkGen.generateKeys C.F pqrKey).macKey = true
        · simp only [hmac, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
          cases hdec : W.dec (mkGen.generateKeys C.F pqrKey).cipherKey
              (mkGen.generateKeys C.F pqrKey).iv msg.ciphertext with
          | none =>
            rw [hdec] at hok
            dsimp only at hok
            rw [exec_throw] at hok
            cases hok
          | some pt =>
            rw [hdec] at hok
            dsimp only at hok
            rw [exec_bind, exec_modify] at hok
            dsimp only at hok
            rw [exec_pure] at hok
            injection hok with h1 h2
            injection h1 with hpt
            subst hpt h2
            exact ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, rfl, hcmk, rfl, rfl⟩
        · have hmac_f : msg.verifyMacWithAddresses C.F expected tr0.remoteIdentityKey
              tr0.localIdentityKey (mkGen.generateKeys C.F pqrKey).macKey = false :=
            Bool.eq_false_iff.mpr hmac
          simp only [hmac_f, Bool.not_false, ↓reduceIte] at hok
          rw [exec_bind, exec_throw] at hok
          cases hok

/-- Structural equalities and invariant preservation across a successful
`SessionState.tryDecryptFromRecordW`. -/
theorem tryDecryptFromRecordW_ok_state_props {PQC : Type}
    {C : Crypto} {W : AesW} {spqr : Spqr (List (BitVec 8)) PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState (List (BitVec 8))} {pt : List (BitVec 8)}
    (hok : SessionState.tryDecryptFromRecordW C W spqr expected msg msgType coins st =
      (.ok pt, st')) :
    st'.localIdentity = st.localIdentity ∧
    st'.remoteIdentity = st.remoteIdentity ∧
    st'.pendingPreKey = false ∧
    (SeedsLen32 st → SeedsLen32 st') ∧
    (st.receiverChains.length < 2 ^ 32 → st'.receiverChains.length < 2 ^ 32) ∧
    (st.receiverChains.length ≤ maxReceiverChains →
      st'.receiverChains.length ≤ maxReceiverChains) ∧
    (SessRepr st → SessRepr st') ∧
    (st.pqRatchetState = [] →
      (∀ m st'' k, spqr.recv [] m = .ok (st'', k) → st'' = []) →
      st'.pqRatchetState = []) := by
  unfold SessionState.tryDecryptFromRecordW at hok
  split at hok
  · cases hok
  · rcases hd : Mut.exec (SessionState.tryDecryptWithStateW C W spqr expected msg msgType coins) st
      with ⟨e | ptext, updated⟩
    · rw [hd] at hok; cases hok
    · rw [hd] at hok
      injection hok with h1 h2
      injection h1 with hpt
      subst hpt h2
      obtain ⟨remIk, tr_out, _, hTr, hSt'⟩ := tryDecryptWithStateW_ok_inv hd
      obtain ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, hens, hcmk, hspqr, hTrOut⟩ :=
        tripleRatchet_decryptW_ok_inv hTr
      rw [hSt', hTrOut]
      dsimp only
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro hSeeds
        have h1 : RatchetSeedsLen32 r1 := by
          have h := ensureReceiverChain_preserves C msg.senderRatchetKey coins
            ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
            hSeeds
          simpa [hens] using h
        have h2 : RatchetSeedsLen32 r2 := by
          have h := consumeMessageKey_preserves C.F msg.senderRatchetKey ck
            msg.counter msgType r1 h1
          simpa [hcmk] using h
        exact h2
      · intro hLt
        have h1 : r1.receiverChains.length < 2 ^ 32 := by
          have h := ensureReceiverChain_receiverChains_lt C msg.senderRatchetKey coins
            ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
            hLt
          simpa [hens] using h
        have h2 := consumeMessageKey_receiverChains_length C.F msg.senderRatchetKey
          ck msg.counter msgType r1
        rw [hcmk] at h2
        dsimp only at h2
        omega
      · intro hLe
        have h1 : r1.receiverChains.length ≤ maxReceiverChains := by
          have h := ensureReceiverChain_receiverChains_le C msg.senderRatchetKey coins
            ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
            hLe
          simpa [hens] using h
        have h2 := consumeMessageKey_receiverChains_length C.F msg.senderRatchetKey
          ck msg.counter msgType r1
        rw [hcmk] at h2
        dsimp only at h2
        omega
      · intro hRepr
        have h1 : RatchetRepr r1 := by
          have h := ensureReceiverChain_ratchetRepr C msg.senderRatchetKey coins
            ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
            hRepr
          simpa [hens] using h
        have h2 : RatchetRepr r2 := by
          have h := consumeMessageKey_ratchetRepr C.F msg.senderRatchetKey ck
            msg.counter msgType r1 h1
          simpa [hcmk] using h
        exact h2
      · intro hPq0 hPqRecv
        rw [hPq0] at hspqr
        exact hPqRecv msg.pqRatchet newPqrState pqrKey hspqr

end Proofs.libsignal.RngG.R3
