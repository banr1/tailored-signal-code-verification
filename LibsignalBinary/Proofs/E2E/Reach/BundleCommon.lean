/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionSMProofDefs
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.TripleRatchet.Seeds.Model

/-!
# Reachable-State Invariant Bundle for SPQR-Off Sessions

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition here.

Establishes `ReachInv C g` by single induction over `Reach (spqrOffSessionParams C) g`, packaging
identity-key agreement, 32-byte message-key seeds, chain and skipped-key count bounds, clamped
sender ratchet private keys, empty post-quantum state, epoch alignment, record-level decoder scope,
and `< 2 ^ 20` record encoding length bounds.
-/

@[expose] public section

namespace CryptoVerification.E2E.Reach

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Seeds
open CryptoVerification.E2E CryptoVerification.E2E.Record CryptoVerification.E2E.Epochs

attribute [local simp] exec_pure exec_throw exec_get exec_set exec_modify exec_modifyGet
  exec_liftE exec_bind exec_map exec_onRatchet

/-! ## Representation Invariant on `RatchetState` and `SessionState` -/

/-- The session-level part of `RecordRepr`: at most `maxMessageKeys` (2000) skipped message keys per
receiver chain, and a clamped sender ratchet private key. -/
def SessRepr (st : SessionState Bytes) : Prop :=
  (∀ c ∈ st.receiverChains, c.messageKeys.length ≤ maxMessageKeys) ∧
    (∀ sc, st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)

def RatchetRepr (r : RatchetState) : Prop :=
  (∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) ∧
    (∀ sc, r.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)

theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
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

theorem clampScalar_keyPair_generate (C : Crypto) (coins : BitVec 256) :
    Ratchet.clampScalar (KeyPair.generate C coins).privateKey.bytes =
      (KeyPair.generate C coins).privateKey.bytes :=
  clampScalar_idem (Ratchet.keyToBytesVec32 coins)

private theorem mem_set_cases {α : Type} {l : List α} {i : ℕ} {x y : α}
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

private theorem mem_of_getElem? {α : Type} {l : List α} {i : ℕ} {x : α}
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

private theorem length_eraseIdx_le {α : Type} (l : List α) (i : ℕ) :
    (l.eraseIdx i).length ≤ l.length := by
  induction l generalizing i with
  | nil => simp [List.eraseIdx]
  | cons a l ih =>
    cases i with
    | zero => simp [List.eraseIdx]
    | succ i =>
      simp only [List.eraseIdx, List.length_cons]
      exact Nat.succ_le_succ (ih i)

theorem new_sessRepr (version : BitVec 8) (ourIdentity theirIdentity : IdentityKey)
    (rootKey : RootKey) (pq : Bytes) :
    SessRepr (SessionState.new version ourIdentity theirIdentity rootKey pq) := by
  simp [SessRepr, SessionState.new]

theorem addReceiverChain_sessRepr (s : SessionState Bytes) (sender : PublicKey) (ck : ChainKey)
    (h : SessRepr s) : SessRepr (s.addReceiverChain sender ck) := by
  refine ⟨?_, h.2⟩
  intro c hc
  unfold SessionState.addReceiverChain at hc
  simp only at hc
  have hcs : c ∈ s.receiverChains ++ [⟨sender, some ck, []⟩] := by
    split at hc
    · exact List.mem_of_mem_drop hc
    · exact hc
  rcases List.mem_append.mp hcs with hc' | hc'
  · exact h.1 c hc'
  · simp only [List.mem_singleton] at hc'
    subst hc'
    simp

theorem setSenderChain_sessRepr (s : SessionState Bytes) (sender : KeyPair) (ck : ChainKey)
    (hcl : Ratchet.clampScalar sender.privateKey.bytes = sender.privateKey.bytes)
    (h : SessRepr s) : SessRepr (s.setSenderChain sender ck) := by
  refine ⟨h.1, ?_⟩
  intro sc hsc
  simp only [SessionState.setSenderChain, Option.some.injEq] at hsc
  subst hsc
  exact hcl

theorem setUnacknowledgedPreKeyMessage_sessRepr (s : SessionState Bytes) (h : SessRepr s) :
    SessRepr s.setUnacknowledgedPreKeyMessage :=
  h

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

theorem setReceiverChainKey_ratchetRepr (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) (h : RatchetRepr r) :
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
    (counter : BitVec 32) (fuel : ℕ) (ck : ChainKey) (r : RatchetState) (h : RatchetRepr r) :
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

theorem sessRepr_initA (P : Params Bytes Unit) (k : InitKeys) :
    SessRepr (P.initA k).session := by
  unfold Params.initA initializeInitiatorSession
  dsimp only
  rcases rootCreateChain P.C k.rootKey
      (KeyPair.generate P.C k.bobSpkCoins).publicKey
      (KeyPair.generate P.C k.aliceRatchetCoins).privateKey with _ | ⟨rk', ck'⟩
  · exact setUnacknowledgedPreKeyMessage_sessRepr _
      (addReceiverChain_sessRepr _ _ _ (new_sessRepr _ _ _ _ _))
  · exact setUnacknowledgedPreKeyMessage_sessRepr _
      (setSenderChain_sessRepr _ _ _ (clampScalar_keyPair_generate P.C k.aliceRatchetCoins)
        (addReceiverChain_sessRepr _ _ _ (new_sessRepr _ _ _ _ _)))

theorem sessRepr_initB (P : Params Bytes Unit) (k : InitKeys) :
    SessRepr (P.initB k).session := by
  unfold Params.initB initializeRecipientSession
  exact setSenderChain_sessRepr _ _ _ (clampScalar_keyPair_generate P.C k.bobSpkCoins)
    (new_sessRepr _ _ _ _ _)

theorem sessRepr_messageEncrypt (C : Crypto) (codec : SignalMessageProtoCodec) (addresses : Option Bytes)
    (ptext : Bytes) (coins : Unit) (st st' : SessionState Bytes) (msg : SignalMessage)
    (hrep : SessRepr st)
    (h : SessionState.messageEncrypt C codec spqrOffB addresses ptext coins st = (.ok msg, st')) :
    SessRepr st' := by
  unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, exec_pure] at h
        unfold OutgoingTripleRatchet.encrypt at h
        simp only [spqrOffB, exec_bind, exec_get, exec_liftE, Bool.false_eq_true, ↓reduceIte] at h
        rcases hn : sc.chainKey.nextChainKey C.F with _ | next
        · simp [hn] at h
        · simp only [hn, exec_set, exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
          rcases h with ⟨_, rfl⟩
          refine ⟨hrep.1, ?_⟩
          intro sc' hsc'
          simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_some,
            Option.some.injEq] at hsc'
          subst hsc'
          exact hrep.2 sc hsc

/-- The empty-state `spqr::recv` model (`spqrOffB.recv`) only succeeds with the empty state and no
salt. -/
theorem spqrRecvEmpty_ok_eq {msg : Bytes} {r : Bytes × HKDF.Salt}
    (h : LibsignalSpqr.spqrRecvEmpty msg = .ok r) : r = ([], none) := by
  unfold LibsignalSpqr.spqrRecvEmpty at h
  split at h
  · exact (Except.ok.inj h).symm
  · cases h

theorem sessRepr_tryDecryptFromRecord (C : Crypto) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (st st' : SessionState Bytes) (pt : Bytes)
    (hrep : SessRepr st)
    (h : SessionState.tryDecryptFromRecord C spqrOffB expected m msgType coins st = (.ok pt, st')) :
    SessRepr st' := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C spqrOffB expected m msgType coins) st with
      ⟨e | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at hd
      · simp only [hrem, exec_bind, exec_modifyGet, exec_get, exec_pure] at hd
        rcases hdec : Mut.exec (TripleRatchet.decrypt C spqrOffB expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · simp [hdec] at hd
        · rw [hdec] at hd
          simp only [exec_liftE, exec_modify, Prod.mk.injEq, Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          unfold TripleRatchet.decrypt at hdec
          rw [exec_bind, exec_onRatchet] at hdec
          have hr0 : RatchetRepr
              ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ :=
            hrep
          have hr1 := ensureReceiverChain_ratchetRepr C m.senderRatchetKey coins _ hr0
          rcases he : Mut.exec (RatchetState.ensureReceiverChain C m.senderRatchetKey coins)
              ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ with
            ⟨e | ck, r1⟩
          · simp [he] at hdec
          · rw [he] at hdec hr1
            simp only [exec_bind, exec_onRatchet] at hdec
            have hr2 := consumeMessageKey_ratchetRepr C.F m.senderRatchetKey ck m.counter msgType r1 hr1
            rcases hc : Mut.exec (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType) r1 with
              ⟨e | mkg, r2⟩
            · simp [hc] at hdec
            · rw [hc] at hdec hr2
              simp only [spqrOffB, exec_get, Bool.false_eq_true, ↓reduceIte] at hdec
              split at hdec
              · rename_i r hr
                obtain rfl := spqrRecvEmpty_ok_eq hr
                simp only [exec_bind, exec_pure] at hdec
                split at hdec
                · simp at hdec
                · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F none).cipherKey
                      (mkg.generateKeys C.F none).iv m.ciphertext with _ | ptext'
                  · simp [haes] at hdec
                  · simp only [haes] at hdec
                    rcases hdec with ⟨_, rfl⟩
                    exact hr2
              · simp at hdec
              · simp at hdec

/-! ## Receiver Chain Length Bounds (`≤ maxReceiverChains`) -/

theorem length_evictReceiverChains_le (cs : List ReceiverChain) :
    (RatchetState.evictReceiverChains cs).length ≤ maxReceiverChains := by
  unfold RatchetState.evictReceiverChains maxReceiverChains
  rw [List.length_drop]
  omega

theorem takeSkippedKey_receiverChains_length (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains.length =
      r.receiverChains.length := by
  have := congrArg List.length (takeSkippedKey_map_senderRatchetKey their counter r)
  simpa [List.length_map] using this

theorem storeSkippedKey_receiverChains_length (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains.length =
      r.receiverChains.length := by
  have := congrArg List.length (storeSkippedKey_map_senderRatchetKey their key r)
  simpa [List.length_map] using this

theorem setReceiverChainKey_receiverChains_length (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains.length =
      r.receiverChains.length := by
  have := congrArg List.length (setReceiverChainKey_map_senderRatchetKey their ck r)
  simpa [List.length_map] using this

theorem consumeMessageKey_receiverChains_length (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains.length =
      r.receiverChains.length := by
  have := congrArg List.length (consumeMessageKey_map_senderRatchetKey F their ck counter msgType r)
  simpa [List.length_map] using this

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

theorem tr_decrypt_ok_props (C : Crypto) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (t t' : TripleRatchet Bytes) (pt : Bytes)
    (hlen : t.ratchet.receiverChains.length ≤ maxReceiverChains)
    (h : Mut.exec (TripleRatchet.decrypt C spqrOffB expected m msgType coins) t = (.ok pt, t')) :
    t'.ratchet.receiverChains.length ≤ maxReceiverChains ∧ t'.pqrState = [] := by
  unfold TripleRatchet.decrypt at h
  rw [exec_bind, exec_onRatchet] at h
  have h1 := ensureReceiverChain_receiverChains_le C m.senderRatchetKey coins t.ratchet hlen
  rcases he : Mut.exec (RatchetState.ensureReceiverChain C m.senderRatchetKey coins) t.ratchet with
    ⟨e | ck, r1⟩
  · simp [he] at h
  · rw [he] at h h1
    simp only [exec_bind, exec_onRatchet] at h
    have h2 := consumeMessageKey_receiverChains_length C.F m.senderRatchetKey ck m.counter msgType r1
    rcases hc : Mut.exec (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType) r1 with
      ⟨e | mkg, r2⟩
    · simp [hc] at h
    · rw [hc] at h h2
      simp only [spqrOffB, exec_get, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i r hr
        obtain rfl := spqrRecvEmpty_ok_eq hr
        simp only [exec_bind, exec_pure] at h
        split at h
        · simp at h
        · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F none).cipherKey
              (mkg.generateKeys C.F none).iv m.ciphertext with _ | ptext
          · simp [haes] at h
          · simp only [haes] at h
            rcases h with ⟨_, rfl⟩
            exact ⟨h2.trans_le h1, rfl⟩
      · simp at h
      · simp at h

theorem tryDecryptFromRecord_ok_props (C : Crypto) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (st st' : SessionState Bytes) (pt : Bytes)
    (hseeds : SeedsLen32 st) (hlen : st.receiverChains.length ≤ maxReceiverChains)
    (h : SessionState.tryDecryptFromRecord C spqrOffB expected m msgType coins st = (.ok pt, st')) :
    SeedsLen32 st' ∧ st'.receiverChains.length ≤ maxReceiverChains ∧ st'.pqRatchetState = [] ∧
      st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity := by
  have hseeds' : SeedsLen32 st' := by
    have := tryDecryptFromRecord_preserves C spqrOffB expected m msgType coins st hseeds
    simpa [h] using this
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C spqrOffB expected m msgType coins) st with
      ⟨e | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at hd
      · simp only [hrem, exec_bind, exec_modifyGet, exec_get, exec_pure] at hd
        rcases hdec : Mut.exec (TripleRatchet.decrypt C spqrOffB expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · simp [hdec] at hd
        · rw [hdec] at hd
          simp only [exec_liftE, exec_modify, Prod.mk.injEq, Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          obtain ⟨hlen', hpq'⟩ := tr_decrypt_ok_props C expected m msgType coins _ tr' pt' hlen hdec
          exact ⟨hseeds', hlen', hpq', rfl, rfl⟩

theorem messageEncrypt_ok_props (C : Crypto) (codec : SignalMessageProtoCodec) (addresses : Option Bytes)
    (ptext : Bytes) (coins : Unit) (st st' : SessionState Bytes) (msg : SignalMessage)
    (hseeds : SeedsLen32 st) (hlen : st.receiverChains.length ≤ maxReceiverChains)
    (h : SessionState.messageEncrypt C codec spqrOffB addresses ptext coins st = (.ok msg, st')) :
    SeedsLen32 st' ∧ st'.receiverChains.length ≤ maxReceiverChains ∧ st'.pqRatchetState = [] ∧
      st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity := by
  unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, exec_pure] at h
        unfold OutgoingTripleRatchet.encrypt at h
        simp only [spqrOffB, exec_bind, exec_get, exec_liftE, Bool.false_eq_true, ↓reduceIte] at h
        rcases hn : sc.chainKey.nextChainKey C.F with _ | next
        · simp [hn] at h
        · simp only [hn, exec_set, exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
          rcases h with ⟨_, rfl⟩
          simp [OutgoingTripleRatchet.applyToSessionState, SeedsLen32] at hseeds ⊢
          exact ⟨hseeds, hlen⟩

/-! ## `SessionInv` and `ReachInv`: Inductive Bundle over `Reach (spqrOffSessionParams C) g` -/

/-- The session-level invariant of a reachable ghost state `g` at `C : Crypto`. -/
def SessionInv (_C : Crypto) (g : GhostState Bytes) : Prop :=
  SeedsLen32 g.session ∧
    g.session.receiverChains.length ≤ maxReceiverChains ∧
    g.session.pqRatchetState = [] ∧
    g.session.localIdentity = partyIdentityKey g.party ∧
    g.session.remoteIdentity = some (partyIdentityKey g.party.other) ∧
    SessRepr g.session

/-- The full invariant of a reachable ghost state `g` at `C : Crypto`: `SessionInv` plus epoch
alignment `g.Aligned`. -/
def ReachInv (C : Crypto) (g : GhostState Bytes) : Prop :=
  SessionInv C g ∧ g.Aligned

theorem reachInv_initA (C : Crypto) (k : InitKeys) : ReachInv C ((spqrOffSessionParams C).initA k) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, sessRepr_initA (spqrOffSessionParams C) k⟩, ?_⟩
  · unfold Params.initA initializeInitiatorSession
    dsimp only
    rcases rootCreateChain (spqrOffSessionParams C).C k.rootKey
        (KeyPair.generate (spqrOffSessionParams C).C k.bobSpkCoins).publicKey
        (KeyPair.generate (spqrOffSessionParams C).C k.aliceRatchetCoins).privateKey with _ | ⟨rk', ck'⟩ <;>
      simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
        SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains, SeedsLen32]
  · unfold Params.initA initializeInitiatorSession
    dsimp only
    rcases rootCreateChain (spqrOffSessionParams C).C k.rootKey
        (KeyPair.generate (spqrOffSessionParams C).C k.bobSpkCoins).publicKey
        (KeyPair.generate (spqrOffSessionParams C).C k.aliceRatchetCoins).privateKey with _ | ⟨rk', ck'⟩ <;>
      simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
        SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
  · unfold Params.initA initializeInitiatorSession spqrOffSessionParams
    dsimp only
    rcases rootCreateChain C k.rootKey
        (KeyPair.generate C k.bobSpkCoins).publicKey
        (KeyPair.generate C k.aliceRatchetCoins).privateKey with _ | ⟨rk', ck'⟩ <;>
      simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
        SessionState.setUnacknowledgedPreKeyMessage, spqrOffB]
  · unfold Params.initA initializeInitiatorSession spqrOffSessionParams
    dsimp only
    rcases rootCreateChain C k.rootKey
        (KeyPair.generate C k.bobSpkCoins).publicKey
        (KeyPair.generate C k.aliceRatchetCoins).privateKey with _ | ⟨rk', ck'⟩ <;>
      simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
        SessionState.setUnacknowledgedPreKeyMessage]
  · unfold Params.initA initializeInitiatorSession spqrOffSessionParams
    dsimp only
    rcases rootCreateChain C k.rootKey
        (KeyPair.generate C k.bobSpkCoins).publicKey
        (KeyPair.generate C k.aliceRatchetCoins).privateKey with _ | ⟨rk', ck'⟩ <;>
      simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
        SessionState.setUnacknowledgedPreKeyMessage, Party.other]
  · unfold GhostState.Aligned Params.initA initializeInitiatorSession
    dsimp only
    rcases rootCreateChain (spqrOffSessionParams C).C k.rootKey
        (KeyPair.generate (spqrOffSessionParams C).C k.bobSpkCoins).publicKey
        (KeyPair.generate (spqrOffSessionParams C).C k.aliceRatchetCoins).privateKey with _ | ⟨rk', ck'⟩ <;>
      simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
        SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]

theorem reachInv_initB (C : Crypto) (k : InitKeys) : ReachInv C ((spqrOffSessionParams C).initB k) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, sessRepr_initB (spqrOffSessionParams C) k⟩, ?_⟩
  · simp [Params.initB, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
      SeedsLen32]
  · simp [Params.initB, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
  · simp [Params.initB, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
      spqrOffSessionParams, spqrOffB]
  · simp [Params.initB, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
      spqrOffSessionParams]
  · simp [Params.initB, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
      spqrOffSessionParams, Party.other]
  · simp [GhostState.Aligned, Params.initB, initializeRecipientSession, SessionState.new,
      SessionState.setSenderChain]

theorem reachInv_send (C : Crypto) (g : GhostState Bytes) (m : Bytes) (r : Unit)
    (hg : ReachInv C g) : ReachInv C ((spqrOffSessionParams C).send g m r).1 := by
  rw [Record.send_eq_afterSend]
  rcases hm : SessionState.messageEncrypt (spqrOffSessionParams C).C (spqrOffSessionParams C).codec (spqrOffSessionParams C).spqr
      ((spqrOffSessionParams C).sendAddrs g.party) m r g.session with ⟨_ | msg, s⟩
  · exact hg
  · obtain ⟨⟨hseeds, hlen, _, hloc, hrem, hrep⟩, hal⟩ := hg
    have hm' : SessionState.messageEncrypt (spqrOffSessionParams C).C (spqrOffSessionParams C).codec spqrOffB
        ((spqrOffSessionParams C).sendAddrs g.party) m r g.session = (.ok msg, s) := hm
    obtain ⟨hseeds', hlen', hpq', hloc', hrem'⟩ :=
      messageEncrypt_ok_props (spqrOffSessionParams C).C (spqrOffSessionParams C).codec ((spqrOffSessionParams C).sendAddrs g.party) m r
        g.session s msg hseeds hlen hm'
    have hrep' :=
      sessRepr_messageEncrypt (spqrOffSessionParams C).C (spqrOffSessionParams C).codec ((spqrOffSessionParams C).sendAddrs g.party) m r
        g.session s msg hrep hm'
    have hrc : s.receiverChains = g.session.receiverChains := by
      have := messageEncrypt_receiverChains (spqrOffSessionParams C).C (spqrOffSessionParams C).codec (spqrOffSessionParams C).spqr
        ((spqrOffSessionParams C).sendAddrs g.party) m r g.session
      simpa [hm] using this
    refine ⟨⟨hseeds', hlen', hpq', hloc'.trans hloc, hrem'.trans hrem, hrep'⟩, ?_⟩
    unfold GhostState.Aligned GhostState.afterSend
    dsimp only
    rw [hrc]
    exact hal

theorem reachInv_receive (C : Crypto) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (hg : ReachInv C g) (g' : GhostState Bytes) (t i : ℕ) (m : Bytes)
    (h : (spqrOffSessionParams C).receive g c rc = some (g', t, i, m)) : ReachInv C g' := by
  rw [Record.receive_eq_afterRecv] at h
  rcases htf : SignalMessage.tryFrom (spqrOffSessionParams C).codec c with _ | msg
  · simp [htf] at h
  · rw [htf] at h
    dsimp only at h
    rcases hd : SessionState.tryDecryptFromRecord (spqrOffSessionParams C).C (spqrOffSessionParams C).spqr
        ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc g.session with ⟨_ | pt, s⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Option.some.injEq] at h
      obtain ⟨⟨hseeds, hlen, _, hloc, hrem, hrep⟩, hal⟩ := hg
      have hd' : SessionState.tryDecryptFromRecord (spqrOffSessionParams C).C spqrOffB
          ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc g.session = (.ok pt, s) := hd
      obtain ⟨hseeds', hlen', hpq', hloc', hrem'⟩ :=
        tryDecryptFromRecord_ok_props (spqrOffSessionParams C).C ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc
          g.session s pt hseeds hlen hd'
      have hrep' :=
        sessRepr_tryDecryptFromRecord (spqrOffSessionParams C).C ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc
          g.session s pt hrep hd'
      rcases tryDecryptFromRecord_ok_ratchet (spqrOffSessionParams C).C (spqrOffSessionParams C).spqr
          ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc g.session s pt hd with
        ⟨ck, r1, mkg, r2, he, hc, hsrc⟩
      have hc_map := consumeMessageKey_map_senderRatchetKey (spqrOffSessionParams C).C.F msg.senderRatchetKey ck
        msg.counter .whisper r1
      rw [hc] at hc_map
      have hmap2 : s.receiverChains.map (·.senderRatchetKey) =
          r1.receiverChains.map (·.senderRatchetKey) := by
        rw [hsrc, hc_map]
      unfold GhostState.afterRecv at h
      dsimp only at h
      rcases hidx : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
        _ | idx
      · rw [hidx] at h
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, _, _, rfl⟩
        refine ⟨⟨hseeds', hlen', hpq', hloc'.trans hloc, hrem'.trans hrem, hrep'⟩, ?_⟩
        unfold GhostState.Aligned
        dsimp only
        have he_map := ensureReceiverChain_ok_none_map_senderRatchetKey (spqrOffSessionParams C).C
          msg.senderRatchetKey rc _ r1 ck hidx he
        have hs_len : s.receiverChains.length =
            (g.session.receiverChains.length + 1) -
              ((g.session.receiverChains.length + 1) - maxReceiverChains) := by
          have := congrArg List.length (hmap2.trans he_map)
          simpa [List.length_drop, List.length_append, List.length_map] using this
        have hce : g.chainEpochs.length = g.session.receiverChains.length := hal
        rw [List.length_drop, List.length_append, List.length_singleton, hce, hs_len]
        omega
      · rw [hidx] at h
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, _, _, rfl⟩
        refine ⟨⟨hseeds', hlen', hpq', hloc'.trans hloc, hrem'.trans hrem, hrep'⟩, ?_⟩
        unfold GhostState.Aligned
        dsimp only
        have he_map := ensureReceiverChain_ok_some_map_senderRatchetKey (spqrOffSessionParams C).C
          msg.senderRatchetKey rc _ r1 ck idx hidx he
        have hs_len : s.receiverChains.length = g.session.receiverChains.length := by
          have := congrArg List.length (hmap2.trans he_map)
          simpa [List.length_map] using this
        have hce : g.chainEpochs.length = g.session.receiverChains.length := hal
        rw [List.length_drop, hce, hs_len]
        omega

/-- Every reachable session-model state `g` (`Reach (spqrOffSessionParams C) g`) satisfies
`ReachInv C g`. -/
theorem reach_inv (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) : ReachInv C g := by
  induction hg with
  | initA k => exact reachInv_initA C k
  | initB k => exact reachInv_initB C k
  | @send g m r _ ih => exact reachInv_send C g m r ih
  | @recv g g' c rc x _ h ih => exact reachInv_receive C g c rc ih g' x.1 x.2.1 x.2.2 h

/-! ## Direct Projections from `Reach (spqrOffSessionParams C) g` -/

theorem reach_sessionInv (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    SessionInv C g :=
  (reach_inv C hg).1

theorem reach_aligned (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    g.Aligned :=
  (reach_inv C hg).2

theorem reach_seedsLen32 (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    SeedsLen32 g.session :=
  (reach_sessionInv C hg).1

theorem reach_receiverChains_le (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    g.session.receiverChains.length ≤ maxReceiverChains :=
  (reach_sessionInv C hg).2.1

theorem reach_receiverChains_lt (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    g.session.receiverChains.length < 2 ^ 32 := by
  have h := reach_receiverChains_le C hg
  unfold maxReceiverChains at h
  omega

theorem reach_pqRatchetState_eq_nil (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    g.session.pqRatchetState = [] :=
  (reach_sessionInv C hg).2.2.1

theorem reach_localIdentity_eq (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    g.session.localIdentity = partyIdentityKey g.party :=
  (reach_sessionInv C hg).2.2.2.1

theorem reach_remoteIdentity_eq (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    g.session.remoteIdentity = some (partyIdentityKey g.party.other) :=
  (reach_sessionInv C hg).2.2.2.2.1

theorem reach_sessRepr (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    SessRepr g.session :=
  (reach_sessionInv C hg).2.2.2.2.2

theorem reach_messageKeys_le (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    ∀ c ∈ g.session.receiverChains, c.messageKeys.length ≤ maxMessageKeys :=
  (reach_sessRepr C hg).1

theorem reach_senderKey_clamped (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    ∀ sc, g.session.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes :=
  (reach_sessRepr C hg).2

theorem idOfE_other_ne (p : Party) :
    some (partyIdentityKey p.other) ≠ some (partyIdentityKey p) := by
  cases p <;> decide

theorem reach_remoteIdentity_ne_local (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    g.session.remoteIdentity ≠ some g.session.localIdentity := by
  rw [reach_remoteIdentity_eq C hg, reach_localIdentity_eq C hg]
  exact idOfE_other_ne g.party

/-! ## Record-Level Bridges (`sessionOf`, `toRecord extrasM`, `DeserializeScope`, `encodeRecord`) -/

/-- The `Session Bytes` stored inside `Record.toRecord Record.extrasM g`. -/
def sessionOf (g : GhostState Bytes) : Session Bytes :=
  { state := g.session
    pendingPreKey := if g.session.pendingPreKey then some (Record.extrasM g.party).pending else none
    pendingKyberPreKey := none
    localRegistrationId := 0#32
    remoteRegistrationId := 0#32
    aliceBaseKey := [] }

theorem sessionOf_wf (g : GhostState Bytes) : (sessionOf g).Wf := by
  unfold sessionOf Session.Wf
  cases g.session.pendingPreKey <;> rfl

theorem toRecord_extrasM_eq (g : GhostState Bytes) :
    Record.toRecord Record.extrasM g = { currentSession := some (sessionOf g) } := by
  unfold Record.toRecord Record.extrasM sessionOf
  cases g.session.pendingPreKey <;> rfl

private theorem msgField9_pending_eq (b : Bool) (p : Party) :
    E2E.msgField 9 (if b then some E2E.encPlaceholderPendingPreKey else none) =
      Record.msgField 9
        ((if b then some (Record.extrasM p).pending else none).map Record.encPendingPreKey) := by
  cases b <;> rfl

theorem encodeRecord_eq_toRecord (g : GhostState Bytes) :
    E2E.encodeRecord g = Record.encodeRecord (Record.toRecord Record.extrasM g) := by
  unfold E2E.encodeRecord encSessionStructureSeed Record.encodeRecord Record.toRecord
  dsimp only [Option.map_some]
  unfold Record.encSession
  dsimp only
  rw [msgField9_pending_eq g.session.pendingPreKey g.party]
  have h10 : Record.uint32Field 10 (Record.extrasM g.party).remoteRegistrationId = [] := rfl
  have h11 : Record.uint32Field 11 (Record.extrasM g.party).localRegistrationId = [] := rfl
  have h13 : Record.bytesField 13 (Record.extrasM g.party).aliceBaseKey = [] := rfl
  have h14 : Record.msgField 14
      ((if g.session.pendingPreKey then (Record.extrasM g.party).kyber else none).map
        Record.encPendingKyber) = [] := by
    cases g.session.pendingPreKey <;> rfl
  rw [h10, h11, h13, h14]
  simp only [List.append_nil, List.append_assoc]
  rfl

theorem reach_sessionScope (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    DeserializeGeneral.SessionScope (sessionOf g) := by
  refine ⟨reach_receiverChains_le C hg, rfl, rfl, rfl, rfl, ?_⟩
  intro p hp
  unfold sessionOf Record.extrasM at hp
  dsimp only at hp
  split at hp
  · injection hp with hp'
    subst hp'
    exact ⟨rfl, rfl, rfl⟩
  · cases hp

theorem reach_recordPqEmpty (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    RecordPqEmpty (Record.toRecord Record.extrasM g) := by
  rw [toRecord_extrasM_eq]
  intro s hs
  injection hs with hs'
  subst hs'
  exact reach_pqRatchetState_eq_nil C hg

theorem reach_recordRepr (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    RecordRepr (Record.toRecord Record.extrasM g) := by
  rw [toRecord_extrasM_eq]
  intro s hs
  injection hs with hs'
  subst hs'
  refine ⟨reach_messageKeys_le C hg, reach_senderKey_clamped C hg, sessionOf_wf g, ?_⟩
  simp [sessionOf]

theorem reach_recordInScope (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    RecordInScope (Record.toRecord Record.extrasM g) := by
  rw [toRecord_extrasM_eq]
  intro s hs
  injection hs with hs'
  subst hs'
  refine ⟨reach_remoteIdentity_ne_local C hg, reach_seedsLen32 C hg,
    reach_receiverChains_lt C hg, ?_⟩
  intro k hk
  cases hk

theorem reach_inScope (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    InScope (Record.toRecord Record.extrasM g) :=
  ⟨reach_recordInScope C hg, reach_recordPqEmpty C hg, reach_recordRepr C hg⟩

theorem reach_deserializeScope (C : Crypto) {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    DeserializeGeneral.DeserializeScope (Record.toRecord Record.extrasM g) := by
  refine ⟨reach_inScope C hg, sessionOf g, ?_, reach_sessionScope C hg⟩
  rw [toRecord_extrasM_eq]

/-! ## Record Encoding Length Bounds (`< 2 ^ 20 < 2 ^ 32 < 2 ^ 62`) -/

/-- `< 2 ^ 20` bound on `(E2E.encodeRecord g).length` for any reachable state `g`. -/
theorem reach_encodeRecord_length_lt_20 (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (E2E.encodeRecord g).length < 2 ^ 20 := by
  rw [encodeRecord_eq_toRecord g]
  exact DeserializeGeneral.encodeRecord_length_lt (reach_deserializeScope C hg)

theorem reach_encodeRecord_length_lt (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (E2E.encodeRecord g).length < 2 ^ 32 :=
  Nat.lt_trans (reach_encodeRecord_length_lt_20 C hg) (by decide)

theorem reach_encodeRecord_length_lt_62 (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (E2E.encodeRecord g).length < 2 ^ 62 :=
  Nat.lt_trans (reach_encodeRecord_length_lt_20 C hg) (by decide)

/-! ## `SessionInv` Projections, Post-Call Preservation, and `CanonRecord` Bridges -/

theorem inScope_of_sessionInv (C : Crypto) {g : GhostState Bytes} (h : SessionInv C g) :
    InScope (Record.toRecord Record.extrasM g) := by
  obtain ⟨hseeds, hlen, hpq, hloc, hrem, hmk, hcl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [toRecord_extrasM_eq]
    intro s hs; injection hs with hs'; subst hs'
    dsimp [sessionOf]
    refine ⟨?_, hseeds, by unfold maxReceiverChains at hlen; omega, ?_⟩
    · rw [hrem, hloc]; exact idOfE_other_ne g.party
    · intro k hk; cases hk
  · rw [toRecord_extrasM_eq]
    intro s hs; injection hs with hs'; subst hs'
    exact hpq
  · rw [toRecord_extrasM_eq]
    intro s hs; injection hs with hs'; subst hs'
    refine ⟨hmk, hcl, sessionOf_wf g, ?_⟩
    simp [sessionOf]

theorem deserializeScope_of_sessionInv (C : Crypto) {g : GhostState Bytes} (h : SessionInv C g) :
    DeserializeGeneral.DeserializeScope (Record.toRecord Record.extrasM g) := by
  refine ⟨inScope_of_sessionInv C h, sessionOf g, ?_, h.2.1, rfl, rfl, rfl, rfl, ?_⟩
  · rw [toRecord_extrasM_eq]
  · intro p hp
    unfold sessionOf Record.extrasM at hp
    dsimp only at hp
    split at hp
    · injection hp with hp'; subst hp'; exact ⟨rfl, rfl, rfl⟩
    · cases hp

theorem encodeRecord_length_lt_20_of_sessionInv (C : Crypto) {g : GhostState Bytes}
    (h : SessionInv C g) :
    (E2E.encodeRecord g).length < 2 ^ 20 := by
  rw [encodeRecord_eq_toRecord g]
  exact DeserializeGeneral.encodeRecord_length_lt (deserializeScope_of_sessionInv C h)

theorem sessionInv_of_send_ok (C : Crypto) {g : GhostState Bytes} (m : Bytes) (r : Unit)
    (msg : SignalMessage) (s : SessionState Bytes) (hg : Reach (spqrOffSessionParams C) g)
    (h : SessionState.messageEncrypt (spqrOffSessionParams C).C (spqrOffSessionParams C).codec (spqrOffSessionParams C).spqr
      ((spqrOffSessionParams C).sendAddrs g.party) m r g.session = (.ok msg, s)) :
    SessionInv C { g with session := s } := by
  have hinv := (reachInv_send C g m r (reach_inv C hg)).1
  rw [Record.send_eq_afterSend, h] at hinv
  exact hinv

theorem sessionInv_of_recv_ok (C : Crypto) {g : GhostState Bytes} (msg : SignalMessage)
    (rc : BitVec 256) (pt : Bytes) (s : SessionState Bytes) (hg : Reach (spqrOffSessionParams C) g)
    (h : SessionState.tryDecryptFromRecord (spqrOffSessionParams C).C (spqrOffSessionParams C).spqr
      ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc g.session = (.ok pt, s)) :
    SessionInv C { g with session := s } := by
  obtain ⟨hseeds, hlen, _, hloc, hrem, hrep⟩ := reach_sessionInv C hg
  have hd' : SessionState.tryDecryptFromRecord (spqrOffSessionParams C).C spqrOffB
      ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc g.session = (.ok pt, s) := h
  obtain ⟨hseeds', hlen', hpq', hloc', hrem'⟩ :=
    tryDecryptFromRecord_ok_props (spqrOffSessionParams C).C ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc
      g.session s pt hseeds hlen hd'
  have hrep' :=
    sessRepr_tryDecryptFromRecord (spqrOffSessionParams C).C ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc
      g.session s pt hrep hd'
  exact ⟨hseeds', hlen', hpq', hloc'.trans hloc, hrem'.trans hrem, hrep'⟩

theorem reach_recordInv (C : Crypto) (E : HonestEnv) {g : GhostState Bytes}
    (hE : E.recOf g = Record.toRecord Record.extrasM g)
    (hid : ∀ p, ownId E p = partyIdentityKey p)
    (hg : Reach (spqrOffSessionParams C) g) :
    Record.Inv E g := by
  refine ⟨hE.symm ▸ reach_inScope C hg, ?_, ?_⟩
  · rw [reach_localIdentity_eq C hg, hid]
  · rw [reach_remoteIdentity_eq C hg, hid]

theorem canonSession_of_canonRecord {gr : RecordGhost} {g : GhostState Bytes}
    (hc : Serialization.CanonRecord gr (Record.toRecord Record.extrasM g)) :
    ∃ gs, gr.cur = some gs ∧ Serialization.CanonSession gs (sessionOf g) := by
  unfold Serialization.CanonRecord Serialization.CanonCur at hc
  rw [toRecord_extrasM_eq] at hc
  cases hcur : gr.cur with
  | none => rw [hcur] at hc; cases hc
  | some gs => rw [hcur] at hc; exact ⟨gs, rfl, hc⟩

end CryptoVerification.E2E.Reach
