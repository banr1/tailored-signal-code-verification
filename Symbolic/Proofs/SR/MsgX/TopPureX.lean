/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SR.RecvSpecWPure
public import Symbolic.Proofs.SpecLemmas.CliPureBytes
import ProofLib.Lemmas
import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Refinement.RngFree.SendSpecPure -- shake: keep
public import Symbolic.Proofs.RngG.R3Canon -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# Flattened W-model `messageDecryptSignalW` and stored-session characterization

Proves skipped-message-key count preservation (`msgKeysLe_of_tryDecryptFromRecordW`), equivalence
between `messageDecryptSignalW` and the flattened `decryptFlatW` (`messageDecryptSignalW_eq_flatW`),
and the two-case characterization of the resulting in-memory session
(`storedSession_decryptW_cases`).
-/

set_option linter.unusedVariables false

namespace Proofs.libsignal.SR.MsgX.TopPure

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open Symbolic.Proofs.SpecLemmas.CliPureBytes
  (exec_pure exec_throw exec_get exec_set exec_modify exec_modifyGet exec_liftE
   exec_bind exec_map exec_onRatchet)
open Proofs.libsignal.SR (AesW messageDecryptSignalW)

attribute [local simp] exec_pure exec_throw exec_get exec_set exec_modify exec_modifyGet
  exec_bind exec_map exec_onRatchet

/-! ## Skipped-key count bound -/

private abbrev MsgKeysLeX (r : RatchetState) : Prop :=
  ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys

private theorem mem_set_casesX {α : Type} {l : List α} {i : ℕ} {x y : α}
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

private theorem mem_of_getElem?X {α : Type} {l : List α} {i : ℕ} {x : α}
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

private theorem length_eraseIdx_leX {α : Type} (l : List α) (i : ℕ) :
    (l.eraseIdx i).length ≤ l.length := by
  induction l generalizing i with
  | nil => simp [List.eraseIdx]
  | cons a l ih =>
    cases i with
    | zero => simp [List.eraseIdx]
    | succ i =>
      simp only [List.eraseIdx, List.length_cons]
      exact Nat.succ_le_succ (ih i)

private theorem takeSkippedKey_msgKeysLeX (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) (h : MsgKeysLeX r) :
    MsgKeysLeX (Mut.exec (RatchetState.takeSkippedKey their counter) r).2 := by
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
          intro c' hc'
          rcases mem_set_casesX hc' with rfl | hc'
          · exact (length_eraseIdx_leX c.messageKeys pos).trans (h c (mem_of_getElem?X h2))
          · exact h c' hc'

private theorem storeSkippedKey_msgKeysLeX (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) (h : MsgKeysLeX r) :
    MsgKeysLeX (Mut.exec (RatchetState.storeSkippedKey their key) r).2 := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simpa [h1] using h
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simpa [h1, h2] using h
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      intro c' hc'
      rcases mem_set_casesX hc' with rfl | hc'
      · have hc_len := h c (mem_of_getElem?X h2)
        dsimp only
        split_ifs with hlt
        · simp only [List.length_dropLast, List.length_cons]
          omega
        · simp only [List.length_cons] at hlt ⊢
          omega
      · exact h c' hc'

private theorem setReceiverChainKey_msgKeysLeX (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) (h : MsgKeysLeX r) :
    MsgKeysLeX (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2 := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simpa [h1] using h
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simpa [h1, h2] using h
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      intro c' hc'
      rcases mem_set_casesX hc' with rfl | hc'
      · exact h c (mem_of_getElem?X h2)
      · exact h c' hc'

private theorem advanceChain_msgKeysLeX (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : ℕ) (ck : ChainKey) (r : RatchetState) (h : MsgKeysLeX r) :
    MsgKeysLeX (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2 := by
  induction fuel generalizing ck r with
  | zero => exact h
  | succ fuel ih =>
    unfold RatchetState.advanceChain
    split
    · rw [exec_bind]
      have h1 := storeSkippedKey_msgKeysLeX their (ck.messageKeys F) r h
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

private theorem consumeMessageKey_msgKeysLeX (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType) (r : RatchetState)
    (h : MsgKeysLeX r) :
    MsgKeysLeX (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2 := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    have h1 := takeSkippedKey_msgKeysLeX their counter r h
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨e | opt, r1⟩
    · rw [ht] at h1
      exact h1
    · rw [ht] at h1
      cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    split
    · simpa using h
    · rw [exec_bind]
      have h1 := advanceChain_msgKeysLeX F their counter (counter - ck.index).toNat ck r h
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨e | ck1, r1⟩
      · rw [ha] at h1
        exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_msgKeysLeX their ck2 r1 h1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨e | _, r2⟩ <;>
            · rw [hs] at h2
              exact h2

private theorem dhRatchetStep_msgKeysLeX (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : MsgKeysLeX r) :
    MsgKeysLeX (Mut.exec (RatchetState.dhRatchetStep C their coins) r).2 := by
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
      · intro c hc
        unfold RatchetState.evictReceiverChains at hc
        have hc' := List.mem_of_mem_drop hc
        rcases List.mem_append.mp hc' with hc0 | hc0
        · exact h c hc0
        · simp only [List.mem_singleton] at hc0
          subst hc0
          simp

private theorem ensureReceiverChain_msgKeysLeX (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r : RatchetState) (h : MsgKeysLeX r) :
    MsgKeysLeX (Mut.exec (RatchetState.ensureReceiverChain C their coins) r).2 := by
  unfold RatchetState.ensureReceiverChain
  simp only [exec_bind, exec_get, exec_liftE]
  rcases hf : r.findReceiverChainKey their with _ | (_ | ck)
  · exact h
  · exact dhRatchetStep_msgKeysLeX C their coins r h
  · simpa using h

/-- A successful W record decrypt keeps every receiver chain's skipped keys within
`maxMessageKeys`. -/
theorem msgKeysLe_of_tryDecryptFromRecordW {PQC : Type} {C : Crypto} {W : AesW}
    {spqr : Spqr (List (BitVec 8)) PQC} {expected : Option (List (BitVec 8))}
    {msg : SignalMessage} {msgType : MessageType} {coins : BitVec 256}
    {st st' : SessionState (List (BitVec 8))} {pt : List (BitVec 8)}
    (hMk : ∀ c ∈ st.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (hok : SessionState.tryDecryptFromRecordW C W spqr expected msg msgType coins st =
      (.ok pt, st')) :
    ∀ c ∈ st'.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
  obtain ⟨-, hd⟩ := Proofs.libsignal.RngG.R3.tryDecryptFromRecordW_ok_inv hok
  obtain ⟨remIk, tr_out, -, hTr, hSt'⟩ := Proofs.libsignal.RngG.R3.tryDecryptWithStateW_ok_inv hd
  obtain ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, hens, hcmk, -, -, -, hTrOut⟩ :=
    Proofs.libsignal.RngG.R3.tripleRatchet_decryptW_ok_inv hTr
  subst hSt' hTrOut
  have h1 := ensureReceiverChain_msgKeysLeX C msg.senderRatchetKey coins
    ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter,
      CryptoGames.LibsignalSession.maxForwardJumps⟩ hMk
  rw [hens] at h1
  have h2 := consumeMessageKey_msgKeysLeX C.F msg.senderRatchetKey ck msg.counter msgType r1 h1
  rw [hcmk] at h2
  exact h2

/-! ## Flattened decrypt model -/

/-- Explicit pattern-matching form of `messageDecryptSignalW`. -/
def decryptFlatW {Addr PQ PQC E : Type} [Inhabited PQ] (C : Crypto) (W : AesW)
    (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remote loc : Addr)
    (coins : BitVec 256) :
    Except (ApiError Addr E) (List (BitVec 8)) × List (StoreCall Addr PQ) :=
  let load := StoreCall.loadSession remote
  match answers.loadSession with
  | .error e => (.error (.store e), [load])
  | .ok none => (.error (.sessionNotFound remote "message_decrypt_signal"), [load])
  | .ok (some record) =>
    match Proofs.libsignal.SR.SessionRecord.tryDecryptFromRecordW C W spqr (ser remote loc)
        ciphertext coins record with
    | .error e => (.error (ApiError.ofProtocol e), [load])
    | .ok (ptext, record') =>
      match record'.currentSession.bind (·.state.remoteIdentity) with
      | none => (.error .panic, [load])
      | some k =>
        let trust := StoreCall.isTrustedIdentity remote k .receiving
        match answers.isTrustedIdentity with
        | .error e => (.error (.store e), [load, trust])
        | .ok false => (.error (.untrustedIdentity remote), [load, trust])
        | .ok true =>
          let save := StoreCall.saveIdentity remote k
          match answers.saveIdentity with
          | .error e => (.error (.store e), [load, trust, save])
          | .ok _ =>
            let store := StoreCall.storeSession remote record'
            match answers.storeSession with
            | .error e => (.error (.store e), [load, trust, save, store])
            | .ok () => (.ok ptext, [load, trust, save, store])

local macro "api_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp [Api.run, storeCall, liftProtocol, modify, modifyGet,
      MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure,
      StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, Id.run, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, $xs,*] $(loc)?)

theorem messageDecryptSignalW_eq_flatW {Addr PQ PQC E : Type} [Inhabited PQ] (C : Crypto)
    (W : AesW) (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remote loc : Addr)
    (coins : BitVec 256) :
    messageDecryptSignalW C W spqr ser answers ciphertext remote loc coins =
      decryptFlatW C W spqr ser answers ciphertext remote loc coins := by
  rcases answers with ⟨l, t, s, st⟩
  simp only [messageDecryptSignalW, decryptFlatW]
  rcases l with el | _ | record
  · api_simp []
  · api_simp []
  · rcases hd : Proofs.libsignal.SR.SessionRecord.tryDecryptFromRecordW C W spqr (ser remote loc)
        ciphertext coins record with ed | ⟨ptext, record'⟩
    · api_simp [hd]
    · rcases record' with ⟨_ | session⟩
      · api_simp [hd]
      · rcases hk : session.state.remoteIdentity with _ | k
        · api_simp [hd, hk]
        · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
            api_simp [hd, hk]

section InMem

variable {C : Crypto} {W : AesW} {S : SpqrModel}
  {sess : Session (List (BitVec 8))} {answers : StoreAnswers (List (BitVec 8)) Unit}
  {ser : AddrVal → AddrVal → Option (List (BitVec 8))}
  {msg : SignalMessage} {remote loc : AddrVal} {coins : BitVec 256}

end InMem

/-! ## Stored-session cases -/

/-- The session stored by `messageDecryptSignalW` on `inMemAnswers sess` is either unchanged or
updated with the decrypted `SessionState` and cleared pending pre-key fields. -/
theorem storedSession_decryptW_cases {Addr Key : Type} (C : Crypto) (W : AesW)
    (spqr : Spqr (List (BitVec 8)) Key) (ser : Addr → Addr → Option (List (BitVec 8)))
    (msg : SignalMessage) (remote loc : Addr) (coins : BitVec 256)
    (sess : Session (List (BitVec 8))) :
    storedSession sess
        (messageDecryptSignalW C W spqr ser (inMemAnswers sess) msg remote loc coins).2 = sess ∨
      ∃ pt st', SessionState.tryDecryptFromRecordW C W spqr (ser remote loc) msg .whisper coins
          sess.state = (.ok pt, st') ∧
        storedSession sess
            (messageDecryptSignalW C W spqr ser (inMemAnswers sess) msg remote loc coins).2 =
          { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none } := by
  rw [messageDecryptSignalW_eq_flatW]
  unfold decryptFlatW inMemAnswers
  dsimp only
  unfold Proofs.libsignal.SR.SessionRecord.tryDecryptFromRecordW
  dsimp only
  rcases htr : SessionState.tryDecryptFromRecordW C W spqr (ser remote loc) msg .whisper coins
      sess.state with ⟨ed | pt', st'⟩
  · left; simp [storedSession]
  · cases hk : st'.remoteIdentity <;> simp [hk, storedSession]

end Proofs.libsignal.SR.MsgX.TopPure
