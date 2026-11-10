/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.SR.RecvSpecWPure
public import Symbolic.Proofs.SpecLemmas.CliPureBytes
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Session-Level Receiver-Chain Inclusion for Whisper Decrypt

Proves receiver-chain key inclusion across `SessionState.tryDecryptFromRecordW` and the
stored-session case split across `messageDecryptSignalW`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPureRcv

section RatchetAndEval

cref_open
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin (storedSession inMemAnswers)
open Proofs.libsignal.RngG.R3
open Proofs.libsignal.SR

@[local simp] theorem exec_pure_hw {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

@[local simp] theorem exec_get_hw {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] theorem exec_set_hw {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

@[local simp] theorem exec_liftE_hw {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

@[local simp] theorem exec_bind_hw {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
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

theorem mem_set_cases_hw {α : Type} {l : List α} {i : Nat} {x y : α}
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

theorem mem_of_getElem?_hw {α : Type} {l : List α} {i : Nat} {x : α}
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

theorem takeSkippedKey_senderRatchetKey_mem (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) {rc' : ReceiverChain}
    (hrc' : rc' ∈ (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains) :
    ∃ rc₀ ∈ r.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey := by
  unfold RatchetState.takeSkippedKey at hrc'
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp only [h1, exec_bind_hw, exec_get_hw, exec_pure_hw] at hrc'
    exact ⟨rc', hrc', rfl⟩
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp only [h1, h2, exec_bind_hw, exec_get_hw] at hrc'
      exact ⟨rc', hrc', rfl⟩
    · rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp only [h1, h2, h3, exec_bind_hw, exec_get_hw, exec_pure_hw] at hrc'
        exact ⟨rc', hrc', rfl⟩
      · rcases h4 : c.messageKeys[pos]? with _ | key
        · simp only [h1, h2, h3, h4, exec_bind_hw, exec_get_hw] at hrc'
          exact ⟨rc', hrc', rfl⟩
        · simp only [h1, h2, h3, h4, exec_bind_hw, exec_get_hw, exec_set_hw, exec_pure_hw] at hrc'
          rcases mem_set_cases_hw hrc' with rfl | hmem
          · exact ⟨c, mem_of_getElem?_hw h2, rfl⟩
          · exact ⟨rc', hmem, rfl⟩

theorem storeSkippedKey_senderRatchetKey_mem (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) {rc' : ReceiverChain}
    (hrc' : rc' ∈ (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains) :
    ∃ rc₀ ∈ r.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey := by
  unfold RatchetState.storeSkippedKey at hrc'
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp only [h1, exec_bind_hw, exec_get_hw] at hrc'
    exact ⟨rc', hrc', rfl⟩
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp only [h1, h2, exec_bind_hw, exec_get_hw] at hrc'
      exact ⟨rc', hrc', rfl⟩
    · simp only [h1, h2, exec_bind_hw, exec_get_hw, exec_set_hw] at hrc'
      rcases mem_set_cases_hw hrc' with rfl | hmem
      · exact ⟨c, mem_of_getElem?_hw h2, rfl⟩
      · exact ⟨rc', hmem, rfl⟩

theorem setReceiverChainKey_senderRatchetKey_mem (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) {rc' : ReceiverChain}
    (hrc' : rc' ∈ (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains) :
    ∃ rc₀ ∈ r.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey := by
  unfold RatchetState.setReceiverChainKey at hrc'
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp only [h1, exec_bind_hw, exec_get_hw] at hrc'
    exact ⟨rc', hrc', rfl⟩
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp only [h1, h2, exec_bind_hw, exec_get_hw] at hrc'
      exact ⟨rc', hrc', rfl⟩
    · simp only [h1, h2, exec_bind_hw, exec_get_hw, exec_set_hw] at hrc'
      rcases mem_set_cases_hw hrc' with rfl | hmem
      · exact ⟨c, mem_of_getElem?_hw h2, rfl⟩
      · exact ⟨rc', hmem, rfl⟩

theorem advanceChain_senderRatchetKey_mem (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : Nat) (ck : ChainKey) (r : RatchetState) {rc' : ReceiverChain}
    (hrc' : rc' ∈ (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains) :
    ∃ rc₀ ∈ r.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey := by
  induction fuel generalizing ck r with
  | zero => exact ⟨rc', hrc', rfl⟩
  | succ fuel ih =>
    unfold RatchetState.advanceChain at hrc'
    split at hrc'
    · rw [exec_bind_hw] at hrc'
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨e | _, r1⟩
      · rw [hs] at hrc'
        have h1 : rc' ∈ (Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r).2.receiverChains := by
          rw [hs]; exact hrc'
        exact storeSkippedKey_senderRatchetKey_mem their (ck.messageKeys F) r h1
      · rw [hs] at hrc'
        simp only [exec_bind_hw, exec_liftE_hw] at hrc'
        have h_r1 : ∀ rc1 ∈ r1.receiverChains,
            ∃ rc₀ ∈ r.receiverChains, rc1.senderRatchetKey = rc₀.senderRatchetKey := by
          intro rc1 hrc1
          have h1 : rc1 ∈ (Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r).2.receiverChains := by
            rw [hs]; exact hrc1
          exact storeSkippedKey_senderRatchetKey_mem their (ck.messageKeys F) r h1
        rcases hn : ck.nextChainKey F with _ | ck'
        · rw [hn] at hrc'
          exact h_r1 rc' hrc'
        · rw [hn] at hrc'
          obtain ⟨rc1, hrc1, heq1⟩ := ih ck' r1 hrc'
          obtain ⟨rc₀, hrc₀, heq0⟩ := h_r1 rc1 hrc1
          exact ⟨rc₀, hrc₀, heq1.trans heq0⟩
    · exact ⟨rc', hrc', rfl⟩

theorem dhRatchetStep_senderRatchetKey_mem {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hDh : Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1))
    {rc' : ReceiverChain} (hrc' : rc' ∈ r1.receiverChains) :
    (∃ rc₀ ∈ r0.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey) ∨
      rc'.senderRatchetKey = their := by
  obtain ⟨sc, newRootKey, finalRootKey, senderChainKey, _hsc, _hrc1, _hrc2, hr1⟩ :=
    Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
  rw [hr1] at hrc'
  dsimp only [RatchetState.evictReceiverChains] at hrc'
  have hmem := List.mem_of_mem_drop hrc'
  rcases List.mem_append.mp hmem with hold | hnew
  · exact Or.inl ⟨rc', hold, rfl⟩
  · simp only [List.mem_singleton] at hnew
    subst hnew
    exact Or.inr rfl

/-- Across a successful `SessionState.tryDecryptFromRecordW`, either every receiver chain in `st'`
shares its `senderRatchetKey` with a chain in `st.receiverChains`, or `RatchetState.dhRatchetStep`
succeeds on `msg.senderRatchetKey` and every chain key in `st'` comes from `st.receiverChains` or
equals `msg.senderRatchetKey`. -/
theorem tryDecryptFromRecordW_receiverChains_cases {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W : AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState PQ} {pt : List (BitVec 8)}
    (hok : SessionState.tryDecryptFromRecordW C W spqr expected msg msgType coins st =
      (.ok pt, st')) :
    (∀ rc' ∈ st'.receiverChains,
      ∃ rc₀ ∈ st.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey) ∨
    (∃ (ck : ChainKey) (r1 : RatchetState),
      Mut.exec (RatchetState.dhRatchetStep C msg.senderRatchetKey coins) (ratchetStateOf st) =
        (.ok ck, r1) ∧
      ∀ rc' ∈ st'.receiverChains,
        (∃ rc₀ ∈ st.receiverChains, rc'.senderRatchetKey = rc₀.senderRatchetKey) ∨
          rc'.senderRatchetKey = msg.senderRatchetKey) := by
  obtain ⟨remIk, r2, mkGen, newPqrState, pqrKey, _, _, _, _, hst', hBr⟩ :=
    decryptW_ok_branch hok
  have hrc_st' : st'.receiverChains = r2.receiverChains := by rw [hst']
  have hrc_r0 : (ratchetStateOf st).receiverChains = st.receiverChains := rfl
  rcases hBr with
    ⟨ck, _, _, hTake, _⟩ |
    ⟨ck, ck_adv, ck_next, r_adv, _, _, _, hAdv, _, hSet, _, _⟩ |
    ⟨ck, ck_adv, ck_next, r1, r_adv, _, hDh, _, _, hAdv, _, hSet, _, _⟩
  · left
    intro rc' hrc'
    rw [hrc_st'] at hrc'
    have hmem : rc' ∈ (Mut.exec (RatchetState.takeSkippedKey msg.senderRatchetKey msg.counter)
        (ratchetStateOf st)).2.receiverChains := by
      rw [hTake]; exact hrc'
    simpa [hrc_r0] using
      takeSkippedKey_senderRatchetKey_mem msg.senderRatchetKey msg.counter (ratchetStateOf st) hmem
  · left
    intro rc' hrc'
    rw [hrc_st'] at hrc'
    have hmemSet : rc' ∈ (Mut.exec (RatchetState.setReceiverChainKey msg.senderRatchetKey ck_next)
        r_adv).2.receiverChains := by
      rw [hSet]; exact hrc'
    obtain ⟨rc₁, hrc₁, heq₁⟩ :=
      setReceiverChainKey_senderRatchetKey_mem msg.senderRatchetKey ck_next r_adv hmemSet
    have hmemAdv : rc₁ ∈ (Mut.exec (RatchetState.advanceChain C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck) (ratchetStateOf st)).2.receiverChains := by
      rw [hAdv]; exact hrc₁
    obtain ⟨rc₀, hrc₀, heq₀⟩ :=
      advanceChain_senderRatchetKey_mem C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck (ratchetStateOf st) hmemAdv
    exact ⟨rc₀, by simpa [hrc_r0] using hrc₀, heq₁.trans heq₀⟩
  · right
    refine ⟨ck, r1, hDh, fun rc' hrc' => ?_⟩
    rw [hrc_st'] at hrc'
    have hmemSet : rc' ∈ (Mut.exec (RatchetState.setReceiverChainKey msg.senderRatchetKey ck_next)
        r_adv).2.receiverChains := by
      rw [hSet]; exact hrc'
    obtain ⟨rc₂, hrc₂, heq₂⟩ :=
      setReceiverChainKey_senderRatchetKey_mem msg.senderRatchetKey ck_next r_adv hmemSet
    have hmemAdv : rc₂ ∈ (Mut.exec (RatchetState.advanceChain C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck) r1).2.receiverChains := by
      rw [hAdv]; exact hrc₂
    obtain ⟨rc₁, hrc₁, heq₁⟩ :=
      advanceChain_senderRatchetKey_mem C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck r1 hmemAdv
    rcases dhRatchetStep_senderRatchetKey_mem hDh hrc₁ with ⟨rc₀, hrc₀, heq₀⟩ | hnew
    · exact Or.inl ⟨rc₀, by simpa [hrc_r0] using hrc₀, (heq₂.trans heq₁).trans heq₀⟩
    · exact Or.inr ((heq₂.trans heq₁).trans hnew)

def decryptFlatW_hw {Addr PQ PQC E : Type} [Inhabited PQ] (C : Crypto) (W : AesW)
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

local macro "api_simp_hw" " [" xs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp [Api.run, storeCall, liftProtocol, modify, modifyGet,
      MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure,
      StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, Id.run, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, $xs,*] $(loc)?)

theorem messageDecryptSignalW_eq_flatW_hw {Addr PQ PQC E : Type} [Inhabited PQ] (C : Crypto)
    (W : AesW) (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remote loc : Addr)
    (coins : BitVec 256) :
    messageDecryptSignalW C W spqr ser answers ciphertext remote loc coins =
      decryptFlatW_hw C W spqr ser answers ciphertext remote loc coins := by
  rcases answers with ⟨l, t, s, st⟩
  simp only [messageDecryptSignalW, decryptFlatW_hw]
  rcases l with el | _ | record
  · api_simp_hw []
  · api_simp_hw []
  · rcases hd : Proofs.libsignal.SR.SessionRecord.tryDecryptFromRecordW C W spqr (ser remote loc)
        ciphertext coins record with ed | ⟨ptext, record'⟩
    · api_simp_hw [hd]
    · rcases record' with ⟨_ | session⟩
      · api_simp_hw [hd]
      · rcases hk : session.state.remoteIdentity with _ | k
        · api_simp_hw [hd, hk]
        · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
            api_simp_hw [hd, hk]

theorem storedSession_decryptW_cases_hw {Addr Key : Type} (C : Crypto) (W : AesW)
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
  rw [messageDecryptSignalW_eq_flatW_hw]
  unfold decryptFlatW_hw inMemAnswers
  dsimp only
  unfold Proofs.libsignal.SR.SessionRecord.tryDecryptFromRecordW
  dsimp only
  rcases htr : SessionState.tryDecryptFromRecordW C W spqr (ser remote loc) msg .whisper coins
      sess.state with ⟨ed | pt', st'⟩
  · left; simp [storedSession]
  · cases hk : st'.remoteIdentity <;> simp [hk, storedSession]

end RatchetAndEval
end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
