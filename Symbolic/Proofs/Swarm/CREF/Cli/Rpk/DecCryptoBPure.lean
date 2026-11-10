/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SR.SendSpecWPure
import ProofLib.Lemmas
import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep

/-!
# Success Inversions for Monadic Session Decrypt

Proves `.ok` inversion lemmas for `tryDecryptWithStateW`, `TripleRatchet.decryptW`,
`ensureReceiverChain`, `dhRatchetStep`, and `consumeMessageKey`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Proofs.libsignal.RngG.CliPure.DecCrypto

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal DY.Libsignal.Rust
open DY.Libsignal.HwEvents
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement
open DY.Libsignal.TripleRatchet.Refinement
open Proofs.libsignal.SR (AesW interpW)

theorem verifyMacWithAddresses_eq_true_iff
    (F : ShaCompress) (m : SignalMessage) (expected : Option (List (BitVec 8)))
    (sender receiver : IdentityKey) (macKey : BitVec 256) :
    m.verifyMacWithAddresses F expected sender receiver macKey = true ↔
      m.verifyMac F sender receiver macKey = true ∧
      CryptoGames.LibsignalAead.addressCheckPasses m.addresses expected = true := by
  simp [SignalMessage.verifyMacWithAddresses]

private theorem exec_bind' {σ α β : Type} (m : Mut σ α) (k : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= k) s =
      match Mut.exec m s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => Mut.exec (k a) s' := by
  unfold Mut.exec
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind,
    ExceptT.bindCont]
  cases m s with
  | mk res s' => cases res <;> rfl

private theorem exec_pure' {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem exec_get' {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem exec_set' {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

private theorem exec_modify' {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok ⟨⟩, f s) := rfl

private theorem exec_modifyGet' {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

private theorem exec_throw' {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem exec_liftE' {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem exec_onRatchet' {PQ α : Type} (m : Mut RatchetState α) (tr : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) tr =
      ((Mut.exec m tr.ratchet).1, { tr with ratchet := (Mut.exec m tr.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  rw [exec_bind', exec_get']
  dsimp only
  cases h : Mut.exec m tr.ratchet with
  | mk res r' =>
    change Mut.exec (do set { tr with ratchet := r' }; liftE res) tr = (res, { tr with ratchet := r' })
    rw [exec_bind', exec_set']
    dsimp only
    rw [exec_liftE']

theorem tryDecryptWithStateW_ok_inv {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W : AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState PQ} {ptext : List (BitVec 8)}
    (hok : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W spqr expected msg msgType coins) st =
      (.ok ptext, st')) :
    ∃ (remIk : IdentityKey) (tr_out : TripleRatchet PQ),
      st.remoteIdentity = some remIk ∧
      Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W spqr expected msg msgType coins)
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
  unfold Proofs.libsignal.SR.SessionState.tryDecryptWithStateW TripleRatchet.fromSessionState
    SessionState.takeRatchetState SessionState.takePqRatchetState
    TripleRatchet.applyToSessionState SessionState.clearUnacknowledgedPreKeyMessage at hok
  rw [exec_bind', exec_bind', exec_modifyGet'] at hok
  dsimp only at hok
  rw [exec_bind', exec_modifyGet'] at hok
  dsimp only at hok
  rw [exec_bind', exec_get'] at hok
  dsimp only at hok
  cases hrem : st.remoteIdentity with
  | none =>
    rw [hrem] at hok
    dsimp only at hok
    rw [exec_throw'] at hok
    cases hok
  | some remIk =>
    rw [hrem] at hok
    dsimp only at hok
    rw [exec_pure'] at hok
    dsimp only at hok
    rcases hdec :
      Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W spqr expected msg msgType coins)
        ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter,
          CryptoGames.LibsignalSession.maxForwardJumps⟩,
         st.pqRatchetState, st.localIdentity, remIk⟩ with ⟨res, tr_out⟩
    rw [hdec] at hok
    cases res with
    | error e =>
      dsimp only at hok
      rw [exec_bind', exec_liftE'] at hok
      cases hok
    | ok pt =>
      dsimp only at hok
      rw [exec_bind', exec_liftE'] at hok
      dsimp only at hok
      rw [exec_bind', exec_modify'] at hok
      dsimp only at hok
      rw [exec_pure'] at hok
      injection hok with h1 h2
      injection h1 with hpt
      subst hpt h2
      exact ⟨remIk, tr_out, rfl, hdec, rfl⟩

theorem tryDecryptWithStateW_interpW_ok_inv {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {interpretation : ExternInterpretation} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState PQ} {ptext : List (BitVec 8)}
    (hok : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C (interpW interpretation)
      spqr expected msg msgType coins) st = (.ok ptext, st')) :
    ∃ (remIk : IdentityKey) (tr_out : TripleRatchet PQ),
      st.remoteIdentity = some remIk ∧
      Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C (interpW interpretation) spqr
        expected msg msgType coins)
        ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter,
          CryptoGames.LibsignalSession.maxForwardJumps⟩,
         st.pqRatchetState, st.localIdentity, remIk⟩ = (.ok ptext, tr_out) ∧
      st' = { st with
        rootKey := tr_out.ratchet.rootKey
        previousCounter := tr_out.ratchet.previousCounter
        senderChain := tr_out.ratchet.senderChain
        receiverChains := tr_out.ratchet.receiverChains
        pqRatchetState := tr_out.pqrState
        pendingPreKey := false } :=
  tryDecryptWithStateW_ok_inv hok

theorem tripleRatchet_decryptW_ok_inv {PQ PQC : Type}
    {C : Crypto} {W : AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {tr0 tr_out : TripleRatchet PQ} {ptext : List (BitVec 8)}
    (hok : Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W spqr expected msg msgType coins) tr0 =
      (.ok ptext, tr_out)) :
    ∃ (ck : ChainKey) (r1 r2 : RatchetState) (mkGen : MessageKeyGenerator)
      (newPqrState : PQ) (pqrKey : CryptoGames.HKDF.Salt),
      Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins) tr0.ratchet = (.ok ck, r1) ∧
      Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType) r1 = (.ok mkGen, r2) ∧
      spqr.recv tr0.pqrState msg.pqRatchet = .ok (newPqrState, pqrKey) ∧
      let mks := mkGen.generateKeys C.F pqrKey
      msg.verifyMacWithAddresses C.F expected tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey = true ∧
      W.dec mks.cipherKey mks.iv msg.ciphertext = some ptext ∧
      tr_out = { tr0 with ratchet := r2, pqrState := newPqrState } := by
  unfold Proofs.libsignal.SR.TripleRatchet.decryptW at hok
  rw [exec_bind', exec_onRatchet'] at hok
  rcases hens : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins) tr0.ratchet with ⟨res1, r1⟩
  rw [hens] at hok
  cases res1 with
  | error e => cases hok
  | ok ck =>
    dsimp only at hok
    rw [exec_bind', exec_onRatchet'] at hok
    dsimp only at hok
    rcases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType) r1 with ⟨res2, r2⟩
    rw [hcmk] at hok
    cases res2 with
    | error e => cases hok
    | ok mkGen =>
      dsimp only at hok
      rw [exec_bind', exec_get'] at hok
      dsimp only at hok
      cases hpan : spqr.recvPanics tr0.pqrState msg.pqRatchet
      case true =>
        simp only [hpan, eq_self, ↓reduceIte] at hok; rw [exec_bind', exec_throw'] at hok; cases hok
      simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hok
      cases hspqr : spqr.recv tr0.pqrState msg.pqRatchet with
      | error b =>
        rw [hspqr] at hok
        cases b <;> (dsimp only at hok; rw [exec_bind', exec_throw'] at hok; cases hok)
      | ok pqrPair =>
        rcases pqrPair with ⟨newPqrState, pqrKey⟩
        rw [hspqr] at hok
        dsimp only at hok
        rw [exec_bind', exec_pure'] at hok
        dsimp only at hok
        set mks := mkGen.generateKeys C.F pqrKey
        by_cases hmac : msg.verifyMacWithAddresses C.F expected tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey = true
        · simp only [hmac, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
          cases hdec : W.dec mks.cipherKey mks.iv msg.ciphertext with
          | none =>
            rw [hdec] at hok
            dsimp only at hok
            rw [exec_throw'] at hok
            cases hok
          | some pt =>
            rw [hdec] at hok
            dsimp only at hok
            rw [exec_bind', exec_modify'] at hok
            dsimp only at hok
            rw [exec_pure'] at hok
            injection hok with h1 h2
            injection h1 with hpt
            subst hpt h2
            exact ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, rfl, hcmk, rfl, hmac, hdec, rfl⟩
        · have hmac_f : msg.verifyMacWithAddresses C.F expected tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey = false :=
            Bool.eq_false_iff.mpr hmac
          simp only [hmac_f, Bool.not_false, ↓reduceIte] at hok
          rw [exec_bind', exec_throw'] at hok
          cases hok

theorem tripleRatchet_decryptW_interpW_ok_inv {PQ PQC : Type}
    {C : Crypto} {interpretation : ExternInterpretation} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {tr0 tr_out : TripleRatchet PQ} {ptext : List (BitVec 8)}
    (hok : Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C (interpW interpretation) spqr
      expected msg msgType coins) tr0 = (.ok ptext, tr_out)) :
    ∃ (ck : ChainKey) (r1 r2 : RatchetState) (mkGen : MessageKeyGenerator)
      (newPqrState : PQ) (pqrKey : CryptoGames.HKDF.Salt),
      Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins) tr0.ratchet = (.ok ck, r1) ∧
      Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType) r1 = (.ok mkGen, r2) ∧
      spqr.recv tr0.pqrState msg.pqRatchet = .ok (newPqrState, pqrKey) ∧
      let mks := mkGen.generateKeys C.F pqrKey
      msg.verifyMacWithAddresses C.F expected tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey = true ∧
      interpretation aesCbcDecryptSymbol
        [msg.ciphertext, keyToBytes32 mks.cipherKey, CBC.blockToBytesLE mks.iv] = some ptext ∧
      tr_out = { tr0 with ratchet := r2, pqrState := newPqrState } :=
  tripleRatchet_decryptW_ok_inv hok

theorem ensureReceiverChain_ok_inv
    {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hok : Mut.exec (RatchetState.ensureReceiverChain C their coins) r0 = (.ok ck, r1)) :
    (r0.findReceiverChainKey their = .ok (some ck) ∧ r1 = r0) ∨
    (r0.findReceiverChainKey their = .ok none ∧
      Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1)) := by
  unfold RatchetState.ensureReceiverChain at hok
  rw [exec_bind', exec_get'] at hok
  dsimp only at hok
  rw [exec_bind', exec_liftE'] at hok
  cases hfind : r0.findReceiverChainKey their with
  | error e =>
    rw [hfind] at hok
    cases hok
  | ok optCk =>
    rw [hfind] at hok
    dsimp only at hok
    cases optCk with
    | none =>
      right
      exact ⟨rfl, hok⟩
    | some ck0 =>
      left
      dsimp only at hok
      rw [exec_pure'] at hok
      injection hok with h1 h2
      injection h1 with hck
      subst hck h2
      exact ⟨rfl, rfl⟩

theorem dhRatchetStep_ok_inv
    {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hok : Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1)) :
    ∃ (sc : SenderChain) (newRootKey finalRootKey : BitVec 256) (senderChainKey : ChainKey),
      r0.senderChain = some sc ∧
      rootCreateChain C r0.rootKey their sc.ratchetKey.privateKey = .ok (newRootKey, ck) ∧
      let newSenderKey := KeyPair.generate C coins
      rootCreateChain C newRootKey their newSenderKey.privateKey = .ok (finalRootKey, senderChainKey) ∧
      r1 = { r0 with
        previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
        rootKey := finalRootKey
        receiverChains := RatchetState.evictReceiverChains
          (r0.receiverChains ++ [⟨their, some ck, []⟩])
        senderChain := some ⟨newSenderKey, senderChainKey⟩ } := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey at hok
  rw [exec_bind', exec_get'] at hok
  dsimp only at hok
  cases hsc : r0.senderChain with
  | none =>
    rw [hsc] at hok
    dsimp only at hok
    rw [exec_throw'] at hok
    cases hok
  | some sc =>
    rw [hsc] at hok
    dsimp only at hok
    rw [exec_bind', exec_modifyGet'] at hok
    dsimp only at hok
    rw [exec_bind', exec_liftE'] at hok
    cases hrc1 : rootCreateChain C r0.rootKey their sc.ratchetKey.privateKey with
    | error e =>
      rw [hrc1] at hok
      cases hok
    | ok pair1 =>
      rcases pair1 with ⟨newRootKey, recvCk⟩
      rw [hrc1] at hok
      dsimp only at hok
      set newSenderKey := KeyPair.generate C coins
      rw [exec_bind', exec_liftE'] at hok
      cases hrc2 : rootCreateChain C newRootKey their newSenderKey.privateKey with
      | error e =>
        rw [hrc2] at hok
        cases hok
      | ok pair2 =>
        rcases pair2 with ⟨finalRootKey, senderCk⟩
        rw [hrc2] at hok
        dsimp only at hok
        rw [exec_bind', exec_modify'] at hok
        dsimp only at hok
        rw [exec_pure'] at hok
        injection hok with h1 h2
        injection h1 with hck
        subst hck h2
        exact ⟨sc, newRootKey, finalRootKey, senderCk, rfl, hrc1, hrc2, rfl⟩

theorem consumeMessageKey_ok_inv
    {F : CryptoGames.LibsignalSession.ShaCompress} {their : PublicKey}
    {ck : ChainKey} {counter : BitVec 32} {msgType : MessageType}
    {r1 r2 : RatchetState} {mkGen : MessageKeyGenerator}
    (hok : Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r1 = (.ok mkGen, r2)) :
    (counter < ck.index ∧
      Mut.exec (RatchetState.takeSkippedKey their counter) r1 = (.ok (some mkGen), r2)) ∨
    (¬ (counter < ck.index) ∧
      (counter - ck.index).toNat ≤ r1.maxForwardJumps ∧
      ∃ (ck_adv ck_next : ChainKey) (r_adv : RatchetState),
        Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r1 = (.ok ck_adv, r_adv) ∧
        ck_adv.nextChainKey F = .ok ck_next ∧
        Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2) ∧
        mkGen = ck_adv.messageKeys F) := by
  unfold RatchetState.consumeMessageKey at hok
  by_cases hlt : counter < ck.index
  · left
    refine ⟨hlt, ?_⟩
    simp only [hlt, ↓reduceIte] at hok
    rw [exec_bind'] at hok
    rcases htake : Mut.exec (RatchetState.takeSkippedKey their counter) r1 with ⟨res, r'⟩
    rw [htake] at hok
    cases res with
    | error e => cases hok
    | ok optKey =>
      dsimp only at hok
      cases optKey with
      | none =>
        dsimp only at hok
        rw [exec_bind', exec_throw'] at hok
        cases hok
      | some k =>
        dsimp only at hok
        rw [exec_pure'] at hok
        injection hok with h1 h2
        injection h1 with hk
        subst hk h2
        rfl
  · right
    simp only [hlt, ↓reduceIte] at hok
    rw [exec_bind', exec_get'] at hok
    dsimp only at hok
    by_cases hjump : r1.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hjump, ↓reduceIte] at hok
      rw [exec_bind', exec_throw'] at hok
      cases hok
    · simp only [hjump, ↓reduceIte] at hok
      refine ⟨hlt, Nat.not_lt.mp hjump, ?_⟩
      rw [exec_bind'] at hok
      rcases hadv : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r1 with ⟨res_adv, r_adv⟩
      rw [hadv] at hok
      cases res_adv with
      | error e => cases hok
      | ok ck_adv =>
        dsimp only at hok
        rw [exec_bind', exec_liftE'] at hok
        cases hnext : ck_adv.nextChainKey F with
        | error e =>
          rw [hnext] at hok
          cases hok
        | ok ck_next =>
          rw [hnext] at hok
          dsimp only at hok
          rw [exec_bind'] at hok
          rcases hset : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv with ⟨res_set, r_set⟩
          rw [hset] at hok
          cases res_set with
          | error e => cases hok
          | ok u =>
            cases u
            dsimp only at hok
            rw [exec_pure'] at hok
            injection hok with h1 h2
            injection h1 with hmk
            subst h2
            exact ⟨ck_adv, ck_next, r_adv, rfl, hnext, hset, hmk.symm⟩

theorem rootCreateChain_ok_index_eq_zero
    {C : Crypto} {rk newRk : BitVec 256} {their : PublicKey} {our : PrivateKey} {ck : ChainKey}
    (h : rootCreateChain C rk their our = .ok (newRk, ck)) :
    ck.index = 0 := by
  unfold rootCreateChain CryptoGames.Ratchet.createChain at h
  split at h
  · cases h
  · injection h with h1
    injection h1 with _ hck
    rw [← hck]

theorem dhRatchetStep_ok_index_eq_zero
    {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hok : Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1)) :
    ck.index = 0 := by
  obtain ⟨_sc, _newRootKey, _, _, _, hrc1, _, _⟩ := dhRatchetStep_ok_inv hok
  exact rootCreateChain_ok_index_eq_zero hrc1

end Proofs.libsignal.RngG.CliPure.DecCrypto
