/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SR.ModelW

/-!
# Inversion of `SessionState.tryDecryptFromRecordW` into three ratchet branches

Inverts a successful whole-message AES session decryption (`tryDecryptFromRecordW`) into version,
remote-identity, SPQR, MAC, and AES-decrypt conditions together with the exclusive ratchet branch
(`DecryptOkBranch`: cached skipped key, existing receiver chain, or DH ratchet step) via
`decryptW_ok_branch`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.RngG.R3

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Proofs.libsignal.SR

/-! ## `Mut.exec` lemmas -/

private theorem exec_bind {σ α β : Type} (m : Mut σ α) (k : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= k) s =
      match Mut.exec m s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => Mut.exec (k a) s' := by
  unfold Mut.exec
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind,
    ExceptT.bindCont]
  cases m s with
  | mk res s' => cases res <;> rfl

private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

private theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok ⟨⟩, f s) := rfl

private theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem exec_onRatchet {PQ α : Type} (m : Mut RatchetState α) (tr : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) tr =
      ((Mut.exec m tr.ratchet).1, { tr with ratchet := (Mut.exec m tr.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  rw [exec_bind, exec_get]
  dsimp only
  cases h : Mut.exec m tr.ratchet with
  | mk res r' =>
    change Mut.exec (do set { tr with ratchet := r' }; liftE res) tr = (res, { tr with ratchet := r' })
    rw [exec_bind, exec_set]
    dsimp only
    rw [exec_liftE]

/-! ## Session-level inversions -/

theorem tryDecryptFromRecordW_ok_inv {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W : AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState PQ} {ptext : List (BitVec 8)}
    (hok : SessionState.tryDecryptFromRecordW C W spqr expected msg msgType coins st =
      (.ok ptext, st')) :
    st.version.toNat = msg.messageVersion.toNat ∧
    Mut.exec (SessionState.tryDecryptWithStateW C W spqr expected msg msgType coins) st =
      (.ok ptext, st') := by
  unfold SessionState.tryDecryptFromRecordW at hok
  split at hok
  · cases hok
  · rename_i hver
    rw [Classical.not_not] at hver
    refine ⟨hver, ?_⟩
    rcases hexec : Mut.exec (SessionState.tryDecryptWithStateW C W spqr expected msg msgType coins)
      st with ⟨res, u⟩
    rw [hexec] at hok
    cases res with
    | error e => cases hok
    | ok pt =>
      injection hok with h1 h2
      injection h1 with hpt
      subst hpt h2
      rfl

theorem tryDecryptWithStateW_ok_inv {PQ PQC : Type} [Inhabited PQ]
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

theorem tripleRatchet_decryptW_ok_inv {PQ PQC : Type}
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
      msg.verifyMacWithAddresses C.F expected tr0.remoteIdentityKey tr0.localIdentityKey
        (mkGen.generateKeys C.F pqrKey).macKey = true ∧
      W.dec (mkGen.generateKeys C.F pqrKey).cipherKey (mkGen.generateKeys C.F pqrKey).iv
        msg.ciphertext = some ptext ∧
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
            exact ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, rfl, hcmk, rfl, hmac, hdec, rfl⟩
        · have hmac_f : msg.verifyMacWithAddresses C.F expected tr0.remoteIdentityKey
              tr0.localIdentityKey (mkGen.generateKeys C.F pqrKey).macKey = false :=
            Bool.eq_false_iff.mpr hmac
          simp only [hmac_f, Bool.not_false, ↓reduceIte] at hok
          rw [exec_bind, exec_throw] at hok
          cases hok

/-! ## Ratchet-level inversions -/

theorem ensureReceiverChain_ok_inv
    {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hok : Mut.exec (RatchetState.ensureReceiverChain C their coins) r0 = (.ok ck, r1)) :
    (r0.findReceiverChainKey their = .ok (some ck) ∧ r1 = r0) ∨
    (r0.findReceiverChainKey their = .ok none ∧
      Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1)) := by
  unfold RatchetState.ensureReceiverChain at hok
  rw [exec_bind, exec_get] at hok
  dsimp only at hok
  rw [exec_bind, exec_liftE] at hok
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
      rw [exec_pure] at hok
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
      rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey =
        .ok (finalRootKey, senderChainKey) ∧
      r1 = { r0 with
        previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
        rootKey := finalRootKey
        receiverChains := RatchetState.evictReceiverChains
          (r0.receiverChains ++ [⟨their, some ck, []⟩])
        senderChain := some ⟨KeyPair.generate C coins, senderChainKey⟩ } := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey at hok
  rw [exec_bind, exec_get] at hok
  dsimp only at hok
  cases hsc : r0.senderChain with
  | none =>
    rw [hsc] at hok
    dsimp only at hok
    rw [exec_throw] at hok
    cases hok
  | some sc =>
    rw [hsc] at hok
    dsimp only at hok
    rw [exec_bind, exec_modifyGet] at hok
    dsimp only at hok
    rw [exec_bind, exec_liftE] at hok
    cases hrc1 : rootCreateChain C r0.rootKey their sc.ratchetKey.privateKey with
    | error e =>
      rw [hrc1] at hok
      cases hok
    | ok pair1 =>
      rcases pair1 with ⟨newRootKey, recvCk⟩
      rw [hrc1] at hok
      dsimp only at hok
      rw [exec_bind, exec_liftE] at hok
      cases hrc2 : rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey with
      | error e =>
        rw [hrc2] at hok
        cases hok
      | ok pair2 =>
        rcases pair2 with ⟨finalRootKey, senderCk⟩
        rw [hrc2] at hok
        dsimp only at hok
        rw [exec_bind, exec_modify] at hok
        dsimp only at hok
        rw [exec_pure] at hok
        injection hok with h1 h2
        injection h1 with hck
        subst hck h2
        exact ⟨sc, newRootKey, finalRootKey, senderCk, rfl, hrc1, hrc2, rfl⟩

theorem consumeMessageKey_ok_inv
    {F : CryptoGames.LibsignalSession.ShaCompress} {their : PublicKey}
    {ck : ChainKey} {counter : BitVec 32} {msgType : MessageType}
    {r1 r2 : RatchetState} {mkGen : MessageKeyGenerator}
    (hok : Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r1 =
      (.ok mkGen, r2)) :
    (counter < ck.index ∧
      Mut.exec (RatchetState.takeSkippedKey their counter) r1 = (.ok (some mkGen), r2)) ∨
    (¬ (counter < ck.index) ∧
      (counter - ck.index).toNat ≤ r1.maxForwardJumps ∧
      ∃ (ck_adv ck_next : ChainKey) (r_adv : RatchetState),
        Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r1 =
          (.ok ck_adv, r_adv) ∧
        ck_adv.nextChainKey F = .ok ck_next ∧
        Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2) ∧
        mkGen = ck_adv.messageKeys F) := by
  unfold RatchetState.consumeMessageKey at hok
  by_cases hlt : counter < ck.index
  · left
    refine ⟨hlt, ?_⟩
    simp only [hlt, ↓reduceIte] at hok
    rw [exec_bind] at hok
    rcases htake : Mut.exec (RatchetState.takeSkippedKey their counter) r1 with ⟨res, r'⟩
    rw [htake] at hok
    cases res with
    | error e => cases hok
    | ok optKey =>
      dsimp only at hok
      cases optKey with
      | none =>
        dsimp only at hok
        rw [exec_bind, exec_throw] at hok
        cases hok
      | some k =>
        dsimp only at hok
        rw [exec_pure] at hok
        injection hok with h1 h2
        injection h1 with hk
        subst hk h2
        rfl
  · right
    simp only [hlt, ↓reduceIte] at hok
    rw [exec_bind, exec_get] at hok
    dsimp only at hok
    by_cases hjump : r1.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hjump, ↓reduceIte] at hok
      rw [exec_bind, exec_throw] at hok
      cases hok
    · simp only [hjump, ↓reduceIte] at hok
      refine ⟨hlt, Nat.not_lt.mp hjump, ?_⟩
      rw [exec_bind] at hok
      rcases hadv : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat
        ck) r1 with ⟨res_adv, r_adv⟩
      rw [hadv] at hok
      cases res_adv with
      | error e => cases hok
      | ok ck_adv =>
        dsimp only at hok
        rw [exec_bind, exec_liftE] at hok
        cases hnext : ck_adv.nextChainKey F with
        | error e =>
          rw [hnext] at hok
          cases hok
        | ok ck_next =>
          rw [hnext] at hok
          dsimp only at hok
          rw [exec_bind] at hok
          rcases hset : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv with
            ⟨res_set, r_set⟩
          rw [hset] at hok
          cases res_set with
          | error e => cases hok
          | ok u =>
            cases u
            dsimp only at hok
            rw [exec_pure] at hok
            injection hok with h1 h2
            injection h1 with hmk
            subst h2
            exact ⟨ck_adv, ck_next, r_adv, rfl, hnext, hset, hmk.symm⟩

/-! ## Three-branch decomposition -/

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

def ratchetStateOf {PQ : Type} (st : SessionState PQ) : RatchetState :=
  ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter,
    CryptoGames.LibsignalSession.maxForwardJumps⟩

/-- Exclusive ratchet branches of `ensureReceiverChain` followed by `consumeMessageKey` on a
successful decrypt: cached skipped key, existing receiver chain, or DH ratchet step. -/
inductive DecryptOkBranch
    (C : Crypto) (r0 : RatchetState) (remIk locIk : IdentityKey)
    (expected : Option (List (BitVec 8))) (msg : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (pqrKey : CryptoGames.HKDF.Salt)
    (r2 : RatchetState) (mkGen : MessageKeyGenerator) : Prop where
  | skipped (ck : ChainKey) :
      r0.findReceiverChainKey msg.senderRatchetKey = .ok (some ck) →
      msg.counter < ck.index →
      Mut.exec (RatchetState.takeSkippedKey msg.senderRatchetKey msg.counter) r0 =
        (.ok (some mkGen), r2) →
      msg.verifyMacWithAddresses C.F expected remIk locIk (mkGen.generateKeys C.F pqrKey).macKey =
        true →
      DecryptOkBranch C r0 remIk locIk expected msg msgType coins pqrKey r2 mkGen
  | existing (ck ck_adv ck_next : ChainKey) (r_adv : RatchetState) :
      r0.findReceiverChainKey msg.senderRatchetKey = .ok (some ck) →
      ¬ (msg.counter < ck.index) →
      (msg.counter - ck.index).toNat ≤ r0.maxForwardJumps →
      Mut.exec (RatchetState.advanceChain C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck) r0 = (.ok ck_adv, r_adv) →
      ck_adv.nextChainKey C.F = .ok ck_next →
      Mut.exec (RatchetState.setReceiverChainKey msg.senderRatchetKey ck_next) r_adv =
        (.ok (), r2) →
      mkGen = ck_adv.messageKeys C.F →
      msg.verifyMacWithAddresses C.F expected remIk locIk (mkGen.generateKeys C.F pqrKey).macKey =
        true →
      DecryptOkBranch C r0 remIk locIk expected msg msgType coins pqrKey r2 mkGen
  | ratchet (ck ck_adv ck_next : ChainKey) (r1 r_adv : RatchetState) :
      r0.findReceiverChainKey msg.senderRatchetKey = .ok none →
      Mut.exec (RatchetState.dhRatchetStep C msg.senderRatchetKey coins) r0 = (.ok ck, r1) →
      ¬ (msg.counter < ck.index) →
      (msg.counter - ck.index).toNat ≤ r1.maxForwardJumps →
      Mut.exec (RatchetState.advanceChain C.F msg.senderRatchetKey msg.counter
        (msg.counter - ck.index).toNat ck) r1 = (.ok ck_adv, r_adv) →
      ck_adv.nextChainKey C.F = .ok ck_next →
      Mut.exec (RatchetState.setReceiverChainKey msg.senderRatchetKey ck_next) r_adv =
        (.ok (), r2) →
      mkGen = ck_adv.messageKeys C.F →
      msg.verifyMacWithAddresses C.F expected remIk locIk (mkGen.generateKeys C.F pqrKey).macKey =
        true →
      DecryptOkBranch C r0 remIk locIk expected msg msgType coins pqrKey r2 mkGen

theorem decryptOkBranch_of_ensure_consume
    {C : Crypto} {r0 r1 r2 : RatchetState} {remIk locIk : IdentityKey}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {pqrKey : CryptoGames.HKDF.Salt}
    {ck : ChainKey} {mkGen : MessageKeyGenerator}
    (hEnsure : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins) r0 =
      (.ok ck, r1))
    (hConsume : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
      msgType) r1 = (.ok mkGen, r2))
    (hMac : msg.verifyMacWithAddresses C.F expected remIk locIk
      (mkGen.generateKeys C.F pqrKey).macKey = true) :
    DecryptOkBranch C r0 remIk locIk expected msg msgType coins pqrKey r2 mkGen := by
  rcases ensureReceiverChain_ok_inv hEnsure with ⟨hFind, rfl⟩ | ⟨hFind, hDh⟩
  · rcases consumeMessageKey_ok_inv hConsume with
      ⟨hLt, hTake⟩ | ⟨hNotLt, hJump, ck_adv, ck_next, r_adv, hAdv, hNext, hSet, hMkGen⟩
    · exact .skipped ck hFind hLt hTake hMac
    · exact .existing ck ck_adv ck_next r_adv hFind hNotLt hJump hAdv hNext hSet hMkGen hMac
  · have hIdx0 : ck.index = 0 := dhRatchetStep_ok_index_eq_zero hDh
    rcases consumeMessageKey_ok_inv hConsume with
      ⟨hLt, _⟩ | ⟨hNotLt, hJump, ck_adv, ck_next, r_adv, hAdv, hNext, hSet, hMkGen⟩
    · rw [hIdx0] at hLt
      exact False.elim (BitVec.not_lt_zero hLt)
    · exact .ratchet ck ck_adv ck_next r1 r_adv hFind hDh hNotLt hJump hAdv hNext hSet hMkGen hMac

/-- Decomposes a successful `SessionState.tryDecryptFromRecordW` into version, remote-identity,
SPQR, and `W.dec` conditions together with `DecryptOkBranch`. -/
theorem decryptW_ok_branch {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W : AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st st' : SessionState PQ} {ptext : List (BitVec 8)}
    (hok : SessionState.tryDecryptFromRecordW C W spqr expected msg msgType coins st =
      (.ok ptext, st')) :
    ∃ (remIk : IdentityKey) (r2 : RatchetState) (mkGen : MessageKeyGenerator)
      (newPqrState : PQ) (pqrKey : CryptoGames.HKDF.Salt),
      st.version.toNat = msg.messageVersion.toNat ∧
      st.remoteIdentity = some remIk ∧
      spqr.recv st.pqRatchetState msg.pqRatchet = .ok (newPqrState, pqrKey) ∧
      W.dec (mkGen.generateKeys C.F pqrKey).cipherKey (mkGen.generateKeys C.F pqrKey).iv
        msg.ciphertext = some ptext ∧
      st' = { st with
        rootKey := r2.rootKey
        previousCounter := r2.previousCounter
        senderChain := r2.senderChain
        receiverChains := r2.receiverChains
        pqRatchetState := newPqrState
        pendingPreKey := false } ∧
      DecryptOkBranch C (ratchetStateOf st) remIk st.localIdentity expected msg msgType coins
        pqrKey r2 mkGen := by
  obtain ⟨hVer, hWithState⟩ := tryDecryptFromRecordW_ok_inv hok
  obtain ⟨remIk, tr_out, hRem, hTr, hSt2⟩ := tryDecryptWithStateW_ok_inv hWithState
  obtain ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, hEnsure, hConsume, hSpqr, hMac, hDec, hTrOut⟩ :=
    tripleRatchet_decryptW_ok_inv hTr
  refine ⟨remIk, r2, mkGen, newPqrState, pqrKey, hVer, hRem, hSpqr, hDec, ?_, ?_⟩
  · rw [hSt2, hTrOut]
  · exact decryptOkBranch_of_ensure_consume hEnsure hConsume hMac

end Proofs.libsignal.RngG.R3
