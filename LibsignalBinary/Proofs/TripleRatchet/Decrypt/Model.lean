/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs

/-!
# Pure Session-Model and Ghost-Relation Lemmas for `try_decrypt_with_state`

Branch unfolding and invariant lemmas for `SessionState.tryDecryptWithState`,
`TripleRatchet.fromSessionState`, `TripleRatchet.decrypt`, `RatchetState.ensureReceiverChain`,
`RatchetState.dhRatchetStep`, `decryptDraws`, and `SessionGhost.AfterTryDecrypt`, covering fixed
`aesCbcDecrypt`, parameterized `decFn`, and explicit-`coins` forms.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.Model

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

/-! ## 0. `Mut.exec` Combinator Lemmas -/

theorem exec_bind {σ α β : Type} (m : Mut σ α) (k : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= k) s =
      match Mut.exec m s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => Mut.exec (k a) s' := by
  unfold Mut.exec
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind,
    ExceptT.bindCont]
  cases m s with
  | mk res s' => cases res <;> rfl

theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok ⟨⟩, f s) := rfl

theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

theorem exec_liftE_ok {σ α : Type} (a : α) (s : σ) :
    Mut.exec (liftE (.ok a) : Mut σ α) s = (.ok a, s) := rfl

theorem exec_liftE_error {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (liftE (.error e) : Mut σ α) s = (.error e, s) := rfl

/-! ## 1. `SessionGhost.AfterTryDecrypt` and `Keeps` Lemmas -/

/-- `G.afterTrFrom` preserves the read-only ghost fields `Keeps`. -/
theorem keeps_afterTrFrom (G : SessionGhost) : G.Keeps G.afterTrFrom := by
  simp [SessionGhost.Keeps, SessionGhost.afterTrFrom]

theorem keeps_trans {G1 G2 G3 : SessionGhost} (h12 : G1.Keeps G2) (h23 : G2.Keeps G3) :
    G1.Keeps G3 := by
  rcases h12 with ⟨hl1, hr1, ha1, hg1⟩
  rcases h23 with ⟨hl2, hr2, ha2, hg2⟩
  exact ⟨hl2.trans hl1, hr2.trans hr1, ha2.trans ha1, hg2.trans hg1⟩

/-- On any error path (`ok = false`), `G.afterTrFrom` satisfies `G.AfterTryDecrypt false G.afterTrFrom`. -/
theorem decRel_false_afterTrFrom (G : SessionGhost) : G.AfterTryDecrypt false G.afterTrFrom := by
  simp [SessionGhost.AfterTryDecrypt, SessionGhost.Keeps, SessionGhost.afterTrFrom]

/-- On the success path (`ok = true`), if `G.afterTrFrom.Keeps G1` (from `TR::apply_to_session_state`)
and `clear_unacknowledged_pre_key_message` clears `pending` and `kyber`, the resulting ghost
satisfies `G.AfterTryDecrypt true { G1 with pending := none, kyber := none }`. -/
theorem decRel_true_of_afterTrFrom_keeps {G G1 : SessionGhost} (h : G.afterTrFrom.Keeps G1) :
    G.AfterTryDecrypt true { G1 with pending := none, kyber := none } := by
  have hK : G.Keeps G1 := keeps_trans (keeps_afterTrFrom G) h
  rcases hK with ⟨hl, hr, ha, hg⟩
  exact ⟨⟨hl, hr, ha, hg⟩, ⟨rfl, rfl⟩⟩

/-! ## 2. `TripleRatchet.fromSessionState` Unfolding Lemmas -/

theorem exec_takeRatchetState {PQ : Type} (st : SessionState PQ) :
    Mut.exec SessionState.takeRatchetState st =
      (.ok ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
       { st with receiverChains := [] }) := rfl

theorem exec_takePqRatchetState (st : SessionState (List (BitVec 8))) :
    Mut.exec SessionState.takePqRatchetState st =
      (.ok st.pqRatchetState, { st with pqRatchetState := [] }) := rfl

/-- When `st.remoteIdentity = none`, `TripleRatchet.fromSessionState` returns
`.error (.invalidSessionStructure .missingRemoteIdentity)`. -/
theorem fromSessionState_eq_of_remote_none {st : SessionState (List (BitVec 8))}
    (h : st.remoteIdentity = none) :
    Mut.exec TripleRatchet.fromSessionState st =
      (.error (.invalidSessionStructure .missingRemoteIdentity),
       { st with receiverChains := [], pqRatchetState := [] }) := by
  unfold TripleRatchet.fromSessionState
  rw [exec_bind, exec_takeRatchetState]
  dsimp only
  rw [exec_bind, exec_takePqRatchetState]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only
  rw [h]
  rfl

/-- When `st.remoteIdentity = some rem`, `TripleRatchet.fromSessionState` returns `.ok tr`. -/
theorem fromSessionState_eq_of_remote_some {st : SessionState (List (BitVec 8))}
    {rem : IdentityKey} (h : st.remoteIdentity = some rem) :
    Mut.exec TripleRatchet.fromSessionState st =
      (.ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
            st.pqRatchetState, st.localIdentity, rem⟩,
       { st with receiverChains := [], pqRatchetState := [] }) := by
  unfold TripleRatchet.fromSessionState
  rw [exec_bind, exec_takeRatchetState]
  dsimp only
  rw [exec_bind, exec_takePqRatchetState]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only
  rw [h]
  rfl

/-- `TripleRatchet.fromSessionState` always leaves `{ st with receiverChains := [],
pqRatchetState := [] }` as the modified `SessionState`. -/
theorem fromSessionState_snd (st : SessionState (List (BitVec 8))) :
    (Mut.exec TripleRatchet.fromSessionState st).2 =
      { st with receiverChains := [], pqRatchetState := [] } := by
  cases h : st.remoteIdentity with
  | none =>
    have h' := fromSessionState_eq_of_remote_none h
    rw [h']
    dsimp only
    rw [h]
  | some rem =>
    have h' := fromSessionState_eq_of_remote_some h
    rw [h']
    dsimp only
    rw [h]

/-- Inversion of `Mut.exec TripleRatchet.fromSessionState st = (.error e, st1)`. -/
theorem fromSessionState_error_inv {st st1 : SessionState (List (BitVec 8))}
    {e : SignalProtocolError}
    (h : Mut.exec TripleRatchet.fromSessionState st = (.error e, st1)) :
    st.remoteIdentity = none ∧
      e = .invalidSessionStructure .missingRemoteIdentity ∧
      st1 = { st with receiverChains := [], pqRatchetState := [] } := by
  cases hrem : st.remoteIdentity with
  | none =>
    have h' := fromSessionState_eq_of_remote_none hrem
    rw [h'] at h
    injection h with he hst1
    injection he with he'
    rw [← hrem]
    exact ⟨rfl, he'.symm, hst1.symm⟩
  | some rem =>
    rw [fromSessionState_eq_of_remote_some hrem] at h
    injection h with he _
    cases he

/-- Inversion of `Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1)`. -/
theorem fromSessionState_ok_inv {st st1 : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))}
    (h : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1)) :
    st.remoteIdentity = some tr.remoteIdentityKey ∧
      tr.ratchet =
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ ∧
      tr.pqrState = st.pqRatchetState ∧
      tr.localIdentityKey = st.localIdentity ∧
      st1 = { st with receiverChains := [], pqRatchetState := [] } := by
  cases hrem : st.remoteIdentity with
  | none =>
    rw [fromSessionState_eq_of_remote_none hrem] at h
    injection h with he _
    cases he
  | some rem =>
    have h' := fromSessionState_eq_of_remote_some hrem
    rw [h'] at h
    injection h with htr hst1
    injection htr with htr'
    subst htr' hst1
    rw [← hrem]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. `findReceiverChainKey`, `dhRatchetStep`, and `ensureReceiverChain` Lemmas -/

theorem findIdx?_some_lt_length {α : Type} {p : α → Bool} {xs : List α} {i : Nat}
    (h : xs.findIdx? p = some i) : i < xs.length :=
  (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1

/-- `findReceiverChainKey` on `.error e` can only be `.invalidSessionStructure .missingReceiverChainKey`
(never `.panic`, because `findIdx?` guarantees the index is in bounds). -/
theorem findReceiverChainKey_error_eq {r : RatchetState} {their : PublicKey}
    {e : SignalProtocolError} (h : r.findReceiverChainKey their = .error e) :
    e = .invalidSessionStructure .missingReceiverChainKey := by
  unfold RatchetState.findReceiverChainKey RatchetState.findReceiverChainIndex at h
  split at h
  · cases h
  · rename_i idx hidx
    have hlt : idx < r.receiverChains.length := findIdx?_some_lt_length hidx
    have hget : r.receiverChains[idx]? = some (r.receiverChains[idx]'hlt) :=
      List.getElem?_eq_getElem hlt
    rw [hget] at h
    dsimp only at h
    split at h
    · injection h with he
      exact he.symm
    · cases h

theorem findReceiverChainKey_ne_panic (r : RatchetState) (their : PublicKey) :
    r.findReceiverChainKey their ≠ .error .panic := by
  intro h
  have he := findReceiverChainKey_error_eq h
  cases he

/-- `rootCreateChain` on `.error e` can only be `.invalidKeyAgreement`. -/
theorem rootCreateChain_error_eq {C : Crypto} {rk : RootKey} {their : PublicKey}
    {our : PrivateKey} {e : SignalProtocolError}
    (h : rootCreateChain C rk their our = .error e) :
    e = .invalidKeyAgreement := by
  unfold rootCreateChain at h
  split at h
  · injection h with he
    exact he.symm
  · cases h

theorem dhRatchetStep_of_senderChain_none {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r : RatchetState} (hsc : r.senderChain = none) :
    Mut.exec (RatchetState.dhRatchetStep C their coins) r =
      (.error (.invalidSessionStructure .missingSenderChain), r) := by
  unfold RatchetState.dhRatchetStep
  rw [exec_bind, exec_get]
  dsimp only
  rw [hsc]
  rfl

theorem exec_takeRootKey (r : RatchetState) :
    Mut.exec RatchetState.takeRootKey r = (.ok r.rootKey, { r with rootKey := 0 }) := rfl

theorem dhRatchetStep_of_first_createChain_error {C : Crypto} {their : PublicKey}
    {coins : BitVec 256} {r : RatchetState} {sc : SenderChain} {e : SignalProtocolError}
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey = .error e) :
    Mut.exec (RatchetState.dhRatchetStep C their coins) r =
      (.error e, { r with rootKey := 0 }) := by
  unfold RatchetState.dhRatchetStep
  rw [exec_bind, exec_get]
  dsimp only
  rw [hsc]
  dsimp only
  rw [exec_bind, exec_takeRootKey]
  dsimp only
  rw [exec_bind, hcc1, exec_liftE_error]
  dsimp only
  rw [hsc]

theorem dhRatchetStep_of_second_createChain_error {C : Crypto} {their : PublicKey}
    {coins : BitVec 256} {r : RatchetState} {sc : SenderChain}
    {newRk : RootKey} {recvCk : ChainKey} {e : SignalProtocolError}
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey = .ok (newRk, recvCk))
    (hcc2 : rootCreateChain C newRk their (KeyPair.generate C coins).privateKey = .error e) :
    Mut.exec (RatchetState.dhRatchetStep C their coins) r =
      (.error e, { r with rootKey := 0 }) := by
  unfold RatchetState.dhRatchetStep
  rw [exec_bind, exec_get]
  dsimp only
  rw [hsc]
  dsimp only
  rw [exec_bind, exec_takeRootKey]
  dsimp only
  rw [exec_bind, hcc1, exec_liftE_ok]
  dsimp only
  rw [exec_bind, hcc2, exec_liftE_error]
  dsimp only
  rw [hsc]

theorem dhRatchetStep_of_both_createChain_ok {C : Crypto} {their : PublicKey}
    {coins : BitVec 256} {r : RatchetState} {sc : SenderChain}
    {newRk finalRk : RootKey} {recvCk sendCk : ChainKey}
    (hsc : r.senderChain = some sc)
    (hcc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey = .ok (newRk, recvCk))
    (hcc2 : rootCreateChain C newRk their (KeyPair.generate C coins).privateKey =
      .ok (finalRk, sendCk)) :
    Mut.exec (RatchetState.dhRatchetStep C their coins) r =
      (.ok recvCk,
       { r with
         previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
         rootKey := finalRk
         receiverChains := RatchetState.evictReceiverChains
           (r.receiverChains ++ [⟨their, some recvCk, []⟩])
         senderChain := some ⟨KeyPair.generate C coins, sendCk⟩ }) := by
  unfold RatchetState.dhRatchetStep
  rw [exec_bind, exec_get]
  dsimp only
  rw [hsc]
  dsimp only
  rw [exec_bind, exec_takeRootKey]
  dsimp only
  rw [exec_bind, hcc1, exec_liftE_ok]
  dsimp only
  rw [exec_bind, hcc2, exec_liftE_ok]
  dsimp only
  rw [exec_bind, exec_modify]
  dsimp only [exec_pure]

/-- `dhRatchetStep` on `.error e` can only be `.invalidSessionStructure .missingSenderChain` or
`.invalidKeyAgreement` (never `.panic`). -/
theorem dhRatchetStep_error_ne_panic {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r r1 : RatchetState} {e : SignalProtocolError}
    (h : Mut.exec (RatchetState.dhRatchetStep C their coins) r = (.error e, r1)) :
    e ≠ .panic := by
  cases hsc : r.senderChain with
  | none =>
    rw [dhRatchetStep_of_senderChain_none hsc] at h
    injection h with he _
    injection he with he'
    subst he'
    decide
  | some sc =>
    cases hcc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
    | error e1 =>
      rw [dhRatchetStep_of_first_createChain_error hsc hcc1] at h
      injection h with he _
      injection he with he'
      subst he'
      rw [rootCreateChain_error_eq hcc1]
      decide
    | ok p1 =>
      rcases p1 with ⟨newRk, recvCk⟩
      cases hcc2 : rootCreateChain C newRk their (KeyPair.generate C coins).privateKey with
      | error e2 =>
        rw [dhRatchetStep_of_second_createChain_error hsc hcc1 hcc2] at h
        injection h with he _
        injection he with he'
        subst he'
        rw [rootCreateChain_error_eq hcc2]
        decide
      | ok p2 =>
        rcases p2 with ⟨finalRk, sendCk⟩
        rw [dhRatchetStep_of_both_createChain_ok hsc hcc1 hcc2] at h
        cases h

theorem ensureReceiverChain_of_find_some {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r : RatchetState} {ck : ChainKey}
    (h : r.findReceiverChainKey their = .ok (some ck)) :
    Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r) := by
  unfold RatchetState.ensureReceiverChain
  rw [exec_bind, exec_get]
  dsimp only
  rw [exec_bind, h, exec_liftE_ok]
  rfl

theorem ensureReceiverChain_of_find_error {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r : RatchetState} {e : SignalProtocolError}
    (h : r.findReceiverChainKey their = .error e) :
    Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.error e, r) := by
  unfold RatchetState.ensureReceiverChain
  rw [exec_bind, exec_get]
  dsimp only
  rw [exec_bind, h, exec_liftE_error]

theorem ensureReceiverChain_of_find_none {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r : RatchetState}
    (h : r.findReceiverChainKey their = .ok none) :
    Mut.exec (RatchetState.ensureReceiverChain C their coins) r =
      Mut.exec (RatchetState.dhRatchetStep C their coins) r := by
  unfold RatchetState.ensureReceiverChain
  rw [exec_bind, exec_get]
  dsimp only
  rw [exec_bind, h, exec_liftE_ok]

/-! ## 4. `drawsCoins` and `decryptDraws` Characterization per Branch -/

/-- When `fromSessionState` returns `.error e`, `decryptDraws = 0`. -/
theorem decryptDraws_of_fromSessionState_error {C : Crypto}
    {st st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (their : PublicKey) (rest : List (BitVec 8))
    (h : Mut.exec TripleRatchet.fromSessionState st = (.error e, st1)) :
    decryptDraws C st their rest = 0 := by
  have ⟨hrem, _, _⟩ := fromSessionState_error_inv h
  simp [decryptDraws, drawsCoins, hrem]

/-- When `fromSessionState = (.ok tr, st1)` and `tr.ratchet.findReceiverChainKey their = .ok (some ck)`,
`decryptDraws = 0`. -/
theorem decryptDraws_of_find_some {C : Crypto}
    {st st1 : SessionState (List (BitVec 8))} {tr : TripleRatchet (List (BitVec 8))}
    {their : PublicKey} {ck : ChainKey} (rest : List (BitVec 8))
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hf : tr.ratchet.findReceiverChainKey their = .ok (some ck)) :
    decryptDraws C st their rest = 0 := by
  have ⟨_, hrat, _, _, _⟩ := fromSessionState_ok_inv htr
  rw [hrat] at hf
  unfold decryptDraws drawsCoins
  rw [hf]
  simp

/-- When `fromSessionState = (.ok tr, st1)` and `tr.ratchet.findReceiverChainKey their = .error e`,
`decryptDraws = 0`. -/
theorem decryptDraws_of_find_error {C : Crypto}
    {st st1 : SessionState (List (BitVec 8))} {tr : TripleRatchet (List (BitVec 8))}
    {their : PublicKey} {e : SignalProtocolError} (rest : List (BitVec 8))
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hf : tr.ratchet.findReceiverChainKey their = .error e) :
    decryptDraws C st their rest = 0 := by
  have ⟨_, hrat, _, _, _⟩ := fromSessionState_ok_inv htr
  rw [hrat] at hf
  unfold decryptDraws drawsCoins
  rw [hf]
  simp

/-- When `fromSessionState = (.ok tr, st1)`, `tr.ratchet.findReceiverChainKey their = .ok none`,
and `tr.ratchet.senderChain = none`, `decryptDraws = 0`. -/
theorem decryptDraws_of_senderChain_none {C : Crypto}
    {st st1 : SessionState (List (BitVec 8))} {tr : TripleRatchet (List (BitVec 8))}
    {their : PublicKey} (rest : List (BitVec 8))
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hf : tr.ratchet.findReceiverChainKey their = .ok none)
    (hsc : tr.ratchet.senderChain = none) :
    decryptDraws C st their rest = 0 := by
  have ⟨_, hrat, _, _, _⟩ := fromSessionState_ok_inv htr
  rw [hrat] at hf hsc
  dsimp only at hsc
  unfold decryptDraws drawsCoins
  rw [hf]
  simp [hsc]

/-- When `fromSessionState = (.ok tr, st1)`, `tr.ratchet.findReceiverChainKey their = .ok none`,
`tr.ratchet.senderChain = some sc`, and the receiving `rootCreateChain` fails, `decryptDraws = 0`. -/
theorem decryptDraws_of_first_createChain_error {C : Crypto}
    {st st1 : SessionState (List (BitVec 8))} {tr : TripleRatchet (List (BitVec 8))}
    {their : PublicKey} {sc : SenderChain} {e : SignalProtocolError} (rest : List (BitVec 8))
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hf : tr.ratchet.findReceiverChainKey their = .ok none)
    (hsc : tr.ratchet.senderChain = some sc)
    (hcc1 : rootCreateChain C tr.ratchet.rootKey their sc.ratchetKey.privateKey = .error e) :
    decryptDraws C st their rest = 0 := by
  have ⟨_, hrat, _, _, _⟩ := fromSessionState_ok_inv htr
  rw [hrat] at hf hsc hcc1
  dsimp only at hsc hcc1
  unfold decryptDraws drawsCoins
  rw [hf]
  simp [hsc, hcc1]

/-- When `fromSessionState = (.ok tr, st1)`, `tr.ratchet.findReceiverChainKey their = .ok none`,
`tr.ratchet.senderChain = some sc`, and the receiving `rootCreateChain` succeeds,
`decryptDraws = min 32 rest.length`. -/
theorem decryptDraws_of_first_createChain_ok {C : Crypto}
    {st st1 : SessionState (List (BitVec 8))} {tr : TripleRatchet (List (BitVec 8))}
    {their : PublicKey} {sc : SenderChain} {newRk : RootKey} {recvCk : ChainKey}
    (rest : List (BitVec 8))
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hf : tr.ratchet.findReceiverChainKey their = .ok none)
    (hsc : tr.ratchet.senderChain = some sc)
    (hcc1 : rootCreateChain C tr.ratchet.rootKey their sc.ratchetKey.privateKey =
      .ok (newRk, recvCk)) :
    decryptDraws C st their rest = min 32 rest.length := by
  have ⟨hrem, hrat, _, _, _⟩ := fromSessionState_ok_inv htr
  rw [hrat] at hf hsc hcc1
  dsimp only at hsc hcc1
  unfold decryptDraws drawsCoins
  rw [hf]
  simp [hsc, hcc1, hrem]

/-- When `fromSessionState = (.ok tr, st1)`, `tr.ratchet.findReceiverChainKey their = .ok none`,
and `dhRatchetStep` succeeds, `decryptDraws = min 32 rest.length`. -/
theorem decryptDraws_of_dhRatchetStep_ok {C : Crypto}
    {st st1 : SessionState (List (BitVec 8))} {tr : TripleRatchet (List (BitVec 8))}
    {their : PublicKey} {coins : BitVec 256} {ck : ChainKey} {r1 : RatchetState}
    (rest : List (BitVec 8))
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (hf : tr.ratchet.findReceiverChainKey their = .ok none)
    (hdh : Mut.exec (RatchetState.dhRatchetStep C their coins) tr.ratchet = (.ok ck, r1)) :
    decryptDraws C st their rest = min 32 rest.length := by
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_of_senderChain_none hsc] at hdh
    cases hdh
  | some sc =>
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey their sc.ratchetKey.privateKey with
    | error e1 =>
      rw [dhRatchetStep_of_first_createChain_error hsc hcc1] at hdh
      cases hdh
    | ok p1 =>
      exact decryptDraws_of_first_createChain_ok rest htr hf hsc hcc1

/-! ## 5. `TryDecryptGhost.model` Branch Unfolding Lemmas -/

/-- `TripleRatchet.onRatchet` preserves `pqrState`, `localIdentityKey`, and `remoteIdentityKey`. -/
theorem onRatchet_eq {PQ α : Type} (m : Mut RatchetState α) (tr : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) tr =
      ((Mut.exec m tr.ratchet).1, { tr with ratchet := (Mut.exec m tr.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  rw [exec_bind, exec_get]
  dsimp only
  cases h : Mut.exec m tr.ratchet with
  | mk res r' =>
    change Mut.exec (do set { tr with ratchet := r' }; liftE res) tr = (res, { tr with ratchet := r' })
    rw [exec_bind]
    dsimp only [Mut.exec, ExceptT.run, StateT.run, set, StateT.set, pure, ExceptT.pure, ExceptT.mk]
    cases res <;> rfl

/-- Unfolding `TryDecryptGhost.model` once `fromSessionState` is known. -/
theorem model_unfold {C : Crypto} {S : SpqrModel}
    (x : TryDecryptGhost) :
    x.model C S uuidTryParse =
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error e, st1) => (.error e, st1)
      | (.ok tr, st1) =>
        match Mut.exec (TripleRatchet.decrypt C S.spqr (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
            x.msg x.msgType (coinsOf x.rest)) tr with
        | (.error e, _) => (.error e, st1)
        | (.ok pt, tr') =>
          (.ok pt, (tr'.applyToSessionState st1).clearUnacknowledgedPreKeyMessage) := by
  unfold TryDecryptGhost.model SessionState.tryDecryptWithState
  rw [exec_bind]
  cases Mut.exec TripleRatchet.fromSessionState x.st with
  | mk res st1 =>
    cases res with
    | error e => rfl
    | ok tr =>
      dsimp only
      cases Mut.exec (TripleRatchet.decrypt C S.spqr (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
          x.msg x.msgType (coinsOf x.rest)) tr with
      | mk r tr' =>
        cases r with
        | error e =>
          rw [exec_bind, exec_liftE_error]
        | ok pt =>
          rw [exec_bind, exec_liftE_ok]
          dsimp only
          rw [exec_bind, exec_modify]
          rfl

/-- S1 error branch: when `Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1)`,
`x.model C S parse = (.error e, st1)` and `e ≠ .panic`. -/
theorem model_of_fromSessionState_error {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1)) :
    x.model C S uuidTryParse = (.error e, st1) ∧ e ≠ .panic := by
  have ⟨_, he, _⟩ := fromSessionState_error_inv htr
  refine ⟨?_, by subst he; decide⟩
  rw [model_unfold, htr]

/-- S2/S3 `ensureReceiverChain` error branch: when `fromSessionState = (.ok tr, st1)` and
`ensureReceiverChain` returns `(.error e, r1)`, `x.model C S parse = (.error e, st1)`. -/
theorem model_of_ensureReceiverChain_error {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {r1 : RatchetState}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.error e, r1)) :
    x.model C S uuidTryParse = (.error e, st1) := by
  rw [model_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]

/-- S4 `consumeMessageKey` error branch: when `fromSessionState = (.ok tr, st1)`,
`ensureReceiverChain = (.ok ck, r1)`, and `consumeMessageKey = (.error e, r2)`,
`x.model C S parse = (.error e, st1)`. -/
theorem model_of_cmk_error {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {e : SignalProtocolError}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.error e, r2)) :
    x.model C S uuidTryParse = (.error e, st1) := by
  rw [model_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]

/-- S5 `spqr.recv` error branch: when `fromSessionState = (.ok tr, st1)`,
`ensureReceiverChain = (.ok ck, r1)`, `consumeMessageKey = (.ok mkg, r2)`, and
`S.recv tr.pqrState x.msg.pqRatchet = .error sd`,
`x.model C S parse = (.error (if sd then .invalidState else .invalidMessage x.msgType .pqRatchet), st1)`. -/
theorem model_of_spqr_error {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {sd : Bool}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState x.msg.pqRatchet = .error sd)
    (hnp : S.recvPanics tr.pqrState x.msg.pqRatchet = false) :
    x.model C S uuidTryParse =
      (.error (if sd then .invalidState else .invalidMessage x.msgType .pqRatchet), st1) := by
  rw [model_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr]
  cases sd <;> rfl

theorem model_of_verifyMac_false {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = false)
    (hnp : S.recvPanics tr.pqrState x.msg.pqRatchet = false) :
    x.model C S uuidTryParse = (.error (.invalidMessage x.msgType .macFailed), st1) := by
  rw [model_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  rfl

theorem model_of_aesDec_none {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = true)
    (haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
      (mkg.generateKeys C.F pqrKey).iv x.msg.ciphertext = none)
    (hnp : S.recvPanics tr.pqrState x.msg.pqRatchet = false) :
    x.model C S uuidTryParse = (.error (.invalidMessage x.msgType .badCiphertext), st1) := by
  rw [model_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [haes]
  rfl

theorem model_of_aesDec_some {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState pt : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = true)
    (haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
      (mkg.generateKeys C.F pqrKey).iv x.msg.ciphertext = some pt)
    (hnp : S.recvPanics tr.pqrState x.msg.pqRatchet = false) :
    x.model C S uuidTryParse =
      (.ok pt,
       (({ tr with ratchet := r2, pqrState := newPqrState }).applyToSessionState
          st1).clearUnacknowledgedPreKeyMessage) := by
  rw [model_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [haes]
  dsimp only
  rw [exec_bind, exec_modify]
  rfl

/-! ## 6. `TryDecryptGhost.modelFn` Branch Unfolding Lemmas & Panic Equivalence -/

theorem modelFn_unfold {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {S : SpqrModel}
    (x : TryDecryptGhost) :
    x.modelFn C decFn S uuidTryParse =
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error e, st1) => (.error e, st1)
      | (.ok tr, st1) =>
        match Mut.exec (TripleRatchet.decryptFn C decFn S.spqr
            (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
            x.msg x.msgType (coinsOf x.rest)) tr with
        | (.error e, _) => (.error e, st1)
        | (.ok pt, tr') =>
          (.ok pt, (tr'.applyToSessionState st1).clearUnacknowledgedPreKeyMessage) := by
  unfold TryDecryptGhost.modelFn SessionState.tryDecryptWithStateFn
  rw [exec_bind]
  cases Mut.exec TripleRatchet.fromSessionState x.st with
  | mk res st1 =>
    cases res with
    | error e => rfl
    | ok tr =>
      dsimp only
      cases Mut.exec (TripleRatchet.decryptFn C decFn S.spqr
          (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
          x.msg x.msgType (coinsOf x.rest)) tr with
      | mk r tr' =>
        cases r with
        | error e =>
          rw [exec_bind, exec_liftE_error]
        | ok pt =>
          rw [exec_bind, exec_liftE_ok]
          dsimp only
          rw [exec_bind, exec_modify]
          rfl

theorem modelFn_of_fromSessionState_error {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {S : SpqrModel}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1)) :
    x.modelFn C decFn S uuidTryParse = (.error e, st1) ∧ e ≠ .panic := by
  have ⟨_, he, _⟩ := fromSessionState_error_inv htr
  refine ⟨?_, by subst he; decide⟩
  rw [modelFn_unfold, htr]

theorem modelFn_of_ensureReceiverChain_error {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {r1 : RatchetState}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.error e, r1)) :
    x.modelFn C decFn S uuidTryParse = (.error e, st1) := by
  rw [modelFn_unfold, htr]
  dsimp only
  unfold TripleRatchet.decryptFn
  rw [exec_bind, onRatchet_eq, herc]

theorem modelFn_of_cmk_error {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {e : SignalProtocolError}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.error e, r2)) :
    x.modelFn C decFn S uuidTryParse = (.error e, st1) := by
  rw [modelFn_unfold, htr]
  dsimp only
  unfold TripleRatchet.decryptFn
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]

theorem modelFn_of_spqr_error {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {sd : Bool}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState x.msg.pqRatchet = .error sd)
    (hnp : S.recvPanics tr.pqrState x.msg.pqRatchet = false) :
    x.modelFn C decFn S uuidTryParse =
      (.error (if sd then .invalidState else .invalidMessage x.msgType .pqRatchet), st1) := by
  rw [modelFn_unfold, htr]
  dsimp only
  unfold TripleRatchet.decryptFn
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr]
  cases sd <;> rfl

theorem modelFn_of_verifyMac_false {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = false)
    (hnp : S.recvPanics tr.pqrState x.msg.pqRatchet = false) :
    x.modelFn C decFn S uuidTryParse = (.error (.invalidMessage x.msgType .macFailed), st1) := by
  rw [modelFn_unfold, htr]
  dsimp only
  unfold TripleRatchet.decryptFn
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  rfl

theorem modelFn_of_aesDec_none {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = true)
    (haes : decFn x.msg.ciphertext
      (keyToBytes32 (mkg.generateKeys C.F pqrKey).cipherKey)
      (CBC.blockToBytesLE (mkg.generateKeys C.F pqrKey).iv) = none)
    (hnp : S.recvPanics tr.pqrState x.msg.pqRatchet = false) :
    x.modelFn C decFn S uuidTryParse = (.error (.invalidMessage x.msgType .badCiphertext), st1) := by
  rw [modelFn_unfold, htr]
  dsimp only
  unfold TripleRatchet.decryptFn
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [haes]
  rfl

theorem modelFn_of_aesDec_some {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState pt : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = true)
    (haes : decFn x.msg.ciphertext
      (keyToBytes32 (mkg.generateKeys C.F pqrKey).cipherKey)
      (CBC.blockToBytesLE (mkg.generateKeys C.F pqrKey).iv) = some pt)
    (hnp : S.recvPanics tr.pqrState x.msg.pqRatchet = false) :
    x.modelFn C decFn S uuidTryParse =
      (.ok pt,
       (({ tr with ratchet := r2, pqrState := newPqrState }).applyToSessionState
          st1).clearUnacknowledgedPreKeyMessage) := by
  rw [modelFn_unfold, htr]
  dsimp only
  unfold TripleRatchet.decryptFn
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [haes]
  dsimp only
  rw [exec_bind, exec_modify]
  rfl

/-- Panic outcome of `modelFn` is independent of `decFn` (since `.panic` only arises in
`consumeMessageKey`, before `decFn` / `aesCbcDecrypt` is reached). -/
theorem modelFn_fst_eq_panic_iff (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (S : SpqrModel) (x : TryDecryptGhost)
    (hnp : S.recvPanics x.st.pqRatchetState x.msg.pqRatchet = false) :
    (x.modelFn C decFn S uuidTryParse).1 = .error .panic ↔ (x.model C S uuidTryParse).1 = .error .panic := by
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk res st1 =>
    cases res with
    | error e =>
      rw [(modelFn_of_fromSessionState_error htr).1, (model_of_fromSessionState_error htr).1]
    | ok tr =>
      have hnp' : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by
        rw [(fromSessionState_ok_inv htr).2.2.1]; exact hnp
      cases herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | mk res1 r1 =>
        cases res1 with
        | error e =>
          rw [modelFn_of_ensureReceiverChain_error htr herc,
            model_of_ensureReceiverChain_error htr herc]
        | ok ck =>
          cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
              x.msg.counter x.msgType) r1 with
          | mk res2 r2 =>
            cases res2 with
            | error e =>
              rw [modelFn_of_cmk_error htr herc hcmk, model_of_cmk_error htr herc hcmk]
            | ok mkg =>
              cases hspqr : S.recv tr.pqrState x.msg.pqRatchet with
              | error sd =>
                rw [modelFn_of_spqr_error htr herc hcmk hspqr hnp',
                  model_of_spqr_error htr herc hcmk hspqr hnp']
              | ok pqPair =>
                rcases pqPair with ⟨newPqrState, pqrKey⟩
                cases hmac : x.msg.verifyMacWithAddresses C.F
                    (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                    tr.remoteIdentityKey tr.localIdentityKey
                    (mkg.generateKeys C.F pqrKey).macKey with
                | false =>
                  rw [modelFn_of_verifyMac_false htr herc hcmk hspqr hmac hnp',
                    model_of_verifyMac_false htr herc hcmk hspqr hmac hnp']
                | true =>
                  have hfn : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic := by
                    cases haes : decFn x.msg.ciphertext
                        (keyToBytes32 (mkg.generateKeys C.F pqrKey).cipherKey)
                        (CBC.blockToBytesLE (mkg.generateKeys C.F pqrKey).iv) with
                    | none =>
                      rw [modelFn_of_aesDec_none htr herc hcmk hspqr hmac haes hnp']
                      rintro ⟨⟩
                    | some pt =>
                      rw [modelFn_of_aesDec_some htr herc hcmk hspqr hmac haes hnp']
                      rintro ⟨⟩
                  have hmod : (x.model C S uuidTryParse).1 ≠ .error .panic := by
                    cases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                        (mkg.generateKeys C.F pqrKey).iv x.msg.ciphertext with
                    | none =>
                      rw [model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp']
                      rintro ⟨⟩
                    | some pt =>
                      rw [model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp']
                      rintro ⟨⟩
                  exact iff_of_false hfn hmod

theorem tryDecryptFnSpec_pre_eq (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).pre =
      (tryDecryptSpec C A ctl uuidTryParse S img).pre := by
  unfold tryDecryptFnSpec tryDecryptSpec Spec.inImage
  rfl

theorem tryDecryptFnSpec_onPanic_eq (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic =
      (tryDecryptSpec C A ctl uuidTryParse S img).onPanic := by
  funext x s0 sf
  unfold tryDecryptFnSpec tryDecryptSpec Spec.inImage
  cases hp : S.recvPanics x.st.pqRatchetState x.msg.pqRatchet with
  | true => simp only [hp, true_or, or_true]
  | false => simp only [modelFn_fst_eq_panic_iff C decFn S x hp]

/-! ## 7. Generic-over-Coins Model Unfolding Lemmas -/

/-- Pure session-model execution of `tryDecryptWithState` with explicit `coins`. -/
def modelWithCoins (C : Crypto) (S : SpqrModel) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st : SessionState (List (BitVec 8))) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState (List (BitVec 8)) :=
  Mut.exec (SessionState.tryDecryptWithState C S.spqr expected msg msgType coins) st

theorem modelWithCoins_eq_model (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : TryDecryptGhost) :
    modelWithCoins C S (serializeAddresses (serviceIdParse uuidParse) x.rem x.loc) x.msg x.msgType
      (coinsOf x.rest) x.st = x.model C S uuidParse :=
  rfl

theorem modelWithCoins_unfold {C : Crypto} {S : SpqrModel}
    (expected : Option (List (BitVec 8))) (msg : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (st : SessionState (List (BitVec 8))) :
    modelWithCoins C S expected msg msgType coins st =
      match Mut.exec TripleRatchet.fromSessionState st with
      | (.error e, st1) => (.error e, st1)
      | (.ok tr, st1) =>
        match Mut.exec (TripleRatchet.decrypt C S.spqr expected msg msgType coins) tr with
        | (.error e, _) => (.error e, st1)
        | (.ok pt, tr') =>
          (.ok pt, (tr'.applyToSessionState st1).clearUnacknowledgedPreKeyMessage) := by
  unfold modelWithCoins SessionState.tryDecryptWithState
  rw [exec_bind]
  cases Mut.exec TripleRatchet.fromSessionState st with
  | mk res st1 =>
    cases res with
    | error e => rfl
    | ok tr =>
      dsimp only
      cases Mut.exec (TripleRatchet.decrypt C S.spqr expected msg msgType coins) tr with
      | mk r tr' =>
        cases r with
        | error e =>
          rw [exec_bind, exec_liftE_error]
        | ok pt =>
          rw [exec_bind, exec_liftE_ok]
          dsimp only
          rw [exec_bind, exec_modify]
          rfl

theorem modelWithCoins_of_fromSessionState_error {C : Crypto} {S : SpqrModel}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st : SessionState (List (BitVec 8))}
    {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.error e, st1)) :
    modelWithCoins C S expected msg msgType coins st = (.error e, st1) ∧ e ≠ .panic := by
  have ⟨_, he, _⟩ := fromSessionState_error_inv htr
  refine ⟨?_, by subst he; decide⟩
  rw [modelWithCoins_unfold, htr]

theorem modelWithCoins_of_ensureReceiverChain_error {C : Crypto} {S : SpqrModel}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {r1 : RatchetState}
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
      tr.ratchet = (.error e, r1)) :
    modelWithCoins C S expected msg msgType coins st = (.error e, st1) := by
  rw [modelWithCoins_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]

theorem modelWithCoins_of_cmk_error {C : Crypto} {S : SpqrModel}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {e : SignalProtocolError}
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
      msgType) r1 = (.error e, r2)) :
    modelWithCoins C S expected msg msgType coins st = (.error e, st1) := by
  rw [modelWithCoins_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]

theorem modelWithCoins_of_spqr_error {C : Crypto} {S : SpqrModel}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {sd : Bool}
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
      msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState msg.pqRatchet = .error sd)
    (hnp : S.recvPanics tr.pqrState msg.pqRatchet = false) :
    modelWithCoins C S expected msg msgType coins st =
      (.error (if sd then .invalidState else .invalidMessage msgType .pqRatchet), st1) := by
  rw [modelWithCoins_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr]
  cases sd <;> rfl

theorem modelWithCoins_of_verifyMac_false {C : Crypto} {S : SpqrModel}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
      msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : msg.verifyMacWithAddresses C.F expected
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = false)
    (hnp : S.recvPanics tr.pqrState msg.pqRatchet = false) :
    modelWithCoins C S expected msg msgType coins st =
      (.error (.invalidMessage msgType .macFailed), st1) := by
  rw [modelWithCoins_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  rfl

theorem modelWithCoins_of_aesDec_none {C : Crypto} {S : SpqrModel}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
      msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : msg.verifyMacWithAddresses C.F expected
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = true)
    (haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
      (mkg.generateKeys C.F pqrKey).iv msg.ciphertext = none)
    (hnp : S.recvPanics tr.pqrState msg.pqRatchet = false) :
    modelWithCoins C S expected msg msgType coins st =
      (.error (.invalidMessage msgType .badCiphertext), st1) := by
  rw [modelWithCoins_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [haes]
  rfl

theorem modelWithCoins_of_aesDec_some {C : Crypto} {S : SpqrModel}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {newPqrState pt : List (BitVec 8)} {pqrKey : Salt}
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
      msgType) r1 = (.ok mkg, r2))
    (hspqr : S.recv tr.pqrState msg.pqRatchet = .ok (newPqrState, pqrKey))
    (hmac : msg.verifyMacWithAddresses C.F expected
      tr.remoteIdentityKey tr.localIdentityKey (mkg.generateKeys C.F pqrKey).macKey = true)
    (haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
      (mkg.generateKeys C.F pqrKey).iv msg.ciphertext = some pt)
    (hnp : S.recvPanics tr.pqrState msg.pqRatchet = false) :
    modelWithCoins C S expected msg msgType coins st =
      (.ok pt,
       (({ tr with ratchet := r2, pqrState := newPqrState }).applyToSessionState
          st1).clearUnacknowledgedPreKeyMessage) := by
  rw [modelWithCoins_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  rw [hspqr, exec_bind, exec_pure]
  dsimp only
  rw [hmac]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [haes]
  dsimp only
  rw [exec_bind, exec_modify]
  rfl

end CryptoVerification.LibsignalTripleRatchet.Decrypt.Model
