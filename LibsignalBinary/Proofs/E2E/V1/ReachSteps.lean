/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
public import LibsignalBinary.Specifications.LibsignalE2E.ParamsEWith
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.TripleRatchet.Seeds.Model

/-!
# Session-model step, epoch, and wire-length lemmas for arbitrary SPQR models

Generalizes the reachable-state step lemmas (`SessRepr`, `SeedsLen32`, receiver-chain bounds, and
identity preservation across `messageEncrypt`, `TripleRatchet.decrypt`, and `tryDecryptFromRecord`),
epoch transition lemmas (`send_epochs_gen`, `recv_epochs_gen`), and wire-length bound
(`send_wire_len_gen`) from `spqrOffB` to an arbitrary `S : Spqr Bytes PQC`.
-/

@[expose] public section

namespace CryptoVerification.E2E.V1

set_option autoImplicit false

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.Record CryptoVerification.E2E.Reach
open CryptoVerification.E2E.Epochs CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Seeds

attribute [local simp] exec_pure exec_throw exec_get exec_set exec_modify exec_modifyGet exec_liftE
  exec_bind exec_onRatchet

/-! ## Session-state step lemmas for arbitrary `Spqr` models -/

section Steps

variable {PQC : Type}

/-- `SessionState.messageEncrypt` preserves `SessRepr` for any SPQR model `S`. -/
theorem sessRepr_messageEncrypt_gen (C : Crypto) (codec : SignalMessageProtoCodec) (S : Spqr Bytes PQC)
    (addresses : Option Bytes) (ptext : Bytes) (coins : PQC) (st st' : SessionState Bytes)
    (msg : SignalMessage) (hrep : SessRepr st)
    (h : SessionState.messageEncrypt C codec S addresses ptext coins st = (.ok msg, st')) :
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
        simp only [exec_bind, exec_get] at h
        cases hpan : S.sendPanics st.pqRatchetState coins
        case true => simp [hpan] at h
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
        rcases hs : S.send st.pqRatchetState coins with _ | ⟨pq', key, pm⟩
        · simp [hs] at h
        · simp only [hs] at h
          rcases hn : sc.chainKey.nextChainKey C.F with _ | next
          · simp [hn] at h
          · simp only [hn, exec_bind, exec_liftE, exec_set, exec_pure, Prod.mk.injEq,
              Except.ok.injEq] at h
            rcases h with ⟨_, rfl⟩
            refine ⟨hrep.1, ?_⟩
            intro sc' hsc'
            simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_some,
              Option.some.injEq] at hsc'
            subst hsc'
            exact hrep.2 sc hsc

/-- `SessionState.tryDecryptFromRecord` preserves `SessRepr` for any SPQR model `S`. -/
theorem sessRepr_tryDecryptFromRecord_gen (C : Crypto) (S : Spqr Bytes PQC)
    (expected : Option Bytes) (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState Bytes) (pt : Bytes) (hrep : SessRepr st)
    (h : SessionState.tryDecryptFromRecord C S expected m msgType coins st = (.ok pt, st')) :
    SessRepr st' := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C S expected m msgType coins) st with
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
        rcases hdec : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins)
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
              simp only [exec_get] at hdec
              cases hpan : S.recvPanics st.pqRatchetState m.pqRatchet
              case true => simp [hpan] at hdec
              simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
              rcases hspqr : S.recv st.pqRatchetState m.pqRatchet with ⟨_ | _⟩ | ⟨pq', key⟩
              · simp [hspqr] at hdec
              · simp [hspqr] at hdec
              · simp only [hspqr, exec_bind, exec_pure] at hdec
                split at hdec
                · simp at hdec
                · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F key).cipherKey
                      (mkg.generateKeys C.F key).iv m.ciphertext with _ | ptext'
                  · simp [haes] at hdec
                  · simp only [haes] at hdec
                    rcases hdec with ⟨_, rfl⟩
                    exact hr2

/-- `SessionState.messageEncrypt` preserves `SeedsLen32`, the receiver-chain bound, and party
identities, updating `pqRatchetState` and `msg.pqRatchet` via `S.send`. -/
theorem messageEncrypt_ok_props_gen (C : Crypto) (codec : SignalMessageProtoCodec) (S : Spqr Bytes PQC)
    (addresses : Option Bytes) (ptext : Bytes) (coins : PQC) (st st' : SessionState Bytes)
    (msg : SignalMessage) (hseeds : SeedsLen32 st)
    (hlen : st.receiverChains.length ≤ maxReceiverChains)
    (h : SessionState.messageEncrypt C codec S addresses ptext coins st = (.ok msg, st')) :
    SeedsLen32 st' ∧ st'.receiverChains.length ≤ maxReceiverChains ∧
      st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity ∧
      ∃ key pm, S.send st.pqRatchetState coins = some (st'.pqRatchetState, key, pm) ∧
        msg.pqRatchet = pm := by
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
        simp only [exec_bind, exec_get] at h
        cases hpan : S.sendPanics st.pqRatchetState coins
        case true => simp [hpan] at h
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
        rcases hs : S.send st.pqRatchetState coins with _ | ⟨pq', key, pm⟩
        · simp [hs] at h
        · simp only [hs] at h
          rcases hn : sc.chainKey.nextChainKey C.F with _ | next
          · simp [hn] at h
          · simp only [hn, exec_bind, exec_liftE, exec_set, exec_pure, Prod.mk.injEq,
              Except.ok.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            simp [OutgoingTripleRatchet.applyToSessionState, SeedsLen32] at hseeds ⊢
            exact ⟨hseeds, hlen, rfl⟩

/-- `TripleRatchet.decrypt` preserves the receiver-chain bound and updates `pqrState` via `S.recv`
on `m.pqRatchet`. -/
theorem tr_decrypt_ok_props_gen (C : Crypto) (S : Spqr Bytes PQC) (expected : Option Bytes)
    (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (t t' : TripleRatchet Bytes) (pt : Bytes)
    (hlen : t.ratchet.receiverChains.length ≤ maxReceiverChains)
    (h : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins) t = (.ok pt, t')) :
    t'.ratchet.receiverChains.length ≤ maxReceiverChains ∧
      ∃ key, S.recv t.pqrState m.pqRatchet = .ok (t'.pqrState, key) := by
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
      simp only [exec_get] at h
      cases hpan : S.recvPanics t.pqrState m.pqRatchet
      case true => simp [hpan] at h
      simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
      rcases hspqr : S.recv t.pqrState m.pqRatchet with ⟨_ | _⟩ | ⟨pq', key⟩
      · simp [hspqr] at h
      · simp [hspqr] at h
      · simp only [hspqr, exec_bind, exec_pure] at h
        split at h
        · simp at h
        · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F key).cipherKey
              (mkg.generateKeys C.F key).iv m.ciphertext with _ | ptext
          · simp [haes] at h
          · simp only [haes] at h
            rcases h with ⟨_, rfl⟩
            exact ⟨h2.trans_le h1, key, rfl⟩

/-- `SessionState.tryDecryptFromRecord` preserves `SeedsLen32`, the receiver-chain bound, and party
identities, updating `pqRatchetState` via `S.recv` on `m.pqRatchet`. -/
theorem tryDecryptFromRecord_ok_props_gen (C : Crypto) (S : Spqr Bytes PQC)
    (expected : Option Bytes) (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState Bytes) (pt : Bytes) (hseeds : SeedsLen32 st)
    (hlen : st.receiverChains.length ≤ maxReceiverChains)
    (h : SessionState.tryDecryptFromRecord C S expected m msgType coins st = (.ok pt, st')) :
    SeedsLen32 st' ∧ st'.receiverChains.length ≤ maxReceiverChains ∧
      st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity ∧
      ∃ key, S.recv st.pqRatchetState m.pqRatchet = .ok (st'.pqRatchetState, key) := by
  have hseeds' : SeedsLen32 st' := by
    have := tryDecryptFromRecord_preserves C S expected m msgType coins st hseeds
    simpa [h] using this
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C S expected m msgType coins) st with
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
        rcases hdec : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · simp [hdec] at hd
        · rw [hdec] at hd
          simp only [exec_liftE, exec_modify, Prod.mk.injEq, Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          obtain ⟨hlen', key, hk⟩ := tr_decrypt_ok_props_gen C S expected m msgType coins _ tr' pt' hlen hdec
          exact ⟨hseeds', hlen', rfl, rfl, key, hk⟩

end Steps

/-! ## Epoch and wire-length lemmas for arbitrary `Spqr` models and coin types -/

theorem paramsEWith_spqrOffB (C : Crypto) :
    sessionParamsForSpqr C CryptoVerification.E2E.spqrOffB = spqrOffSessionParams C := rfl

/-- `Params.send` epoch transition characterization for arbitrary coin type `PQC`. -/
theorem send_epochs_gen {PQC : Type} (P : Params Bytes PQC) (g : GhostState Bytes) (m : Bytes)
    (r : PQC) (msg : SignalMessage) (s : SessionState Bytes)
    (h : SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session =
      (.ok msg, s)) :
    EpochGhost.ofGhost (P.send g m r).1 = (EpochGhost.ofGhost g).send g.party := by
  rw [Record.send_eq_afterSend, h]
  have hs : s.receiverChains = g.session.receiverChains := by
    have hrc := messageEncrypt_receiverChains P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
    simpa [h] using hrc
  dsimp [EpochGhost.ofGhost, GhostState.afterSend, EpochGhost.send]
  rw [hs]

/-- `Params.receive` epoch transition characterization for arbitrary coin type `PQC`. -/
theorem recv_epochs_gen {PQC : Type} (P : Params Bytes PQC) (g : GhostState Bytes) (c : Bytes)
    (rc : BitVec 256) (hal : g.Aligned)
    (_h5 : g.session.receiverChains.length ≤ maxReceiverChains)
    (msg : SignalMessage) (hmsg : SignalMessage.tryFrom P.codec c = .ok msg)
    (x : GhostState Bytes × ℕ × ℕ × Bytes) (hx : P.receive g c rc = some x) :
    (EpochGhost.ofGhost g).recv msg.senderRatchetKey = (x.2.1, EpochGhost.ofGhost x.1) ∧
      x.2.2.1 = msg.counter.toNat + 1 ∧ x.1.party = g.party := by
  rw [Record.receive_eq_afterRecv, hmsg] at hx
  dsimp only at hx
  rcases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
      rc g.session with ⟨e | pt, s⟩
  · simp [hdec] at hx
  · rw [hdec] at hx
    simp only [Option.some.injEq] at hx
    subst hx
    rcases tryDecryptFromRecord_ok_ratchet P.C P.spqr (P.expectedAddrs g.party) msg .whisper
        rc g.session s pt hdec with ⟨ck, r1, mkg, r2, he, hc, hsrc⟩
    have hc_map := consumeMessageKey_map_senderRatchetKey P.C.F msg.senderRatchetKey ck
      msg.counter .whisper r1
    rw [hc] at hc_map
    have hmap2 : s.receiverChains.map (·.senderRatchetKey) =
        r1.receiverChains.map (·.senderRatchetKey) := by
      rw [hsrc, hc_map]
    have hlen_ks : (g.session.receiverChains.map (·.senderRatchetKey)).length =
        g.chainEpochs.length := by
      rw [List.length_map, hal.symm]
    refine ⟨?_, ?_, ?_⟩
    · unfold GhostState.afterRecv EpochGhost.recv EpochGhost.ofGhost
      dsimp only
      rcases hidx : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
        _ | i
      · have hidx_ks : (g.session.receiverChains.map (·.senderRatchetKey)).findIdx?
            (· == msg.senderRatchetKey) = none := by
          rw [findIdx?_map]
          exact hidx
        have hfind_none : ((g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs).find?
            (·.1 == msg.senderRatchetKey) = none :=
          find?_zip_of_findIdx?_none (· == msg.senderRatchetKey) _ _ hidx_ks
        have he_map := ensureReceiverChain_ok_none_map_senderRatchetKey P.C msg.senderRatchetKey
          rc _ r1 ck hidx he
        have hs_map : s.receiverChains.map (·.senderRatchetKey) =
            (g.session.receiverChains.map (·.senderRatchetKey) ++ [msg.senderRatchetKey]).drop
              ((g.session.receiverChains.length + 1) - maxReceiverChains) :=
          hmap2.trans he_map
        have hs_len : s.receiverChains.length =
            (g.session.receiverChains.length + 1) -
              ((g.session.receiverChains.length + 1) - maxReceiverChains) := by
          have := congrArg List.length hs_map
          simpa [List.length_drop, List.length_append, List.length_map] using this
        have hdrop_eq : (g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length =
            (g.session.receiverChains.length + 1) - maxReceiverChains := by
          have hce : g.chainEpochs.length = g.session.receiverChains.length := hal
          rw [List.length_append, List.length_singleton, hce, hs_len]
          omega
        have hcs_len : (((g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs) ++
            [(msg.senderRatchetKey, g.epoch + 1)]).length - maxReceiverChains =
            (g.session.receiverChains.length + 1) - maxReceiverChains := by
          have hce : g.chainEpochs.length = g.session.receiverChains.length := hal
          simp [List.length_append, List.length_zip, List.length_map, hce]
        simp only [hidx, hfind_none, hs_map, hdrop_eq, hcs_len, zip_drop,
          zip_append_singleton _ _ _ _ hlen_ks]
      · have hidx_ks : (g.session.receiverChains.map (·.senderRatchetKey)).findIdx?
            (· == msg.senderRatchetKey) = some i := by
          rw [findIdx?_map]
          exact hidx
        rcases find?_zip_of_findIdx?_some (· == msg.senderRatchetKey) _ _ i hlen_ks hidx_ks with
          ⟨k', hfind_some⟩
        have he_map := ensureReceiverChain_ok_some_map_senderRatchetKey P.C msg.senderRatchetKey
          rc _ r1 ck i hidx he
        have hs_map : s.receiverChains.map (·.senderRatchetKey) =
            g.session.receiverChains.map (·.senderRatchetKey) :=
          hmap2.trans he_map
        have hs_len : s.receiverChains.length = g.session.receiverChains.length := by
          have := congrArg List.length hs_map
          simpa [List.length_map] using this
        have hdrop_zero : g.chainEpochs.length - s.receiverChains.length = 0 := by
          have hce : g.chainEpochs.length = g.session.receiverChains.length := hal
          omega
        simp only [hidx, hfind_some, hs_map, hdrop_zero, List.drop_zero]
    · unfold GhostState.afterRecv
      rcases g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) <;> rfl
    · unfold GhostState.afterRecv
      rcases g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) <;> rfl

private theorem addrsE_length' (s r : Party) (a : List (BitVec 8))
    (h : serializedPartyAddresses uuidTryParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : serviceIdParse uuidTryParse (utf8 (partyAddressName s)) <;>
    cases hr : serviceIdParse uuidTryParse (utf8 (partyAddressName r)) <;> simp_all [addrBytes]
  subst h
  simp

/-- Wire-length bound (`< 2 ^ 32` bytes) for `Params.send` on plaintexts of length `< 2 ^ 31`,
provided `S.send` emits a `pq_ratchet` payload of at most `2 ^ 30` bytes. -/
theorem send_wire_len_gen {PQC : Type} (C : Crypto) (S : Spqr Bytes PQC) (ℓ : ℕ)
    (hℓ : ℓ < 2 ^ 31) (g : GhostState Bytes) (m : Bytes) (hm : m.length = ℓ) (r : PQC)
    (hpm : ∀ pq' key pm, S.send g.session.pqRatchetState r = some (pq', key, pm) →
      pm.length ≤ 2 ^ 30) :
    ((sessionParamsForSpqr C S).send g m r).2.length < 2 ^ 32 := by
  simp only [Params.send]
  rcases he : SessionState.messageEncrypt (sessionParamsForSpqr C S).C (sessionParamsForSpqr C S).codec
      (sessionParamsForSpqr C S).spqr ((sessionParamsForSpqr C S).sendAddrs g.party) m r g.session with ⟨e | msg, s⟩
  · simp
  · dsimp only
    unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
      SessionState.takePqRatchetState at he
    rcases hsc : g.session.senderChain with _ | sc
    · simp [hsc] at he
    · simp only [hsc, exec_bind, exec_get, exec_modifyGet] at he
      split_ifs at he
      · simp at he
      · rcases hrem : g.session.remoteIdentity with _ | remote
        · simp [hrem] at he
        · simp only [hrem, exec_pure] at he
          rw [show (sessionParamsForSpqr C S).C = C from rfl,
            show (sessionParamsForSpqr C S).codec = protoSignalCodec from rfl,
            show (sessionParamsForSpqr C S).spqr = S from rfl] at he
          unfold OutgoingTripleRatchet.encrypt at he
          simp only [exec_bind, exec_get] at he
          cases hpan : S.sendPanics g.session.pqRatchetState r
          case true => simp [hpan] at he
          simp only [hpan, Bool.false_eq_true, ↓reduceIte] at he
          rcases hs : S.send g.session.pqRatchetState r with _ | ⟨pq', key, pm⟩
          · simp [hs] at he
          · have hpmlen := hpm pq' key pm hs
            simp only [hs] at he
            rcases hn : sc.chainKey.nextChainKey C.F with _ | next
            · simp [hn] at he
            · simp only [hn, exec_bind, exec_liftE, exec_set, exec_pure, Prod.mk.injEq,
                Except.ok.injEq] at he
              rcases he with ⟨rfl, _⟩
              have hvar : ∀ k v, (encodeVarintAux k v).length ≤ k := by
                intro k; induction k with
                | zero => simp [encodeVarintAux]
                | succ k ih =>
                  intro v; simp only [encodeVarintAux]
                  split
                  · simp
                  · simp only [List.length_cons]; have := ih (v >>> 7); omega
              have hu32 : ∀ tag v, (encodeUint32Field tag v).length ≤ 20 := by
                intro tag v; cases v with
                | none => simp [encodeUint32Field]
                | some v =>
                  simp only [encodeUint32Field, List.length_append]
                  have h1 := hvar 10 (BitVec.ofNat 64 (tag * 8 + WireType.varint.toNat))
                  have h2 := hvar 10 (v.zeroExtend 64)
                  unfold encodeKey encodeVarint at *; omega
              have hbf : ∀ tag bs, (encodeBytesField tag (some bs)).length ≤ 20 + bs.length := by
                intro tag bs
                simp only [encodeBytesField, List.length_append]
                have h1 := hvar 10 (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
                have h2 := hvar 10 (BitVec.ofNat 64 bs.length)
                unfold encodeKey encodeVarint at *; omega
              have hblk : ∀ l : List (BitVec 128),
                  (l.flatMap CBC.blockToBytesLE).length = 16 * l.length := by
                intro l; induction l with
                | nil => rfl
                | cons b t ih =>
                  have hb : (CBC.blockToBytesLE b).length = 16 := by simp [CBC.blockToBytesLE]
                  simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, hb]; omega
              have hct : ∀ k iv,
                  (aesCbcEncrypt C.E k iv m).length = 16 * (ℓ / 16 + 1) := by
                intro k iv
                unfold aesCbcEncrypt
                rw [hblk, List.Vector.toList_length, hm]
                rfl
              have had6 : (encodeBytesField 6
                  (g.session.encryptAddresses ((sessionParamsForSpqr C S).sendAddrs g.party))).length ≤ 56 := by
                unfold SessionState.encryptAddresses sessionParamsForSpqr Params.sendAddrs
                split_ifs
                · cases hp : g.party <;>
                  · dsimp only
                    cases hs : serializedPartyAddresses uuidTryParse _ _ with
                    | none => simp [encodeBytesField]
                    | some ad =>
                      have h1 := hbf 6 ad
                      have h2 := addrsE_length' _ _ ad hs
                      omega
                · simp [encodeBytesField]
              have hrk : sc.ratchetKey.publicKey.serialize.length = 33 := by
                simp [PublicKey.serialize]
              have h5 : (encodeBytesField 5 (if pm.isEmpty then none else some pm)).length ≤
                  20 + pm.length := by
                split
                · simp [encodeBytesField]
                · exact hbf 5 pm
              have hnew : ∀ v k ad rk cnt prev ct s1 r1,
                  (SignalMessage.new C.F protoSignalCodec v k ad rk cnt prev ct s1 r1 pm).serialized.length ≤
                    1 + (encodeBytesField 1 (some rk.serialize)).length +
                    (encodeUint32Field 2 (some cnt)).length +
                    (encodeUint32Field 3 (some prev)).length +
                    (encodeBytesField 4 (some ct)).length +
                    (encodeBytesField 5 (if pm.isEmpty then none else some pm)).length +
                    (encodeBytesField 6 ad).length + 8 := by
                intro v k ad rk cnt prev ct s1 r1
                dsimp only [SignalMessage.new]
                rw [List.length_append]
                have hm8 : (computeMac C.F s1 r1 k
                    (serializeContent protoSignalCodec v rk cnt prev ct pm ad)).length ≤ 8 :=
                  List.length_take_le 8 _
                refine Nat.le_trans (Nat.add_le_add_left hm8 _) ?_
                dsimp only [serializeContent, protoSignalCodec,
                  CryptoVerification.LibsignalProtoCodec.encode]
                simp only [List.length_append, List.length_cons]
                omega
              refine Nat.lt_of_le_of_lt (hnew _ _ _ _ _ _ _ _ _) ?_
              have h1 := hbf 1 sc.ratchetKey.publicKey.serialize
              have h2 := hu32 2 (some sc.chainKey.index)
              have h3 := hu32 3 (some g.session.previousCounter)
              have h4 := hbf 4 (aesCbcEncrypt C.E
                ((sc.chainKey.messageKeys C.F).generateKeys C.F key).cipherKey
                ((sc.chainKey.messageKeys C.F).generateKeys C.F key).iv m)
              have h4' := hct
                ((sc.chainKey.messageKeys C.F).generateKeys C.F key).cipherKey
                ((sc.chainKey.messageKeys C.F).generateKeys C.F key).iv
              omega

/-! ## Specializations to `spqrOffB` -/

theorem messageEncrypt_ok_props_spqrOffB (C : Crypto) (codec : SignalMessageProtoCodec)
    (addresses : Option Bytes) (ptext : Bytes) (coins : Unit) (st st' : SessionState Bytes)
    (msg : SignalMessage) (hseeds : SeedsLen32 st)
    (hlen : st.receiverChains.length ≤ maxReceiverChains)
    (h : SessionState.messageEncrypt C codec CryptoVerification.E2E.spqrOffB addresses ptext
      coins st = (.ok msg, st')) :
    SeedsLen32 st' ∧ st'.receiverChains.length ≤ maxReceiverChains ∧ st'.pqRatchetState = [] ∧
      st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity := by
  obtain ⟨hs, hl, hloc, hrem, key, pm, hsend, -⟩ :=
    messageEncrypt_ok_props_gen C codec _ addresses ptext coins st st' msg hseeds hlen h
  simp only [CryptoVerification.E2E.spqrOffB, Option.some.injEq, Prod.mk.injEq] at hsend
  exact ⟨hs, hl, hsend.1.symm, hloc, hrem⟩

theorem tr_decrypt_ok_props_spqrOffB (C : Crypto) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (t t' : TripleRatchet Bytes) (pt : Bytes)
    (hlen : t.ratchet.receiverChains.length ≤ maxReceiverChains)
    (h : Mut.exec (TripleRatchet.decrypt C CryptoVerification.E2E.spqrOffB expected m msgType
      coins) t = (.ok pt, t')) :
    t'.ratchet.receiverChains.length ≤ maxReceiverChains ∧ t'.pqrState = [] := by
  obtain ⟨hl, key, hrecv⟩ := tr_decrypt_ok_props_gen C _ expected m msgType coins t t' pt hlen h
  have := spqrRecvEmpty_ok_eq hrecv
  simp only [Prod.mk.injEq] at this
  exact ⟨hl, this.1⟩

theorem tryDecryptFromRecord_ok_props_spqrOffB (C : Crypto) (expected : Option Bytes)
    (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState Bytes) (pt : Bytes) (hseeds : SeedsLen32 st)
    (hlen : st.receiverChains.length ≤ maxReceiverChains)
    (h : SessionState.tryDecryptFromRecord C CryptoVerification.E2E.spqrOffB expected m msgType
      coins st = (.ok pt, st')) :
    SeedsLen32 st' ∧ st'.receiverChains.length ≤ maxReceiverChains ∧ st'.pqRatchetState = [] ∧
      st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity := by
  obtain ⟨hs, hl, hloc, hrem, key, hrecv⟩ :=
    tryDecryptFromRecord_ok_props_gen C _ expected m msgType coins st st' pt hseeds hlen h
  have := spqrRecvEmpty_ok_eq hrecv
  simp only [Prod.mk.injEq] at this
  exact ⟨hs, hl, this.1, hloc, hrem⟩

theorem send_wire_len_spqrOffB (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 2 ^ 31) (g : GhostState Bytes)
    (m : Bytes) (hm : m.length = ℓ) (r : Unit) :
    ((spqrOffSessionParams C).send g m r).2.length < 2 ^ 32 := by
  rw [← paramsEWith_spqrOffB]
  refine send_wire_len_gen C _ ℓ hℓ g m hm r ?_
  intro pq' key pm hs
  simp only [CryptoVerification.E2E.spqrOffB, Option.some.injEq, Prod.mk.injEq] at hs
  rw [← hs.2.2]
  simp

end CryptoVerification.E2E.V1
