/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1B
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins

/-!
# Hop 2 Receiver-Chain Helpers and Lazy Pre-Sampling

Proves receive-coin irrelevance on `steppedSessBase`, receiver-chain freshness helpers
(`NoKeyInChains`, `hop2OffChainOut`), and fresh pre-sampling absorption for `runHop2`
(`evalDist_runHop2_lazy_cons_fresh`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

set_option linter.unusedSectionVars false

section Hop2Coupling

open CryptoGames.CKA CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF MACScheme

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}

/-! ## Stepped-session receive-coin irrelevance -/

theorem tryDecryptFromRecord_steppedSessBase_rc_irrel (P : Params PQ PQC)
    (g : GhostState PQ) (msg : SignalMessage) (rc : BitVec 256)
    (prev : BitVec 32) (ckR : BitVec 256)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
        none) :
    SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc (steppedSessBase g msg prev ckR) =
    SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper 0 (steppedSessBase g msg prev ckR) := by
  set base := steppedSessBase g msg prev ckR
  have hdec1 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc base
  have hdec2 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper 0 base
  rw [hdec1, hdec2]
  split_ifs with hv
  · rfl
  · cases base.remoteIdentity with
    | none => rfl
    | some rem =>
      dsimp only []
      set r0 : RatchetState :=
        ⟨base.rootKey, base.senderChain, base.receiverChains, base.previousCounter, maxForwardJumps⟩
      have hens1 : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc) r0 =
          (.ok ⟨ckR, 0⟩, r0) :=
        exec_ensureReceiverChain_evict_append P.C
          ⟨0, none, g.session.receiverChains, prev, maxForwardJumps⟩
          msg.senderRatchetKey ⟨ckR, 0⟩ rc hnone
      have hens0 : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey 0) r0 =
          (.ok ⟨ckR, 0⟩, r0) :=
        exec_ensureReceiverChain_evict_append P.C
          ⟨0, none, g.session.receiverChains, prev, maxForwardJumps⟩
          msg.senderRatchetKey ⟨ckR, 0⟩ 0 hnone
      have hrat :
          Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc) r0 =
          Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper 0) r0 := by
        unfold ratchetDecryptStep
        rw [Mut_exec_bind, Mut_exec_bind, hens1, hens0]
      rw [hrat]

theorem hop2BadAt_eq_false_of_senderRatchetKey_ne (P : Params Bytes PQC) (s : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (msg : SignalMessage)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hne : msg.senderRatchetKey ≠ (KeyPair.generate P.C s).publicKey) :
    hop2BadAt P s g c = false := by
  unfold hop2BadAt
  rw [htry]
  have hbeq : (msg.senderRatchetKey == (KeyPair.generate P.C s).publicKey) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp [hbeq]

theorem hop2BadAt_eq_false_of_party_B (P : Params Bytes PQC) (s : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (hp : g.party = .B) :
    hop2BadAt P s g c = false := by
  unfold hop2BadAt
  simp [hp]

theorem hop2BadAt_eq_false_of_pos_epochs (P : Params Bytes PQC) (s : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (hpos : ∀ e ∈ g.chainEpochs, 0 < e) :
    hop2BadAt P s g c = false := by
  unfold hop2BadAt
  have hno0 : 0 ∉ g.chainEpochs := fun h0 => by
    have := hpos 0 h0
    omega
  simp [hno0]

/-! ## Session and receiver-chain helpers -/

/-- No receiver chain in `cs` has `senderRatchetKey = k`. -/
def NoKeyInChains (k : PublicKey) (cs : List ReceiverChain) : Prop :=
  ∀ c ∈ cs, c.senderRatchetKey ≠ k

theorem findIdx?_eq_none_of_noKeyInChains (k : PublicKey) (cs : List ReceiverChain)
    (h : NoKeyInChains k cs) :
    cs.findIdx? (·.senderRatchetKey == k) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro c hc
  exact beq_eq_false_iff_ne.mpr (h c hc)

theorem noKeyInChains_set (k : PublicKey) (cs : List ReceiverChain) (idx : ℕ)
    (c c' : ReceiverChain) (h : NoKeyInChains k cs)
    (hget : cs[idx]? = some c) (hk : c'.senderRatchetKey = c.senderRatchetKey) :
    NoKeyInChains k (cs.set idx c') := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hmem | rfl
  · exact h x hmem
  · rw [hk]
    exact h c (List.mem_of_getElem? hget)

theorem takeSkippedKey_noKeyInChains (k their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) (h : NoKeyInChains k r.receiverChains) :
    NoKeyInChains k (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains := by
  unfold RatchetState.takeSkippedKey
  rw [Mut_exec_bind, Mut_exec_get]
  dsimp only []
  cases r.findReceiverChainIndex their with
  | none => exact h
  | some idx =>
    dsimp only []
    cases hget : r.receiverChains[idx]? with
    | none => exact h
    | some c =>
      dsimp only []
      cases c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
      | none => exact h
      | some pos =>
        dsimp only []
        cases c.messageKeys[pos]? with
        | none => exact h
        | some key =>
          rw [Mut_exec_bind, Mut_exec_set]
          exact noKeyInChains_set k r.receiverChains idx c _ h hget rfl

theorem storeSkippedKey_noKeyInChains (k their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) (h : NoKeyInChains k r.receiverChains) :
    NoKeyInChains k (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains := by
  unfold RatchetState.storeSkippedKey
  rw [Mut_exec_bind, Mut_exec_get]
  dsimp only []
  cases r.findReceiverChainIndex their with
  | none => exact h
  | some idx =>
    dsimp only []
    cases hget : r.receiverChains[idx]? with
    | none => exact h
    | some c =>
      rw [Mut_exec_set]
      exact noKeyInChains_set k r.receiverChains idx c _ h hget rfl

theorem setReceiverChainKey_noKeyInChains (k their : PublicKey) (ck : LibsignalSession.ChainKey)
    (r : RatchetState) (h : NoKeyInChains k r.receiverChains) :
    NoKeyInChains k (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains := by
  unfold RatchetState.setReceiverChainKey
  rw [Mut_exec_bind, Mut_exec_get]
  dsimp only []
  cases r.findReceiverChainIndex their with
  | none => exact h
  | some idx =>
    dsimp only []
    cases hget : r.receiverChains[idx]? with
    | none => exact h
    | some c =>
      rw [Mut_exec_set]
      exact noKeyInChains_set k r.receiverChains idx c _ h hget rfl

theorem advanceChain_noKeyInChains (F : ShaState → List (BitVec 8) → ShaState)
    (k their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck : LibsignalSession.ChainKey) (r : RatchetState),
      NoKeyInChains k r.receiverChains →
      NoKeyInChains k (Mut.exec (RatchetState.advanceChain F their counter fuel ck)
          r).2.receiverChains
  | 0, ck, r, h => h
  | fuel + 1, ck, r, h => by
    unfold RatchetState.advanceChain
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, Mut_exec_bind]
      have hst := storeSkippedKey_noKeyInChains k their (ck.messageKeys F) r h
      rcases h_st : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with ⟨r_st,
          s_st⟩
      rw [h_st] at hst
      cases r_st with
      | error _ => exact hst
      | ok _ =>
        dsimp only []
        cases ck.nextChainKey F with
        | error _ =>
          simp only [Mut_exec_liftE]
          exact hst
        | ok ck' =>
          simp only [Mut_exec_liftE]
          exact advanceChain_noKeyInChains F k their counter fuel ck' s_st hst
    · simp only [hlt, ↓reduceIte, Mut_exec_pure]
      exact h

theorem consumeMessageKey_noKeyInChains (F : ShaState → List (BitVec 8) → ShaState)
    (k their : PublicKey) (ck : LibsignalSession.ChainKey) (counter : BitVec 32)
    (msgType : MessageType) (r : RatchetState) (h : NoKeyInChains k r.receiverChains) :
    NoKeyInChains k
      (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains :=
          by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, Mut_exec_bind]
    have htk := takeSkippedKey_noKeyInChains k their counter r h
    rcases h_tk : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨r_tk, s_tk⟩
    rw [h_tk] at htk
    cases r_tk with
    | error _ => exact htk
    | ok optK =>
      cases optK <;> simp only [Mut_exec_pure] <;> exact htk
  · simp only [hlt, ↓reduceIte, Mut_exec_bind, Mut_exec_get]
    by_cases hj : r.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hj, ↓reduceIte, Mut_exec_throw, Mut_exec_bind]
      exact h
    · simp only [hj, ↓reduceIte, Mut_exec_pure, Mut_exec_bind]
      have hadv := advanceChain_noKeyInChains F k their counter (counter - ck.index).toNat ck r h
      rcases h_adv :
          Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨r_adv, s_adv⟩
      rw [h_adv] at hadv
      cases r_adv with
      | error _ => exact hadv
      | ok ckOut =>
        dsimp only []
        cases ckOut.nextChainKey F with
        | error _ =>
          simp only [Mut_exec_liftE]
          exact hadv
        | ok ckNext =>
          simp only [Mut_exec_liftE]
          have hset := setReceiverChainKey_noKeyInChains k their ckNext s_adv hadv
          rcases h_set :
              Mut.exec (RatchetState.setReceiverChainKey their ckNext) s_adv with ⟨r_set, s_set⟩
          rw [h_set] at hset
          cases r_set <;> exact hset

theorem noKeyInChains_evict_append (k their : PublicKey) (cs : List ReceiverChain)
    (ck : Option LibsignalSession.ChainKey) (mks : List MessageKeyGenerator)
    (h : NoKeyInChains k cs) (hne : their ≠ k) :
    NoKeyInChains k (RatchetState.evictReceiverChains (cs ++ [⟨their, ck, mks⟩])) := by
  intro x hx
  have hmem := mem_of_mem_drop _ _ _ hx
  rw [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl
  · exact h x hmem
  · exact hne

def hop2OffChainOut (P : Params Bytes PQC) (ℓ : ℕ) (g : GhostState Bytes)
    (msg : SignalMessage) (sc : SenderChain) (rc u : BitVec 256) : Hop2Out Pt ℓ :=
  let (rk', ckR) := Ratchet.rootExpand P.C.F (keyToBytes32 u)
  let newKey := KeyPair.generate P.C rc
  match rootCreateChain P.C rk' msg.senderRatchetKey newKey.privateKey with
  | .error _ => none
  | .ok (rk2, ck2) =>
    let cur := sc.chainKey.index
    let sess' : SessionState Bytes :=
      { g.session with
        previousCounter := if cur = 0 then 0 else cur - 1
        rootKey := rk2
        receiverChains := RatchetState.evictReceiverChains
          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
        senderChain := some ⟨newKey, ⟨ck2.key, 0⟩⟩ }
    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
        rc sess' with
    | (.error _, _) => none
    | (.ok m, s_out) =>
      let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
        ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
      some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
        g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨none, rc, none⟩)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2OffChainOut_eq_none_of_testSpk_false (P : Params Bytes PQC) (ℓ : ℕ)
    (g : GhostState Bytes) (c : Bytes) (msg : SignalMessage) (sc : SenderChain)
    (rc u : BitVec 256)
    (hparty : g.party = .A)
    (hrem : g.session.remoteIdentity = some P.idB)
    (hloc : g.session.localIdentity = P.idA)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (htest : testSpk P g.session.pqRatchetState c ((Ratchet.expandPRG P.C.F).gen u).2 = false) :
    hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u = none := by
  unfold hop2OffChainOut
  dsimp only []
  cases rootCreateChain P.C (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
      msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
  | error _ => rfl
  | ok p2 =>
    rcases p2 with ⟨rk2, ck2⟩
    dsimp only []
    obtain ⟨e, s_out, hdec⟩ := tryDecryptFromRecord_stepped_error_of_testSpk_false P g c msg rc
      (if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1)
      rk2 (Ratchet.rootExpand P.C.F (keyToBytes32 u)).2
      (some ⟨KeyPair.generate P.C rc, ⟨ck2.key, 0⟩⟩)
      hparty hrem hloc htry hnone htest
    rw [hdec]

theorem tryDecryptFromRecord_existing_props (P : Params Bytes PQC)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (idx : ℕ) (m : Bytes) (s_out : SessionState Bytes)
    (hfind : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
        some idx)
    (hok : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc g.session = (.ok m, s_out)) :
    s_out.remoteIdentity = g.session.remoteIdentity ∧
    s_out.localIdentity = g.session.localIdentity ∧
    s_out.receiverChains.length = g.session.receiverChains.length ∧
    (∀ pk, NoKeyInChains pk g.session.receiverChains → NoKeyInChains pk s_out.receiverChains) := by
  rw [tryDecryptFromRecord_eq] at hok
  split_ifs at hok with hv
  · cases hok
  · cases hrem : g.session.remoteIdentity with
    | none => rw [hrem] at hok; cases hok
    | some rem =>
      rw [hrem] at hok
      dsimp only [] at hok
      rcases hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
         g.session.previousCounter, maxForwardJumps⟩ with ⟨r_rat, r'⟩
      rw [hrat] at hok
      cases r_rat with
      | error _ => cases hok
      | ok gen =>
        dsimp only [] at hok
        have hpost := ((postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper g.session rem gen r' g.session.receiverChains r'.receiverChains).2 m s_out
              hok).2
        have hlen := (ratchetDecryptStep_length P.C msg.senderRatchetKey msg.counter .whisper rc
          _ r' gen hrat).1 idx hfind
        refine ⟨hpost.1.trans hrem, hpost.2.1, (congrArg List.length hpost.2.2).trans hlen.1, ?_⟩
        intro pk hno
        rw [hpost.2.2]
        unfold ratchetDecryptStep RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
            at hrat
        simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_liftE] at hrat
        change _ at hfind
        rw [show (RatchetState.findReceiverChainIndex
          ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
           g.session.previousCounter, maxForwardJumps⟩ msg.senderRatchetKey) =
               some idx from hfind] at hrat
        dsimp only [] at hrat
        cases hget : g.session.receiverChains[idx]? with
        | none => rw [hget] at hrat; simp [] at hrat
        | some ch =>
          rw [hget] at hrat
          dsimp only [] at hrat
          cases hck : ch.chainKey with
          | none => rw [hck] at hrat; simp [] at hrat
          | some ck0 =>
            rw [hck] at hrat
            simp only [Mut_exec_pure] at hrat
            have hcmk := consumeMessageKey_noKeyInChains P.C.F pk msg.senderRatchetKey ck0
              msg.counter .whisper
              ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
               g.session.previousCounter, maxForwardJumps⟩ hno
            rw [hrat] at hcmk
            exact hcmk

theorem tryDecryptFromRecord_stepped_props (P : Params Bytes PQC)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (prev : BitVec 32) (rk2 : Ratchet.RootKey) (ckR : BitVec 256) (sc' : Option SenderChain)
    (m : Bytes) (s_out : SessionState Bytes)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (hok : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
      { g.session with
        previousCounter := prev
        rootKey := rk2
        receiverChains := RatchetState.evictReceiverChains
          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
        senderChain := sc' } = (.ok m, s_out)) :
    s_out.remoteIdentity = g.session.remoteIdentity ∧
    s_out.localIdentity = g.session.localIdentity ∧
    s_out.receiverChains.length =
      (RatchetState.evictReceiverChains
        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])).length ∧
    (∀ pk, NoKeyInChains pk g.session.receiverChains → msg.senderRatchetKey ≠ pk →
      NoKeyInChains pk s_out.receiverChains) := by
  set sess' : SessionState Bytes :=
    { g.session with
      previousCounter := prev
      rootKey := rk2
      receiverChains := RatchetState.evictReceiverChains
        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
      senderChain := sc' }
  rw [tryDecryptFromRecord_eq] at hok
  split_ifs at hok with hv
  · cases hok
  · cases hrem : sess'.remoteIdentity with
    | none => rw [hrem] at hok; cases hok
    | some rem =>
      rw [hrem] at hok
      dsimp only [] at hok
      set r_stepped : RatchetState :=
        ⟨rk2, sc',
         RatchetState.evictReceiverChains
           (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩]),
         prev, maxForwardJumps⟩
      rcases hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        r_stepped with ⟨r_rat, r'⟩
      change (match Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
          r_stepped with
        | (.error e, _) => _
        | (.ok gen, r') => _) = _ at hok
      rw [hrat] at hok
      cases r_rat with
      | error _ => cases hok
      | ok gen =>
        dsimp only [] at hok
        have hpost := ((postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper sess' rem gen r' sess'.receiverChains r'.receiverChains).2 m s_out hok).2
        have hens : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
            r_stepped = (.ok ⟨ckR, 0⟩, r_stepped) :=
          exec_ensureReceiverChain_evict_append P.C
            ⟨rk2, sc', g.session.receiverChains, prev, maxForwardJumps⟩
            msg.senderRatchetKey ⟨ckR, 0⟩ rc hnone
        unfold ratchetDecryptStep at hrat
        rw [Mut_exec_bind, hens] at hrat
        dsimp only [] at hrat
        have hcmk_len := consumeMessageKey_length P.C.F msg.senderRatchetKey ⟨ckR, 0⟩
          msg.counter .whisper r_stepped
        rw [hrat] at hcmk_len
        refine ⟨hpost.1.trans hrem, hpost.2.1, (congrArg List.length hpost.2.2).trans hcmk_len, ?_⟩
        intro pk hno hne
        rw [hpost.2.2]
        have hno_stepped : NoKeyInChains pk r_stepped.receiverChains :=
          noKeyInChains_evict_append pk msg.senderRatchetKey g.session.receiverChains
            (some ⟨ckR, 0⟩) [] hno hne
        have hcmk_no := consumeMessageKey_noKeyInChains P.C.F pk msg.senderRatchetKey ⟨ckR, 0⟩
          msg.counter .whisper r_stepped hno_stepped
        rw [hrat] at hcmk_no
        exact hcmk_no

/-! ## Lazy-table pre-sampling for `runHop2` -/

abbrev Hop2State (Pt : Type) (ℓ : ℕ) : Type :=
  SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt

def withLazy {ℓ : ℕ} (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ) : Hop2State Pt ℓ :=
  (st.1, { st.2 with lazy := l })

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp]
theorem withLazy_withLazy {ℓ : ℕ} (l₁ l₂ : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ) :
    withLazy l₁ (withLazy l₂ st) = withLazy l₁ st := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp]
theorem withLazy_self {ℓ : ℕ} (st : Hop2State Pt ℓ) :
    withLazy st.2.lazy st = st := rfl


omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem stateT_lift_run_hop2 {ℓ : ℕ} {α : Type}
    (m : Hop2Comp Pt α) (st : Hop2State Pt ℓ) :
    (StateT.lift m : Hop2M Pt ℓ α).run st = (do let a ← m; return (a, st)) := rfl

def hop2LazyKey {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (h : Hop2Hyb Pt)
    (g : GhostState Bytes) (c : Bytes) (st : Hop2State Pt ℓ) :
    Option ((ℕ × Pt) × SignalMessage × SenderChain) :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => none
  | .ok msg =>
    match st.2.idx g.party with
    | none => none
    | some t =>
      if (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone
          then
        match decT msg.senderRatchetKey with
        | none => none
        | some T =>
          if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none
          else
            match g.session.senderChain with
            | none => none
            | some sc =>
              let Q := Dh.dh (st.2.coins g.party) T
              if Q = 0 then none
              else if t ≤ h.k then
                match st.2.made.lookup (t, Q) with
                | some _ => none
                | none => some ((t, Q), msg, sc)
              else none
      else none

omit [SampleableType Pt] in
@[simp]
theorem hop2LazyKey_withLazy {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (h : Hop2Hyb Pt)
    (g : GhostState Bytes) (c : Bytes) (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ) :
    hop2LazyKey P Dh encT decT h g c (withLazy l st) = hop2LazyKey P Dh encT decT h g c st := rfl

omit [SampleableType Pt] in
theorem hop2Recv_run_of_hop2LazyKey_some {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ)
    (tq : ℕ × Pt) (msg : SignalMessage) (sc : SenderChain)
    (hkey : hop2LazyKey P Dh encT decT h g c st = some (tq, msg, sc)) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run (withLazy l st) =
      (fun r => (hop2OffChainOut P ℓ g msg sc rc r.1, r.2)) <$>
        (hop2Lazy tq.1 tq.2).run (withLazy l st) := by
  unfold hop2LazyKey at hkey
  unfold hop2Recv hop2DH hop2RecvHalf hop2SendHalf hop2OffChainOut
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hkey; cases hkey
  | ok msg' =>
    rw [htry] at hkey
    dsimp only [] at hkey ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hidx1 : (withLazy l st).2.idx g.party = st.2.idx g.party := rfl
    rw [hidx1]
    cases hidx : st.2.idx g.party with
    | none => rw [hidx] at hkey; cases hkey
    | some t =>
      rw [hidx] at hkey
      dsimp only [] at hkey ⊢
      by_cases hfind :
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg'.senderRatchetKey)).isNone =
          true
      · simp only [hfind, ↓reduceIte] at hkey ⊢
        cases hdec : decT msg'.senderRatchetKey with
        | none => rw [hdec] at hkey; cases hkey
        | some T =>
          rw [hdec] at hkey
          dsimp only [] at hkey ⊢
          by_cases hT : T = 0 ∨ encT T ≠ msg'.senderRatchetKey
          · simp only [hT, ↓reduceIte] at hkey; cases hkey
          · simp only [hT, ↓reduceIte] at hkey ⊢
            cases hsc : g.session.senderChain with
            | none => rw [hsc] at hkey; cases hkey
            | some sc' =>
              rw [hsc] at hkey
              dsimp only [] at hkey ⊢
              have hcoins : (withLazy l st).2.coins g.party = st.2.coins g.party := rfl
              rw [hcoins]
              by_cases hQ0 : Dh.dh (st.2.coins g.party) T = 0
              · simp only [hQ0, ↓reduceIte] at hkey; cases hkey
              · simp only [hQ0, ↓reduceIte] at hkey ⊢
                by_cases htle : t ≤ h.k
                · simp only [htle, ↓reduceIte] at hkey ⊢
                  cases hmade : st.2.made.lookup (t, Dh.dh (st.2.coins g.party) T) with
                  | some _ => rw [hmade] at hkey; cases hkey
                  | none =>
                    rw [hmade] at hkey
                    injection hkey with htuple
                    rcases Prod.mk.inj htuple with ⟨htq, hrest⟩
                    rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
                    subst htq
                    have hmade' : (withLazy l st).2.made.lookup (t,
                        Dh.dh (st.2.coins g.party) T) = none := hmade
                    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure,
                        stateT_lift_run_hop2,
                      map_eq_bind_pure_comp, bind_assoc, pure_bind, hmade']
                    refine bind_congr fun r => ?_
                    dsimp only [Function.comp_apply]
                    cases rootCreateChain P.C (Ratchet.rootExpand P.C.F (keyToBytes32 r.1)).1
                      msg'.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
                    | error _ => simp [StateT.run_pure]
                    | ok p2 =>
                      rcases p2 with ⟨rk2, ck2⟩
                      simp only [pure_bind]
                      rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
                        msg' .whisper rc _ with ⟨r_tr, s_out⟩
                      cases r_tr <;> simp [StateT.run_pure]
                · simp only [htle, ↓reduceIte] at hkey; cases hkey
      · simp only [hfind, Bool.false_eq_true, ↓reduceIte] at hkey; cases hkey

omit [SampleableType Pt] in
theorem hop2Recv_run_of_hop2LazyKey_none {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ)
    (hkey : hop2LazyKey P Dh encT decT h g c st = none) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run (withLazy l st) =
      (fun r => (r.1, withLazy l st)) <$>
        (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run (withLazy [] st) := by
  unfold hop2LazyKey at hkey
  unfold hop2Recv hop2DH hop2RecvHalf
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => simp [StateT.run_pure]
  | ok msg =>
    rw [htry] at hkey
    dsimp only [] at hkey ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hidx1 : (withLazy l st).2.idx g.party = st.2.idx g.party := rfl
    have hidx2 : (withLazy [] st).2.idx g.party = st.2.idx g.party := rfl
    rw [hidx1, hidx2]
    cases hidx : st.2.idx g.party with
    | none => simp [StateT.run_pure]
    | some t =>
      rw [hidx] at hkey
      dsimp only [] at hkey ⊢
      by_cases hfind :
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
          true
      · simp only [hfind, ↓reduceIte] at hkey ⊢
        cases hdec : decT msg.senderRatchetKey with
        | none => simp [StateT.run_pure]
        | some T =>
          rw [hdec] at hkey
          dsimp only [] at hkey ⊢
          by_cases hT : T = 0 ∨ encT T ≠ msg.senderRatchetKey
          · simp [hT, StateT.run_pure]
          · simp only [hT, ↓reduceIte] at hkey ⊢
            cases hsc : g.session.senderChain with
            | none => simp [StateT.run_pure]
            | some sc =>
              rw [hsc] at hkey
              dsimp only [] at hkey ⊢
              have hc1 : (withLazy l st).2.coins g.party = st.2.coins g.party := rfl
              have hc2 : (withLazy [] st).2.coins g.party = st.2.coins g.party := rfl
              rw [hc1, hc2]
              by_cases hQ0 : Dh.dh (st.2.coins g.party) T = 0
              · simp [hQ0, StateT.run_pure]
              · simp only [hQ0, ↓reduceIte] at hkey ⊢
                by_cases htle : t ≤ h.k
                · simp only [htle, ↓reduceIte] at hkey ⊢
                  have hm1 : (withLazy l st).2.made = st.2.made := rfl
                  have hm2 : (withLazy [] st).2.made = st.2.made := rfl
                  simp only [StateT.run_bind, StateT.run_get, pure_bind, hm1, hm2]
                  cases hmade : st.2.made.lookup (t, Dh.dh (st.2.coins g.party) T) with
                  | none => rw [hmade] at hkey; cases hkey
                  | some ck =>
                    simp only [StateT.run_bind, StateT.run_pure, stateT_lift_run_hop2,
                      map_eq_bind_pure_comp, bind_assoc, pure_bind]
                    refine bind_congr fun r2 => ?_
                    cases r2 with
                    | none => simp [StateT.run_pure]
                    | some p2 =>
                      rcases p2 with ⟨idx2, rk2, ckS, pend⟩
                      dsimp only []
                      rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
                        msg .whisper rc _ with ⟨r_tr, s_out⟩
                      cases r_tr <;> simp [StateT.run_pure]
                · simp only [htle, ↓reduceIte, StateT.run_bind,
                    stateT_lift_run_hop2,
                    map_eq_bind_pure_comp, bind_assoc, pure_bind]
                  refine bind_congr fun u => ?_
                  refine bind_congr fun r2 => ?_
                  cases r2 with
                  | none => simp [StateT.run_pure]
                  | some p2 =>
                    rcases p2 with ⟨idx2, rk2, ckS, pend⟩
                    dsimp only []
                    rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
                      msg .whisper rc _ with ⟨r_tr, s_out⟩
                    cases r_tr <;> simp [StateT.run_pure]
      · simp [hfind, StateT.run_pure]

def hop2DeliverPost {ℓ : ℕ} (P : Params Bytes PQC) (s : BitVec 256)
    (Q : Party) (c : Bytes) (g₀ : GhostState Bytes) (r : SM.Record (CBC.Plain ℓ) Bytes)
    (o : Hop2Out Pt ℓ) (st2 : Hop2State Pt ℓ) :
    Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ :=
  match o with
  | none => (some .rejected, st2)
  | some ((st', t', i', m'), u) =>
    (some (.accepted t' i' (if st2.1.chall.contains r.pos then none else some m')),
      (st2.1.accept Q st' r.pos,
        { hop2Commit st2.2 Q u with bad := st2.2.bad || hop2BadAt P s g₀ c }))

def hop2InjectPost {ℓ : ℕ} (P : Params Bytes PQC) (qep : ℕ) (s : BitVec 256)
    (Q : Party) (c : Bytes) (g₀ : GhostState Bytes)
    (o : Hop2Out Pt ℓ) (st2 : Hop2State Pt ℓ) :
    Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ :=
  match o with
  | none => (some .rejected, st2)
  | some ((st', t', i', m'), u) =>
    let aux := { st2.2 with bad := st2.2.bad || hop2BadAt P s g₀ c }
    if qep + 1 < t' then
      (some .rejected, (st2.1, aux))
    else
      let pos : SM.Pos := ⟨Q.other, t', i'⟩
      if st2.1.trivial 3 pos then
        (some (.accepted t' i' (some m')), (st2.1.accept Q st' pos, hop2Commit aux Q u))
      else
        (some .rejected, ({ st2.1 with win := true }, aux))

structure IsHop2Post {ℓ : ℕ} (P : Params Bytes PQC) (s : BitVec 256)
    (Q : Party) (c : Bytes) (g₀ : GhostState Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ →
        Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ) : Prop where
  on_none : ∀ st2, post none st2 = (some .rejected, st2)
  withLazy_comm : ∀ l o st2, post o (withLazy l st2) = ((post o st2).1, withLazy l (post o st2).2)
  on_some : ∀ st' t' i' m' u st2,
    let st_next := (post (some ((st', t', i', m'), u)) st2).2
    st_next.2.bad = (st2.2.bad || hop2BadAt P s g₀ c) ∧
    st_next.2.lazy = st2.2.lazy ∧
    ((st_next.1.st = st2.1.st ∧ st_next.2.idx = st2.2.idx ∧
      st_next.2.coins = st2.2.coins ∧ st_next.2.made = st2.2.made) ∨
     (st_next.1.st = Function.update st2.1.st Q st' ∧
      st_next.2.idx = (hop2Commit st2.2 Q u).idx ∧
      st_next.2.coins = (hop2Commit st2.2 Q u).coins ∧
      st_next.2.made = (hop2Commit st2.2 Q u).made))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2DeliverPost_isHop2Post {ℓ : ℕ} (P : Params Bytes PQC) (s : BitVec 256)
    (Q : Party) (c : Bytes) (g₀ : GhostState Bytes) (r : SM.Record (CBC.Plain ℓ) Bytes) :
    IsHop2Post (Pt := Pt) P s Q c g₀ (hop2DeliverPost P s Q c g₀ r) where
  on_none _ := rfl
  withLazy_comm l o st2 := by
    cases o with
    | none => rfl
    | some val =>
      rcases val with ⟨⟨st', t', i', m'⟩, u⟩
      cases u <;> rfl
  on_some st' t' i' m' u st2 := by
    refine ⟨rfl, ?_, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
    cases u <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2InjectPost_isHop2Post {ℓ : ℕ} (P : Params Bytes PQC) (qep : ℕ) (s : BitVec 256)
    (Q : Party) (c : Bytes) (g₀ : GhostState Bytes) :
    IsHop2Post (Pt := Pt) P s Q c g₀ (hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c g₀) where
  on_none _ := rfl
  withLazy_comm l o st2 := by
    cases o with
    | none => rfl
    | some val =>
      rcases val with ⟨⟨st', t', i', m'⟩, u⟩
      dsimp only [hop2InjectPost, withLazy]
      split_ifs
      · rfl
      · cases u <;> rfl
      · rfl
  on_some st' t' i' m' u st2 := by
    dsimp only [hop2InjectPost]
    split_ifs
    · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · refine ⟨?_, ?_, Or.inr ⟨rfl, ?_, ?_, ?_⟩⟩ <;> (cases u <;> rfl)
    · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem hop2Lift_run {ℓ : ℕ} {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (st : Hop2State Pt ℓ) :
    (hop2Lift m).run st =
      (do
        let r ← (liftM (m.run st.1) :
          Hop2Comp Pt (α × SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes))
        return (r.1, (r.2, st.2))) := rfl

omit [SampleableType Pt] in
theorem hop2Deliver_run_eq_post {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256) (h : Hop2Hyb Pt)
    (Q : Party) (c : Bytes) (st : Hop2State Pt ℓ) (r : SM.Record (CBC.Plain ℓ) Bytes)
    (hwin : st.1.win = false) (hin : st.1.inTransit Q.other c = some r) :
    (hop2Deliver P Dh encT decT s h (Q, c)).run st =
      (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st
        return hop2DeliverPost P s Q c (st.1.st Q) r res.1 res.2) := by
  unfold hop2Deliver hop2DeliverPost
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte,
    hin, stateT_lift_run_hop2, bind_assoc]
  refine bind_congr fun rc => ?_
  refine bind_congr fun res => ?_
  rcases res with ⟨o, st2⟩
  cases o with
  | none => rfl
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    rfl

omit [SampleableType Pt] in
theorem hop2Inject_run_eq_post {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (Q : Party) (c : Bytes) (st : Hop2State Pt ℓ)
    (hguard : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false) :
    (hop2Inject P Dh encT decT qep s h (Q, c)).run st =
      (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st
        return hop2InjectPost P qep s Q c (st.1.st Q) res.1 res.2) := by
  unfold hop2Inject hop2InjectPost
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hguard, Bool.false_eq_true, ↓reduceIte,
    stateT_lift_run_hop2, bind_assoc]
  refine bind_congr fun rc => ?_
  refine bind_congr fun res => ?_
  rcases res with ⟨o, st2⟩
  cases o with
  | none => rfl
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp [StateT.run_set]

omit [SampleableType Pt] in
theorem hop2RecvWithPost_withLazy {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256)
    (h : Hop2Hyb Pt) (Q : Party) (c : Bytes) (g₀ : GhostState Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s Q c g₀ post)
    (rc : BitVec 256) (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ) :
    (do
      let res ← (hop2Recv P Dh encT decT h g₀ c rc).run (withLazy l st)
      return post res.1 res.2) =
    match hop2LazyKey P Dh encT decT h g₀ c st with
    | none =>
      (fun r => ( (post r.1 st).1, withLazy l (post r.1 st).2 )) <$>
        (hop2Recv P Dh encT decT h g₀ c rc).run (withLazy [] st)
    | some (tq, msg, sc) =>
      match l.lookup tq with
      | some u =>
        pure ((post (hop2OffChainOut P ℓ g₀ msg sc rc u) st).1,
          withLazy l (post (hop2OffChainOut P ℓ g₀ msg sc rc u) st).2)
      | none =>
        (fun u => ((post (hop2OffChainOut P ℓ g₀ msg sc rc u) st).1,
          withLazy ((tq, u) :: l) (post (hop2OffChainOut P ℓ g₀ msg sc rc u) st).2)) <$>
          hop2Unif (Pt := Pt) := by
  cases hkey : hop2LazyKey P Dh encT decT h g₀ c st with
  | none =>
    rw [hop2Recv_run_of_hop2LazyKey_none P Dh encT decT h g₀ c rc l st hkey]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
      hpost.withLazy_comm l]
    rfl
  | some val =>
    rcases val with ⟨tq, msg, sc⟩
    rw [hop2Recv_run_of_hop2LazyKey_some P Dh encT decT h g₀ c rc l st tq msg sc hkey]
    unfold hop2Lazy
    have hl : (withLazy l st).2.lazy = l := rfl
    simp only [hl, Prod.mk.eta, map_eq_bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind]
    cases l.lookup tq with
    | some u =>
      simp only [StateT.run_pure, Function.comp_apply, pure_bind, hpost.withLazy_comm l]
    | none =>
      simp only [stateT_lift_run_hop2, StateT.run_bind, StateT.run_set, StateT.run_pure,
        Function.comp_apply, bind_assoc, pure_bind]
      refine bind_congr fun u => ?_
      have hcomm := hpost.withLazy_comm ((tq, u) :: l) (hop2OffChainOut P ℓ g₀ msg sc rc u) st
      simpa only [withLazy, Function.comp_apply] using congrArg pure hcomm

omit [SampleableType Pt] in
theorem hop2Deliver_run_withLazy {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256) (h : Hop2Hyb Pt)
    (Q : Party) (c : Bytes) (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ)
    (r : SM.Record (CBC.Plain ℓ) Bytes)
    (hwin : st.1.win = false) (hin : st.1.inTransit Q.other c = some r) :
    (hop2Deliver P Dh encT decT s h (Q, c)).run (withLazy l st) =
      (do
        let rc ← hop2Unif (Pt := Pt)
        match hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
        | none =>
          (fun res => ((hop2DeliverPost P s Q c (st.1.st Q) r res.1 st).1,
            withLazy l (hop2DeliverPost P s Q c (st.1.st Q) r res.1 st).2)) <$>
            (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy [] st)
        | some (tq, msg, sc) =>
          match l.lookup tq with
          | some u =>
            pure ((hop2DeliverPost P s Q c (st.1.st Q) r (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc
                u) st).1,
              withLazy l (hop2DeliverPost P s Q c (st.1.st Q) r (hop2OffChainOut P ℓ (st.1.st Q) msg
                  sc rc u) st).2)
          | none =>
            (fun u => ((hop2DeliverPost P s Q c (st.1.st Q) r (hop2OffChainOut P ℓ (st.1.st Q) msg
                sc rc u) st).1,
              withLazy ((tq, u) :: l)
                (hop2DeliverPost P s Q c (st.1.st Q) r (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u)
                    st).2)) <$>
              hop2Unif (Pt := Pt)) := by
  rw [hop2Deliver_run_eq_post P Dh encT decT s h Q c (withLazy l st) r hwin hin]
  refine bind_congr fun rc => ?_
  exact hop2RecvWithPost_withLazy P Dh encT decT s h Q c (st.1.st Q) _
    (hop2DeliverPost_isHop2Post P s Q c (st.1.st Q) r) rc l st

omit [SampleableType Pt] in
theorem hop2Inject_run_withLazy {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (Q : Party) (c : Bytes)
    (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ)
    (hguard : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false) :
    (hop2Inject P Dh encT decT qep s h (Q, c)).run (withLazy l st) =
      (do
        let rc ← hop2Unif (Pt := Pt)
        match hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
        | none =>
          (fun res => ((hop2InjectPost P qep s Q c (st.1.st Q) res.1 st).1,
            withLazy l (hop2InjectPost P qep s Q c (st.1.st Q) res.1 st).2)) <$>
            (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy [] st)
        | some (tq, msg, sc) =>
          match l.lookup tq with
          | some u =>
            pure ((hop2InjectPost P qep s Q c (st.1.st Q) (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc
                u) st).1,
              withLazy l (hop2InjectPost P qep s Q c (st.1.st Q) (hop2OffChainOut P ℓ (st.1.st Q)
                  msg sc rc u) st).2)
          | none =>
            (fun u => ((hop2InjectPost P qep s Q c (st.1.st Q) (hop2OffChainOut P ℓ (st.1.st Q) msg
                sc rc u) st).1,
              withLazy ((tq, u) :: l)
                (hop2InjectPost P qep s Q c (st.1.st Q) (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc
                    u) st).2)) <$>
              hop2Unif (Pt := Pt)) := by
  rw [hop2Inject_run_eq_post P Dh encT decT qep s h Q c (withLazy l st) hguard]
  refine bind_congr fun rc => ?_
  exact hop2RecvWithPost_withLazy P Dh encT decT s h Q c (st.1.st Q) _
    (hop2InjectPost_isHop2Post (Pt := Pt) (ℓ := ℓ) P qep s Q c (st.1.st Q)) rc l st

omit [SampleableType Pt] in
theorem simulateQ_hop2Impl_withLazy_congr {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) {l₁ l₂ : List ((ℕ × Pt) × BitVec 256)}
    (hlook : LookupEq l₁ l₂) :
    (do let (_, st') ← (simulateQ (hop2Impl P Dh encT decT qep s h) oa).run (withLazy l₁ st)
        return st'.2.bad) =
    (do let (_, st') ← (simulateQ (hop2Impl P Dh encT decT qep s h) oa).run (withLazy l₂ st)
        return st'.2.bad) := by
  induction oa using OracleComp.inductionOn generalizing st l₁ l₂ with
  | pure a =>
    simp [StateT.run_pure, withLazy]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    rcases t with u | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · simp only [hop2Impl, stateT_lift_run_hop2, bind_assoc, pure_bind]
      refine bind_congr fun a => ?_
      exact ih a st hlook
    · simp only [hop2Impl, hop2Lift_run, bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      exact ih r.1 (r.2, st.2) hlook
    · simp only [hop2Impl, hop2Lift_run, bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      exact ih r.1 (r.2, st.2) hlook
    · dsimp only [hop2Impl]
      by_cases hwin : st.1.win = true
      · have hw1 : (withLazy l₁ st).1.win = true := hwin
        have hw2 : (withLazy l₂ st).1.win = true := hwin
        unfold hop2Deliver
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hw1, hw2, ↓reduceIte,
            StateT.run_pure]
        exact ih none st hlook
      · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
        cases hin : st.1.inTransit Q.other c with
        | none =>
          have hw1 : (withLazy l₁ st).1.win = false := hwinF
          have hw2 : (withLazy l₂ st).1.win = false := hwinF
          have hi1 : (withLazy l₁ st).1.inTransit Q.other c = none := hin
          have hi2 : (withLazy l₂ st).1.inTransit Q.other c = none := hin
          unfold hop2Deliver
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hw1, hw2, Bool.false_eq_true,
            ↓reduceIte, hi1, hi2, StateT.run_pure]
          exact ih none st hlook
        | some r =>
          rw [hop2Deliver_run_withLazy P Dh encT decT s h Q c l₁ st r hwinF hin,
              hop2Deliver_run_withLazy P Dh encT decT s h Q c l₂ st r hwinF hin]
          simp only [bind_assoc]
          refine bind_congr fun rc => ?_
          cases hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
          | none =>
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            refine bind_congr fun res => ?_
            exact ih _ _ hlook
          | some val =>
            rcases val with ⟨tq, msg, sc⟩
            dsimp only []
            rw [hlook tq]
            cases l₂.lookup tq with
            | some u =>
              simp only [pure_bind]
              exact ih _ _ hlook
            | none =>
              simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
              refine bind_congr fun u => ?_
              exact ih _ _ (hlook.cons tq u)
    · dsimp only [hop2Impl]
      by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
      · have hg1 : ((withLazy l₁ st).1.win || ((withLazy l₁ st).1.inTransit Q.other c).isSome ||
            !((withLazy l₁ st).1.safeInj 3) ||
                !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg
        have hg2 : ((withLazy l₂ st).1.win || ((withLazy l₂ st).1.inTransit Q.other c).isSome ||
            !((withLazy l₂ st).1.safeInj 3) ||
                !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg
        unfold hop2Inject
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hg1, hg2, ↓reduceIte,
            StateT.run_pure]
        exact ih none st hlook
      · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
        rw [hop2Inject_run_withLazy P Dh encT decT qep s h Q c l₁ st hgF,
            hop2Inject_run_withLazy P Dh encT decT qep s h Q c l₂ st hgF]
        simp only [bind_assoc]
        refine bind_congr fun rc => ?_
        cases hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
        | none =>
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
          refine bind_congr fun res => ?_
          exact ih _ _ hlook
        | some val =>
          rcases val with ⟨tq, msg, sc⟩
          dsimp only []
          rw [hlook tq]
          cases l₂.lookup tq with
          | some u =>
            simp only [pure_bind]
            exact ih _ _ hlook
          | none =>
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            refine bind_congr fun u => ?_
            exact ih _ _ (hlook.cons tq u)
    · simp only [hop2Impl, hop2Lift_run, bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      exact ih r.1 (r.2, st.2) hlook

omit [Zero Pt] [SampleableType Pt] in
@[simp] theorem simulateQ_lazyImpl_liftM {α : Type} (oa : ProbComp α) :
    simulateQ (lazyImpl (Pt := Pt))
      (liftM oa : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) =
      (StateT.lift oa : StateT (List (Pt × BitVec 256)) ProbComp α) := by
  simp [lazyImpl, QueryImpl.simulateQ_add_liftM_left]
  rfl

@[simp] theorem stateT_lift_probComp_run {S α : Type} (oa : ProbComp α) (s : S) :
    (StateT.lift oa : StateT S ProbComp α).run s = (do let a ← oa; return (a, s)) := rfl


/-- Runs `oa` in `hop2Impl` under `lazyImpl` from `(st, tbl)`, returning `st'.2.bad`. -/
def runHop2 {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) : ProbComp Bool :=
  (simulateQ (lazyImpl (Pt := Pt)) (do
    let (_, st') ← (simulateQ (hop2Impl P Dh encT decT qep s h) oa).run st
    return st'.2.bad)).run' tbl

omit [SampleableType Pt] in
@[simp] theorem runHop2_pure {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (a : β) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    runHop2 P Dh encT decT qep s h (pure a) st tbl = pure st.2.bad := rfl

omit [SampleableType Pt] in
theorem runHop2_withLazy_congr {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    {l₁ l₂ : List ((ℕ × Pt) × BitVec 256)} (hlook : LookupEq l₁ l₂) :
    runHop2 P Dh encT decT qep s h oa (withLazy l₁ st) tbl =
      runHop2 P Dh encT decT qep s h oa (withLazy l₂ st) tbl := by
  unfold runHop2
  rw [simulateQ_hop2Impl_withLazy_congr P Dh encT decT qep s h oa st hlook]


omit [SampleableType Pt] in
theorem evalDist_runHop2_tbl_cons_fresh {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) (I : Pt)
    (hfresh : tbl.lookup I = none) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
        runHop2 P Dh encT decT qep s h oa st ((I, u) :: tbl)] =
      𝒟[runHop2 P Dh encT decT qep s h oa st tbl] :=
  evalDist_lazyImpl_cons_fresh _ I tbl hfresh

omit [SampleableType Pt] in
theorem runHop2_bind_query {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (t : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (k : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Range t →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    runHop2 P Dh encT decT qep s h
      (liftM (OracleSpec.query (spec := unifSpec +
          SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) t) >>= k)
      st tbl =
      (do
        let z ← (simulateQ (lazyImpl (Pt :=
            Pt)) ((hop2Impl P Dh encT decT qep s h t).run st)).run tbl
        runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2) := by
  unfold runHop2
  simp only [StateT.run'_eq, simulateQ_bind, simulateQ_pure, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind, StateT.run_pure,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rfl

omit [SampleableType Pt] in
theorem runHop2_hop2Lift {ℓ : ℕ} {α β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (k : α → OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) ((hop2Lift m).run (withLazy l st))).run tbl
      runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2) =
    (do
      let r ← m.run st.1
      runHop2 P Dh encT decT qep s h (k r.1) (withLazy l (r.2, st.2)) tbl) := by
  simp [withLazy]

omit [SampleableType Pt] in
theorem runHop2_recvWithPost {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (Q : Party) (c : Bytes)
    (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s Q c (st.1.st Q) post)
    (k : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l st)
        return post res.1 res.2)).run tbl
      runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2) =
    (do
      let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      match hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
      | none =>
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy [] st))).run tbl
        runHop2 P Dh encT decT qep s h (k (post z.1.1 st).1) (withLazy l (post z.1.1 st).2) z.2
      | some (tq, msg, sc) =>
        match l.lookup tq with
        | some u =>
          let p := post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st
          runHop2 P Dh encT decT qep s h (k p.1) (withLazy l p.2) tbl
        | none =>
          let u ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          let p := post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st
          runHop2 P Dh encT decT qep s h (k p.1) (withLazy ((tq, u) :: l) p.2) tbl) := by
  have h1 : (do
      let rc ← hop2Unif (Pt := Pt)
      let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l st)
      return post res.1 res.2) =
    (do
      let rc ← hop2Unif (Pt := Pt)
      match hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
      | none =>
        (fun r => ((post r.1 st).1, withLazy l (post r.1 st).2)) <$>
          (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy [] st)
      | some (tq, msg, sc) =>
        match l.lookup tq with
        | some u =>
          pure ((post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st).1,
            withLazy l (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st).2)
        | none =>
          (fun u => ((post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st).1,
            withLazy ((tq, u) :: l) (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st).2)) <$>
            hop2Unif (Pt := Pt)) := by
    refine bind_congr fun rc => ?_
    exact hop2RecvWithPost_withLazy P Dh encT decT s h Q c (st.1.st Q) post hpost rc l st
  rw [h1]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif, stateT_lift_probComp_run,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr fun rc => ?_
  cases hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
  | none =>
    simp [simulateQ_bind]
  | some val =>
    rcases val with ⟨tq, msg, sc⟩
    dsimp only []
    cases l.lookup tq with
    | some u =>
      simp [StateT.run_pure]
    | none =>
      simp [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
        StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType Pt] in
theorem evalDist_runHop2_recvWithPost_cons_fresh {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (Q : Party) (c : Bytes)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s Q c (st.1.st Q) post)
    (k : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (l : List ((ℕ × Pt) × BitVec 256)) (tq : ℕ × Pt)
    (hfresh : l.lookup tq = none)
    (ih : ∀ a st' tbl' l', l'.lookup tq = none →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
          runHop2 P Dh encT decT qep s h (k a) (withLazy ((tq, u) :: l') st') tbl'] =
        𝒟[runHop2 P Dh encT decT qep s h (k a) (withLazy l' st') tbl']) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
        do
          let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
            let rc ← hop2Unif (Pt := Pt)
            let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run
              (withLazy ((tq, u) :: l) st)
            return post res.1 res.2)).run tbl
          runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2] =
    𝒟[do
        let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
          let rc ← hop2Unif (Pt := Pt)
          let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l st)
          return post res.1 res.2)).run tbl
        runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2] := by
  have hl1 : ∀ u, (do
        let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
          let rc ← hop2Unif (Pt := Pt)
          let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run
            (withLazy ((tq, u) :: l) st)
          return post res.1 res.2)).run tbl
        runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2) = _ :=
    fun u => runHop2_recvWithPost P Dh encT decT qep s h Q c ((tq, u) :: l) st tbl post hpost k
  simp_rw [hl1, runHop2_recvWithPost P Dh encT decT qep s h Q c l st tbl post hpost k]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun rc => ?_
  cases hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
  | none =>
    dsimp only []
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
    refine evalDist_bind_congr _ _ _ fun z => ?_
    exact ih (post z.1.1 st).1 (post z.1.1 st).2 z.2 l hfresh
  | some val =>
    rcases val with ⟨tq', msg, sc⟩
    dsimp only [List.lookup]
    by_cases heq : (tq' == tq) = true
    · have htq : tq' = tq := eq_of_beq heq
      subst htq
      simp only [heq, hfresh]
    · have hne : (tq' == tq) = false := Bool.eq_false_iff.mpr heq
      have hne_val : tq' ≠ tq := beq_eq_false_iff_ne.mp hne
      simp only [hne]
      cases hlook' : l.lookup tq' with
      | some u' =>
        dsimp only []
        exact ih _ _ tbl l hfresh
      | none =>
        dsimp only []
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
        refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun u' => ?_
        have hswap : ∀ u,
            runHop2 P Dh encT decT qep s h
              (k (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).1)
              (withLazy ((tq', u') :: (tq, u) :: l)
                (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).2) tbl =
            runHop2 P Dh encT decT qep s h
              (k (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).1)
              (withLazy ((tq, u) :: (tq', u') :: l)
                (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).2) tbl :=
          fun u => runHop2_withLazy_congr P Dh encT decT qep s h _ _ tbl
            (LookupEq.swap_cons tq' tq u' u l hne_val)
        simp_rw [hswap]
        have hfresh' : (((tq', u') :: l).lookup tq) = none := by
          have hne_symm : (tq == tq') = false := beq_eq_false_iff_ne.mpr hne_val.symm
          simp [List.lookup, hne_symm, hfresh]
        exact ih _ _ tbl ((tq', u') :: l) hfresh'

omit [SampleableType Pt] in
/-- Pre-sampling a fresh entry `(tq, u)` in `withLazy` preserves `evalDist` of `runHop2`. -/
theorem evalDist_runHop2_lazy_cons_fresh {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (l : List ((ℕ × Pt) × BitVec 256)) (tq : ℕ × Pt)
    (hfresh : l.lookup tq = none) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
        runHop2 P Dh encT decT qep s h oa (withLazy ((tq, u) :: l) st) tbl] =
      𝒟[runHop2 P Dh encT decT qep s h oa (withLazy l st) tbl] := by
  induction oa using OracleComp.inductionOn generalizing st tbl l with
  | pure a =>
    simp only [runHop2_pure, withLazy, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
  | query_bind t k ih =>
    simp_rw [runHop2_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · have hunif : ∀ l',
          (do
            let z ← (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Impl P Dh encT decT qep s h (.inl u_q)).run (withLazy l' st))).run tbl
            runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2) =
          (do
            let a ← (liftM (OracleSpec.query (spec := unifSpec) u_q) : ProbComp _)
            runHop2 P Dh encT decT qep s h (k a) (withLazy l' st) tbl) := by
        intro l'
        simp [hop2Impl,
          lazyImpl, QueryImpl.add_apply_inl,
          StateT.run_monadLift, monadLift_self]
      simp_rw [hunif]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine evalDist_bind_congr _ _ _ fun a => ih a st tbl l hfresh
    · dsimp only [hop2Impl]
      simp_rw [runHop2_hop2Lift]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine evalDist_bind_congr _ _ _ fun r => ih r.1 (r.2, st.2) tbl l hfresh
    · dsimp only [hop2Impl]
      simp_rw [runHop2_hop2Lift]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine evalDist_bind_congr _ _ _ fun r => ih r.1 (r.2, st.2) tbl l hfresh
    · dsimp only [hop2Impl]
      by_cases hwin : st.1.win = true
      · have hstep : ∀ l',
            (hop2Deliver P Dh encT decT s h (Q, c)).run (withLazy l' st) =
            pure (none, withLazy l' st) := by
          intro l'
          have hw : (withLazy l' st).1.win = true := hwin
          unfold hop2Deliver
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hw, ↓reduceIte, StateT.run_pure]
        simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
        exact ih none st tbl l hfresh
      · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
        cases hin : st.1.inTransit Q.other c with
        | none =>
          have hstep : ∀ l',
              (hop2Deliver P Dh encT decT s h (Q, c)).run (withLazy l' st) =
              pure (none, withLazy l' st) := by
            intro l'
            have hw : (withLazy l' st).1.win = false := hwinF
            have hi : (withLazy l' st).1.inTransit Q.other c = none := hin
            unfold hop2Deliver
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hw, Bool.false_eq_true,
              ↓reduceIte, hi, StateT.run_pure]
          simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
          exact ih none st tbl l hfresh
        | some r =>
          have hstep : ∀ l',
              (hop2Deliver P Dh encT decT s h (Q, c)).run (withLazy l' st) =
              (do
                let rc ← hop2Unif (Pt := Pt)
                let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l' st)
                return hop2DeliverPost P s Q c (st.1.st Q) r res.1 res.2) :=
            fun l' => hop2Deliver_run_eq_post P Dh encT decT s h Q c (withLazy l' st) r hwinF hin
          simp_rw [hstep]
          exact evalDist_runHop2_recvWithPost_cons_fresh P Dh encT decT qep s h Q c st tbl _
            (hop2DeliverPost_isHop2Post P s Q c (st.1.st Q) r) k l tq hfresh ih
    · dsimp only [hop2Impl]
      by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
      · have hstep : ∀ l',
            (hop2Inject P Dh encT decT qep s h (Q, c)).run (withLazy l' st) =
            pure (none, withLazy l' st) := by
          intro l'
          have hgl : ((withLazy l' st).1.win || ((withLazy l' st).1.inTransit Q.other c).isSome ||
              !((withLazy l' st).1.safeInj 3) ||
                  !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg
          unfold hop2Inject
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hgl, ↓reduceIte, StateT.run_pure]
        simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
        exact ih none st tbl l hfresh
      · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
        have hstep : ∀ l',
            (hop2Inject P Dh encT decT qep s h (Q, c)).run (withLazy l' st) =
            (do
              let rc ← hop2Unif (Pt := Pt)
              let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l' st)
              return hop2InjectPost P qep s Q c (st.1.st Q) res.1 res.2) :=
          fun l' => hop2Inject_run_eq_post P Dh encT decT qep s h Q c (withLazy l' st) hgF
        simp_rw [hstep]
        exact evalDist_runHop2_recvWithPost_cons_fresh P Dh encT decT qep s h Q c st tbl _
          (hop2InjectPost_isHop2Post (Pt := Pt) (ℓ := ℓ) P qep s Q c (st.1.st Q)) k l tq hfresh ih
    · dsimp only [hop2Impl]
      simp_rw [runHop2_hop2Lift]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine evalDist_bind_congr _ _ _ fun r => ih r.1 (r.2, st.2) tbl l hfresh

end Hop2Coupling
end CryptoVerification.E2E.SpkHop1
