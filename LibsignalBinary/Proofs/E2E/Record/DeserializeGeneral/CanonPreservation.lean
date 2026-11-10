/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs

/-!
# Canonicity Preservation Across Session Send and Receive

Establishes that `CanonRecord` and `CanonState` are preserved across session operations so
`serializeCanon_root` re-encodes updated records faithfully:
* **Send** (`canonRecord_send`): `SessionState.messageEncrypt` preserves identities, ratchet keys,
  pending pre-key state, and receiver chains (`SendKeeps`), keeping `CanonRecord` across
  `AfterOutgoingRatchetApply` and `AgreeExceptPq`.
* **Receive** (`sessionStateAt_canon`, `sessionRecordAt_canon`, `recvKeepsCanon_of_recordDecrypt`):
  `sessionStateAt` entails `CanonState`, discharging `RecvKeepsCanon` from `RecordDecryptRunStmt`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonCur CanonSession CanonSender CanonChain
  CanonPending)

/-! ## `SessionState` Canonicity -/

/-- The `SessionState` part of `CanonSession` (everything but the pending pre-key): identity keys
and ratchet public keys stored as their serializations, the sender's private key exactly,
receiver chains without private keys, matching shapes. -/
def CanonState (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  G.localIk.bytes = st.localIdentity.serialize ∧
  G.remoteIk.bytes = (st.remoteIdentity.map IdentityKey.serialize).getD [] ∧
  CanonSender G.sender st.senderChain ∧
  G.chains.length = st.receiverChains.length ∧
  (∀ gc ∈ G.chains.zip st.receiverChains, CanonChain gc)

/-- `CanonSession` splits into `CanonState` and `CanonPending`. -/
theorem canonSession_iff (G : SessionGhost) (s : Session (List (BitVec 8))) :
    CanonSession G s ↔ CanonState G s.state ∧ CanonPending G.pending s.pendingPreKey := by
  simp only [CanonSession, CanonState, and_assoc]

/-! ## Send Preservation -/

/-- What a successful session-model send keeps of the session state: the identities, the receiver chains, the
pending flag, and the sender chain's ratchet key pair (only its chain key advances). -/
def SendKeeps (st st' : SessionState (List (BitVec 8))) : Prop :=
  st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity ∧
    st'.receiverChains = st.receiverChains ∧ st'.pendingPreKey = st.pendingPreKey ∧
    st'.senderChain.map SenderChain.ratchetKey = st.senderChain.map SenderChain.ratchetKey

private theorem exec_get' {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem exec_throw' {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem exec_pure' {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := rfl

private theorem exec_modifyGet' {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

private theorem exec_bind' {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
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

private theorem fromSessionState_state (st : SessionState (List (BitVec 8))) :
    ∃ pq, (Mut.exec OutgoingTripleRatchet.fromSessionState st).2 =
      { st with pqRatchetState := pq } := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
  rcases hsc : st.senderChain with _ | sc
  · refine ⟨st.pqRatchetState, ?_⟩
    simp only [hsc, exec_bind', exec_get', exec_throw']
    cases st
    simp_all
  · refine ⟨default, ?_⟩
    simp only [hsc, exec_bind', exec_get', exec_modifyGet']
    split_ifs
    · rfl
    · rcases st.remoteIdentity with _ | remote <;> simp [exec_throw', exec_pure']

/-- Successful `SessionState.messageEncrypt` preserves `SendKeeps`, updating only the sender chain
key and post-quantum ratchet state. -/
theorem messageEncrypt_sendKeeps {PQC : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr (List (BitVec 8)) PQC) (addresses : Option (List (BitVec 8)))
    (ptext : List (BitVec 8)) (coins : PQC) (st : SessionState (List (BitVec 8)))
    (msg : SignalMessage) (st' : SessionState (List (BitVec 8)))
    (h : SessionState.messageEncrypt C codec spqr addresses ptext coins st = (.ok msg, st')) :
    SendKeeps st st' := by
  unfold SessionState.messageEncrypt at h
  obtain ⟨pq, hpq⟩ := fromSessionState_state st
  rcases h1 : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨e | session, taken⟩
  · rw [h1] at h
    simp at h
  · rw [h1] at h hpq
    dsimp only at h hpq
    rcases h2 : Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext
        (st.encryptAddresses addresses) coins) session with ⟨e | message, session'⟩
    · rw [h2] at h
      simp at h
    · rw [h2] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      subst hpq
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_map]
      rcases st.senderChain with _ | sc <;> rfl

/-- `CanonSender` reads only the ghost's `srk` / `priv` bytes and the model's ratchet key pair. -/
theorem canonSender_congr {g g' : Option SenderChainGhost} {s s' : Option SenderChain}
    (hc : CanonSender g s)
    (hg : g'.map (fun x => (x.srk, x.priv)) = g.map (fun x => (x.srk, x.priv)))
    (hs : s'.map SenderChain.ratchetKey = s.map SenderChain.ratchetKey) :
    CanonSender g' s' := by
  rcases g with _ | g <;> rcases s with _ | s <;> rcases g' with _ | g' <;>
    rcases s' with _ | s' <;>
    simp only [CanonSender, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq, Prod.mk.injEq] at hc hg hs ⊢
  obtain ⟨h1, h2⟩ := hg
  rw [h1, h2, hs]
  exact hc

/-- `AfterOutgoingRatchetApply` and `AgreeExceptPq` preserve `CanonState` when the model transition
satisfies `SendKeeps`. -/
theorem canonState_send (G G' : SessionGhost) (st st' : SessionState (List (BitVec 8)))
    (hc : CanonState G st) (hG : G.AfterOutgoingRatchetApply G' ∨ G.AgreeExceptPq G') (hk : SendKeeps st st') :
    CanonState G' st' := by
  obtain ⟨hl, hr, hs, hn, hz⟩ := hc
  obtain ⟨kl, kr, kc, -, ks⟩ := hk
  have hsame : G'.localIk = G.localIk ∧ G'.remoteIk = G.remoteIk ∧ G'.chains = G.chains ∧
      G'.sender.map (fun x => (x.srk, x.priv)) = G.sender.map (fun x => (x.srk, x.priv)) := by
    rcases hG with ⟨sg, sg', hsg, hsg', hsgsg, hG'⟩ | hG'
    · have e1 := congrArg SessionGhost.localIk hG'
      have e2 := congrArg SessionGhost.remoteIk hG'
      have e3 := congrArg SessionGhost.chains hG'
      refine ⟨e1, e2, e3, ?_⟩
      rw [hsg, hsg', Option.map_some, Option.map_some, hsgsg]
    · unfold SessionGhost.AgreeExceptPq at hG'
      have e1 := congrArg SessionGhost.localIk hG'
      have e2 := congrArg SessionGhost.remoteIk hG'
      have e3 := congrArg SessionGhost.chains hG'
      have e4 := congrArg (fun G => G.sender.map (fun x : SenderChainGhost => (x.srk, x.priv))) hG'
      exact ⟨e1, e2, e3, e4⟩
  obtain ⟨e1, e2, e3, e4⟩ := hsame
  refine ⟨?_, ?_, canonSender_congr hs e4 ks, ?_, ?_⟩
  · rw [e1, kl]; exact hl
  · rw [e2, kr]; exact hr
  · rw [e3, kc]; exact hn
  · rw [e3, kc]; exact hz

/-- A successful session send preserves `CanonRecord` on the stored `SessionRecord`. -/
theorem canonRecord_send {PQC : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr (List (BitVec 8)) PQC) (addresses : Option (List (BitVec 8)))
    (ptext : List (BitVec 8)) (coins : PQC) (g : GhostState Bytes) (msg : SignalMessage)
    (st' : SessionState (List (BitVec 8)))
    (h : SessionState.messageEncrypt C codec spqr addresses ptext coins g.session = (.ok msg, st'))
    (pc pp : BitVec 64) (G G' : SessionGhost)
    (hc : CanonRecord ⟨pc, pp, some G⟩ (toRecord extrasM g))
    (hG : G.AfterOutgoingRatchetApply G' ∨ G.AgreeExceptPq G') :
    CanonRecord ⟨pc, pp, some G'⟩ (toRecord extrasM { g with session := st' }) := by
  have hk := messageEncrypt_sendKeeps C codec spqr addresses ptext coins g.session msg st' h
  have hpend : G'.pending = G.pending := by
    rcases hG with ⟨sg, sg', -, -, -, hG'⟩ | hG'
    · have e := congrArg SessionGhost.pending hG'
      exact e
    · unfold SessionGhost.AgreeExceptPq at hG'
      have e := congrArg SessionGhost.pending hG'
      exact e
  simp only [CanonRecord, CanonCur, toRecord, canonSession_iff] at hc ⊢
  obtain ⟨hcs, hcp⟩ := hc
  refine ⟨canonState_send G G' g.session st' hcs hG hk, ?_⟩
  rw [hpend, hk.2.2.2.1]
  exact hcp

/-! ## Receive Canonicity Interface -/

/-- `sessionStateAt` with a canonical ghost. -/
def canonStateAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜CanonState G st⌝ ∗ sessionStateAt A ss G st

/-- `recordDecryptSpec` specialized to canonical session ghosts (`canonStateAt` in precondition and
postconditions). -/
def recordDecryptCanonSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (img : Obj.Image) : Spec RecordDecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.spAligned = true ∧ s.readReg64 .x27 = x.sret ∧ s.readReg64 .x19 = x.remA ∧
          s.readReg64 .x23 = s.sp + 0x5f0#64 ∧ s.readReg64 .x24 = s.sp + 0xca0#64 ∧
          x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
          x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
        memRegion s.sp 0xa0 ∗
        ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        canonStateAt A (s.sp + 0x138#64) x.G x.st ∗
        memRegion (s.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace ∧ sf.sp = s0.sp ∧
          sf.readReg64 .x29 = s0.readReg64 .x29 ∧ sf.readReg64 .x27 = x.sret ∧
          sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧
          sf.readReg64 .x28 = recordResultTag (x.model C S uuidParse).1⌝ ∗
        memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (match (x.model C S uuidParse).1 with
         | .ok _ => ∃∗ G' : SessionGhost, ⌜x.G.AfterRecordDecrypt G'⌝ ∗
             canonStateAt A (s0.sp + 0x138#64) G' (x.model C S uuidParse).2
         | .error _ => canonStateAt A (s0.sp + 0x138#64) x.G x.st) ∗
        recordResultAt A (s0.sp + 0x4b0#64) (x.model C S uuidParse).1 ∗
        memRegion (s0.sp + 0x4e0#64) 0x920 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest (x.draws C) ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model C S uuidParse).1 = .error .panic ∨
            (x.st.version.toNat = x.msg.messageVersion.toNat ∧
              S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- Canonicity-preserving contract for `try_decrypt_from_record` (`recordDecryptCanonSpec`). -/
def RecvKeepsCanon (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → SpqrRecvOk C A ctl S abs img → Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg img C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      (recordDecryptCanonSpec C A ctl uuidParse S img)

/-! ## Entailment of `CanonState` and `CanonRecord` from Representation Predicates -/

theorem pk_eq_serialize_of_deserialize_len33 {bs : List (BitVec 8)} {pk : PublicKey}
    (hd : PublicKey.deserialize bs = .ok pk) (hl : bs.length = 33) :
    bs = pk.serialize := by
  unfold PublicKey.deserialize PublicKey.serialize at *
  rcases bs with _ | ⟨tag, rest⟩
  · simp at hl
  · dsimp only at hd
    have hl' : rest.length = 32 := by simp at hl; omega
    split_ifs at hd with h1 h2
    · have htag : tag = djbType := Classical.not_not.mp h1
      subst htag
      simp only [Except.ok.injEq] at hd
      subst hd
      simp [List.take_of_length_le (Nat.le_of_eq hl')]

theorem ik_serialize_eq (ik : IdentityKey) :
    ik.serialize = ik.publicKey.serialize := rfl

theorem chainAt_canon (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a ⊢ ⌜CanonChain gc⌝ ∗ chainAt A gc a := by
  unfold chainAt
  apply Entails.pure_left
  rintro ⟨hdeser, hmax, hklen, hsrk_len, hpriv⟩
  have hcanon : CanonChain gc :=
    ⟨pk_eq_serialize_of_deserialize_len33 hdeser hsrk_len, hpriv⟩
  exact Entails.pure_right hcanon
    (Entails.pure_right ⟨hdeser, hmax, hklen, hsrk_len, hpriv⟩ (Entails.refl _))

theorem arrayAt_chainAt_canon (A : RustAlloc) :
    ∀ (xs : List (ChainGhost × ReceiverChain)) (base : BitVec 64),
      arrayAt (chainAt A) 104 base xs ⊢
        ⌜∀ gc ∈ xs, CanonChain gc⌝ ∗ arrayAt (chainAt A) 104 base xs
  | [], _ => by
    dsimp only [arrayAt]
    exact Entails.pure_right (by intro _ h; cases h) (Entails.refl _)
  | gc :: xs, base => by
    dsimp only [arrayAt]
    refine Entails.trans
      (sepConj_mono (chainAt_canon A gc base)
        (arrayAt_chainAt_canon A xs (base + BitVec.ofNat 64 104))) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hgc
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hxs
    have hall : ∀ x ∈ gc :: xs, CanonChain x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hgc
      · exact hxs x hx
    exact Entails.pure_right hall (Entails.refl _)

theorem vecAt_chainAt_canon (A : RustAlloc) (v cap ptr : BitVec 64)
    (xs : List (ChainGhost × ReceiverChain)) :
    vecAt A 104 8 (chainAt A) v cap ptr xs ⊢
      ⌜∀ gc ∈ xs, CanonChain gc⌝ ∗ vecAt A 104 8 (chainAt A) v cap ptr xs := by
  unfold vecAt vecBuf
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbuf
  by_cases hcap : cap = 0
  · subst hcap
    have hxs0 : xs.length = 0 := Nat.eq_zero_of_le_zero hbuf.1
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero hxs0
    subst hnil
    refine Entails.pure_right (by intro _ h; cases h) ?_
    exact Entails.pure_right hbuf (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (arrayAt_chainAt_canon A xs ptr)))) ?_
    have hpull :
        (vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗
          A.live ptr (cap.toNat * 104) 8 ∗
          (⌜∀ gc ∈ xs, CanonChain gc⌝ ∗ arrayAt (chainAt A) 104 ptr xs) ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * 104)) ((cap.toNat - xs.length) * 104)) =
        (⌜∀ gc ∈ xs, CanonChain gc⌝ ∗
          (vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗
            A.live ptr (cap.toNat * 104) 8 ∗
            arrayAt (chainAt A) 104 ptr xs ∗
            memRegion (ptr + BitVec.ofNat 64 (xs.length * 104)) ((cap.toNat - xs.length) * 104))) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hall
    refine Entails.pure_right hall ?_
    exact Entails.pure_right hbuf (Entails.refl _)

theorem optSenderChainAt_canon (A : RustAlloc) (a : BitVec 64)
    (gsender : Option SenderChainGhost) (sc : Option SenderChain) :
    optSenderChainAt A a gsender sc ⊢
      ⌜CanonSender gsender sc⌝ ∗ optSenderChainAt A a gsender sc := by
  rcases gsender with _ | g <;> rcases sc with _ | s
  · exact Entails.pure_right trivial (Entails.refl _)
  · dsimp only [optSenderChainAt]
    exact Entails.pure_left_only False.elim
  · dsimp only [optSenderChainAt]
    exact Entails.pure_left_only False.elim
  · unfold optSenderChainAt
    apply Entails.pure_left
    rintro ⟨hdeser, hpriv, hclamp, hsrk_len⟩
    have hcanon : CanonSender (some g) (some s) :=
      ⟨pk_eq_serialize_of_deserialize_len33 hdeser hsrk_len, hpriv⟩
    exact Entails.pure_right hcanon
      (Entails.pure_right ⟨hdeser, hpriv, hclamp, hsrk_len⟩ (Entails.refl _))

/-- `sessionStateAt` entails `CanonState`. -/
theorem sessionStateAt_canon (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢ ⌜CanonState G st⌝ ∗ sessionStateAt A ss G st := by
  unfold sessionStateAt
  apply Entails.pure_left
  rintro ⟨hloc_deser, hrem_deser, hchains_len, hpend_some, hreg_len, hloc_len, hrem_len⟩
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (vecAt_chainAt_canon A (ss + 0x48#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains))
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (optSenderChainAt_canon A (ss + 0x90#64) G.sender st.senderChain)))))))) ?_
  have hpull :
      (vecGhostAt A G.localIk ss ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
        (⌜∀ gc ∈ G.chains.zip st.receiverChains, CanonChain gc⌝ ∗
          vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains)) ∗
        vecGhostAt A G.alice (ss + 0x60#64) ∗
        vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        (⌜CanonSender G.sender st.senderChain⌝ ∗
          optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain) ∗
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
        optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
        ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
        ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds)) =
      (⌜∀ gc ∈ G.chains.zip st.receiverChains, CanonChain gc⌝ ∗
        ⌜CanonSender G.sender st.senderChain⌝ ∗
        (vecGhostAt A G.localIk ss ∗
          vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
          vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
          vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          vecGhostAt A G.alice (ss + 0x60#64) ∗
          vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
          optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
          optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
          optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
          ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
          ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
          ((ss + 0x150#64) ↦ₛ G.regIds))) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hchains_canon
  apply Entails.pure_left; intro hsender_canon
  have hloc_eq : G.localIk.bytes = st.localIdentity.serialize :=
    pk_eq_serialize_of_deserialize_len33 hloc_deser hloc_len
  have hrem_eq : G.remoteIk.bytes = (st.remoteIdentity.map IdentityKey.serialize).getD [] := by
    rcases hrem : st.remoteIdentity with _ | ik
    · rw [hrem] at hrem_deser
      exact hrem_deser
    · rw [hrem] at hrem_deser hrem_len
      exact pk_eq_serialize_of_deserialize_len33 hrem_deser (hrem_len rfl)
  have hcanon : CanonState G st :=
    ⟨hloc_eq, hrem_eq, hsender_canon, hchains_len, hchains_canon⟩
  exact Entails.pure_right hcanon
    (Entails.pure_right
      ⟨hloc_deser, hrem_deser, hchains_len, hpend_some, hreg_len, hloc_len, hrem_len⟩
      (Entails.refl _))

theorem canonPending_of_pendingRel {pg : Option TailVecGhost} {p : Option PendingPreKey}
    (h : PendingRel pg p) : CanonPending pg p := by
  rcases pg with _ | g <;> rcases p with _ | pk
  · trivial
  · exact False.elim h
  · exact False.elim h
  · exact pk_eq_serialize_of_deserialize_len33 h.1 h.2.2.2.2

theorem sessionAt_canon (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s ⊢ ⌜CanonSession G s⌝ ∗ sessionStateReprAt A ss G s := by
  unfold sessionStateReprAt
  apply Entails.pure_left
  rintro ⟨hpend, hkyb, halice, hremReg, hlocReg⟩
  refine Entails.trans (sessionStateAt_canon A ss G s.state) ?_
  apply Entails.pure_left; intro hcs
  have hcanon : CanonSession G s :=
    (canonSession_iff G s).mpr ⟨hcs, canonPending_of_pendingRel hpend⟩
  exact Entails.pure_right hcanon
    (Entails.pure_right ⟨hpend, hkyb, halice, hremReg, hlocReg⟩ (Entails.refl _))

/-- `sessionRecordAt` entails `CanonRecord`. -/
theorem sessionRecordAt_canon (A : RustAlloc) (r : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A r g rec ⊢ ⌜CanonRecord g rec⌝ ∗ sessionRecordAt A r g rec := by
  unfold sessionRecordAt CanonRecord CanonCur
  rcases g.cur with _ | G <;> rcases rec.currentSession with _ | s
  · exact Entails.pure_right trivial (Entails.refl _)
  · dsimp only
    have hpull :
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) r g.prevCap g.prevPtr [] ∗ ⌜False⌝) =
        (⌜False⌝ ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) r g.prevCap g.prevPtr []) := by ac_rfl
    rw [hpull]
    exact Entails.pure_left False.elim
  · dsimp only
    have hpull :
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) r g.prevCap g.prevPtr [] ∗ ⌜False⌝) =
        (⌜False⌝ ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) r g.prevCap g.prevPtr []) := by ac_rfl
    rw [hpull]
    exact Entails.pure_left False.elim
  · dsimp only
    refine Entails.trans (sepConj_mono_right (sessionAt_canon A (r + 0x18#64) G s)) ?_
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hcs
    exact Entails.pure_right hcs (Entails.refl _)

theorem canonStateAt_eq_sessionStateAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    canonStateAt A ss G st = sessionStateAt A ss G st := by
  have h1 : canonStateAt A ss G st ⊢ sessionStateAt A ss G st :=
    Entails.pure_left fun _ => Entails.refl _
  have h2 : sessionStateAt A ss G st ⊢ canonStateAt A ss G st :=
    sessionStateAt_canon A ss G st
  exact ProofLib.sepProp_eq_of_entails h1 h2

theorem canonStateAt_eq : @canonStateAt = @sessionStateAt := by
  funext A ss G st
  exact canonStateAt_eq_sessionStateAt A ss G st

theorem recordDecryptCanonSpec_eq (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image) :
    recordDecryptCanonSpec C A ctl uuidTryParse S img =
      recordDecryptSpec C A ctl uuidTryParse S img := by
  unfold recordDecryptCanonSpec recordDecryptSpec
  rw [canonStateAt_eq]
  rfl

/-- Discharges `RecvKeepsCanon` from `RecordDecryptRunStmt` via `sessionStateAt_canon`. -/
theorem recvKeepsCanon_of_recordDecrypt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) (h : RecordDecryptRunStmt C A ctl S abs img) :
    RecvKeepsCanon C A ctl uuidTryParse S abs img := by
  unfold RecvKeepsCanon RecordDecryptRunStmt at *
  rwa [recordDecryptCanonSpec_eq]

end CryptoVerification.E2E.Record.DeserializeGeneral
