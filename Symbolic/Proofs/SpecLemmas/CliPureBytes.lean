/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM

/-!
# Session record encoding, scope invariants, and ratchet preservation

Defines protobuf session-record encoders (`encodeRecord`), record scope predicates (`InScopeP`,
`DeserializeScopeP`), 32-byte skipped-key seed preservation (`SeedsLen32`, `RatchetSeedsLen32`),
`SessRepr` and `RatchetRepr` preservation across encrypt and decrypt steps, and two-party `Role`
and in-memory `StoreAnswers` helpers.
-/

@[expose] public section
set_option autoImplicit false
namespace Symbolic.Proofs.SpecLemmas.CliPureBytes
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec

/-! ## `Mut.exec` and list helpers -/

@[simp] theorem exec_pure {σ α : Type} (a : α) (s : σ) : Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl
@[simp] theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
@[simp] theorem exec_get {σ : Type} (s : σ) : Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
@[simp] theorem exec_set {σ : Type} (s' s : σ) : Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl
@[simp] theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl
@[simp] theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
@[simp] theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by cases r <;> rfl
@[simp] theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with | (.ok a, s') => Mut.exec (f a) s' | (.error e, s') => (.error e, s') := by
  unfold Mut.exec; change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]; simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩; cases r <;> rfl
@[simp] theorem exec_map {σ α β : Type} (f : α → β) (m : Mut σ α) (s : σ) :
    Mut.exec (f <$> m) s =
      match Mut.exec m s with | (.ok a, s') => (.ok (f a), s') | (.error e, s') => (.error e, s') := by
  rw [map_eq_bind_pure_comp]; simp only [exec_bind, Function.comp_apply, exec_pure]
@[simp] theorem exec_onRatchet {PQ α : Type} (m : Mut RatchetState α) (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      ((Mut.exec m t.ratchet).1, { t with ratchet := (Mut.exec m t.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom; simp

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

private theorem mem_of_mem_eraseIdx {α : Type} {l : List α} {i : ℕ} {y : α}
    (h : y ∈ l.eraseIdx i) : y ∈ l := by
  induction l generalizing i with
  | nil => simp [List.eraseIdx] at h
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.eraseIdx] at h
      exact List.mem_cons_of_mem a h
    | succ i =>
      simp only [List.eraseIdx, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih h)

private theorem mem_of_mem_dropLast {α : Type} {l : List α} {y : α}
    (h : y ∈ l.dropLast) : y ∈ l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    cases l with
    | nil => simp at h
    | cons b l' =>
      simp only [List.dropLast, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih h)

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

/-! ## 32-byte skipped-key seed preservation -/

abbrev Bytes := List (BitVec 8)

/-- Every stored skipped-key seed in `s.receiverChains` has length 32 bytes. -/
def SeedsLen32 {PQ : Type} (s : SessionState PQ) : Prop :=
  ∀ c ∈ s.receiverChains, ∀ k ∈ c.messageKeys, k.seed.length = 32

/-- `SeedsLen32` for a bare `RatchetState`. -/
def RatchetSeedsLen32 (r : RatchetState) : Prop :=
  ∀ c ∈ r.receiverChains, ∀ k ∈ c.messageKeys, k.seed.length = 32

private theorem length_sha256With (F : ShaCompress) (m : List (BitVec 8)) :
    (HMAC.sha256With F m).length = 32 := by
  unfold HMAC.sha256With
  generalize (HMAC.chunks64 (HMAC.sha256Pad m)).foldl F HMAC.sha256IV = st
  rcases st with ⟨l, hl⟩
  simp [HMAC.toBEBytes, List.length_flatMap, hl]

theorem messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  simpa [ChainKey.messageKeys, Ratchet.chainHmac, HMAC.hmacWith] using
    length_sha256With F _

theorem evictReceiverChains_preserves (cs : List ReceiverChain)
    (h : ∀ c ∈ cs, ∀ k ∈ c.messageKeys, k.seed.length = 32) :
    ∀ c ∈ RatchetState.evictReceiverChains cs, ∀ k ∈ c.messageKeys, k.seed.length = 32 := by
  intro c hc
  exact h c (List.mem_of_mem_drop hc)

theorem takeSkippedKey_preserves (their : PublicKey) (counter : BitVec 32) (r : RatchetState)
    (h : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.takeSkippedKey their counter) r).2 := by
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
          intro c' hc' k hk
          rcases mem_set_cases hc' with rfl | hc'
          · exact h c (mem_of_getElem? h2) k (mem_of_mem_eraseIdx hk)
          · exact h c' hc' k hk

theorem storeSkippedKey_preserves (F : ShaCompress) (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) (h : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r).2 := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simpa [h1] using h
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simpa [h1, h2] using h
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      intro c' hc' k hk
      rcases mem_set_cases hc' with rfl | hc'
      · have hk' : k ∈ ck.messageKeys F :: c.messageKeys := by
          split at hk
          · exact mem_of_mem_dropLast hk
          · exact hk
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact messageKeys_seed_length F ck
        · exact h c (mem_of_getElem? h2) k hk'
      · exact h c' hc' k hk

theorem setReceiverChainKey_preserves (their : PublicKey) (ck : ChainKey) (r : RatchetState)
    (h : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2 := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simpa [h1] using h
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simpa [h1, h2] using h
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      intro c' hc' k hk
      rcases mem_set_cases hc' with rfl | hc'
      · exact h c (mem_of_getElem? h2) k hk
      · exact h c' hc' k hk

theorem advanceChain_preserves (F : ShaCompress) (their : PublicKey) (counter : BitVec 32)
    (fuel : ℕ) (ck : ChainKey) (r : RatchetState) (h : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2 := by
  induction fuel generalizing ck r with
  | zero => exact h
  | succ fuel ih =>
    unfold RatchetState.advanceChain
    split
    · rw [exec_bind]
      have h1 := storeSkippedKey_preserves F their ck r h
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨e | _, r1⟩
      · rw [hs] at h1; exact h1
      · rw [hs] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck.nextChainKey F with _ | ck'
        · exact h1
        · exact ih ck' r1 h1
    · exact h

theorem consumeMessageKey_preserves (F : ShaCompress) (their : PublicKey) (ck : ChainKey)
    (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) (h : RatchetSeedsLen32 r) :
    RatchetSeedsLen32
      (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2 := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    have h1 := takeSkippedKey_preserves their counter r h
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨e | opt, r1⟩
    · rw [ht] at h1; exact h1
    · rw [ht] at h1; cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    split
    · simpa using h
    · rw [exec_bind]
      have h1 := advanceChain_preserves F their counter (counter - ck.index).toNat ck r h
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨e | ck1, r1⟩
      · rw [ha] at h1; exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_preserves their ck2 r1 h1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨e | _, r2⟩ <;>
            · rw [hs] at h2; exact h2

theorem dhRatchetStep_preserves (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.dhRatchetStep C their coins) r).2 := by
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
      · intro c hc k hk
        have hcs : ∀ c0 ∈ r.receiverChains ++ [⟨their, some receiverChainKey, []⟩],
            ∀ k0 ∈ c0.messageKeys, k0.seed.length = 32 := by
          intro c0 hc0 k0 hk0
          rcases List.mem_append.mp hc0 with hc0 | hc0
          · exact h c0 hc0 k0 hk0
          · simp only [List.mem_singleton] at hc0
            subst hc0
            simp at hk0
        exact evictReceiverChains_preserves _ hcs c hc k hk

theorem ensureReceiverChain_preserves (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) (h : RatchetSeedsLen32 r) :
    RatchetSeedsLen32 (Mut.exec (RatchetState.ensureReceiverChain C their coins) r).2 := by
  unfold RatchetState.ensureReceiverChain
  simp only [exec_bind, exec_get, exec_liftE]
  rcases hf : r.findReceiverChainKey their with _ | (_ | ck)
  · exact h
  · exact dhRatchetStep_preserves C their coins r h
  · simpa using h

theorem tr_fromSessionState_ratchet {PQ : Type} [Inhabited PQ] (st : SessionState PQ)
    (h : SeedsLen32 st) (t : TripleRatchet PQ) (st' : SessionState PQ)
    (ht : Mut.exec TripleRatchet.fromSessionState st = (.ok t, st')) :
    RatchetSeedsLen32 t.ratchet := by
  unfold TripleRatchet.fromSessionState SessionState.takeRatchetState
    SessionState.takePqRatchetState at ht
  rcases hrem : st.remoteIdentity with _ | remote
  · simp [hrem] at ht
  · simp [hrem] at ht
    rcases ht with ⟨rfl, _⟩
    exact h

theorem tr_fromSessionState_state {PQ : Type} [Inhabited PQ] (st : SessionState PQ) :
    SeedsLen32 (Mut.exec (TripleRatchet.fromSessionState (PQ := PQ)) st).2 := by
  unfold TripleRatchet.fromSessionState SessionState.takeRatchetState
    SessionState.takePqRatchetState
  rcases hrem : st.remoteIdentity with _ | remote <;>
    simp [SeedsLen32, hrem]

theorem tr_decrypt_preserves {PQ PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (m : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (t : TripleRatchet PQ) (h : RatchetSeedsLen32 t.ratchet) :
    RatchetSeedsLen32
      (Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins) t).2.ratchet := by
  unfold TripleRatchet.decrypt
  rw [exec_bind, exec_onRatchet]
  have h1 := ensureReceiverChain_preserves C m.senderRatchetKey coins t.ratchet h
  rcases he : Mut.exec (RatchetState.ensureReceiverChain C m.senderRatchetKey coins) t.ratchet with
    ⟨e | ck, r1⟩
  · rw [he] at h1; exact h1
  · rw [he] at h1
    simp only [exec_bind, exec_onRatchet]
    have h2 := consumeMessageKey_preserves C.F m.senderRatchetKey ck m.counter msgType r1 h1
    rcases hc : Mut.exec (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType) r1 with
      ⟨e | mkg, r2⟩
    · rw [hc] at h2; exact h2
    · rw [hc] at h2
      simp only [exec_get]
      cases hpan : spqr.recvPanics t.pqrState m.pqRatchet
      case true => simpa [hpan] using h2
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hspqr : spqr.recv t.pqrState m.pqRatchet with (_ | _) | ⟨newPqrState, pqrKey⟩
      · simpa using h2
      · simpa using h2
      · simp only [exec_pure, exec_bind]
        split
        · simpa using h2
        · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
            (mkg.generateKeys C.F pqrKey).iv m.ciphertext with _ | ptext <;>
            simpa [haes] using h2

theorem tryDecryptWithState_preserves {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8))) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (st : SessionState PQ) (h : SeedsLen32 st) :
    SeedsLen32
      (Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) st).2 := by
  unfold SessionState.tryDecryptWithState
  rw [exec_bind]
  have hst1 := tr_fromSessionState_state st
  rcases htr : Mut.exec TripleRatchet.fromSessionState st with ⟨e | session, st1⟩
  · rw [htr] at hst1; exact hst1
  · rw [htr] at hst1
    have hr0 := tr_fromSessionState_ratchet st h session st1 htr
    have hr1 := tr_decrypt_preserves C spqr expected m msgType coins session hr0
    rcases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins) session with
      ⟨e | ptext, session'⟩
    · simp [hdec]; exact hst1
    · rw [hdec] at hr1
      simp only [hdec, exec_bind, exec_liftE, exec_modify, exec_pure]
      exact hr1

theorem tryDecryptFromRecord_preserves {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8))) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (st : SessionState PQ) (h : SeedsLen32 st) :
    SeedsLen32 (SessionState.tryDecryptFromRecord C spqr expected m msgType coins st).2 := by
  unfold SessionState.tryDecryptFromRecord
  split
  · exact h
  · have h1 := tryDecryptWithState_preserves C spqr expected m msgType coins st h
    rcases hd : Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) st with
      ⟨e | ptext, updated⟩
    · exact h
    · rw [hd] at h1; exact h1

/-! ## Protobuf `SessionRecord` encoding and scope predicates -/

/-- Session-model `send` ghost update (`Params.send`, success branch). -/
def ghostAfterSend {PQ : Type} (g : GhostState PQ) (s : SessionState PQ) : GhostState PQ :=
  { g with session := s, epoch := if g.party.sendsIn g.epoch then g.epoch else g.epoch + 1 }

/-- Session-model `receive` ghost update (`Params.receive`, success branch). -/
def ghostAfterRecv {PQ : Type} (g : GhostState PQ) (rk : PublicKey) (counter : BitVec 32)
    (s : SessionState PQ) (m : Bytes) : GhostState PQ × ℕ × ℕ × Bytes :=
  let idx := g.session.receiverChains.findIdx? (·.senderRatchetKey == rk)
  let (t, epochs, cur) := match idx with
    | some i => (g.chainEpochs.getD i 0, g.chainEpochs, g.epoch)
    | none => (g.epoch + 1, g.chainEpochs ++ [g.epoch + 1], g.epoch + 1)
  let epochs := epochs.drop (epochs.length - s.receiverChains.length)
  ({ g with session := s, epoch := cur, chainEpochs := epochs }, t, counter.toNat + 1, m)

theorem send_eq_afterSend {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC) (g : GhostState PQ)
    (m : Bytes) (r : PQC) :
    P.send g m r =
      match SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session with
      | (.ok msg, s) => (ghostAfterSend g s, msg.serialized)
      | (.error _, _) => (g, []) := rfl

theorem receive_eq_afterRecv {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC)
    (g : GhostState PQ) (c : Bytes) (rc : BitVec 256) :
    P.receive g c rc =
      match SignalMessage.tryFrom P.codec c with
      | .error _ => none
      | .ok msg =>
        match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
            rc g.session with
        | (.error _, _) => none
        | (.ok m, s) => some (ghostAfterRecv g msg.senderRatchetKey msg.counter s m) := rfl

def lenField (tag : ℕ) (payload : List (BitVec 8)) : List (BitVec 8) :=
  encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 payload.length) ++ payload
def bytesField (tag : ℕ) (v : List (BitVec 8)) : List (BitVec 8) :=
  if v = [] then [] else lenField tag v
def uint32Field (tag : ℕ) (v : BitVec 32) : List (BitVec 8) :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint (v.setWidth 64)
def uint64Field (tag : ℕ) (v : BitVec 64) : List (BitVec 8) :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint v
def int32Field (tag : ℕ) (v : BitVec 32) : List (BitVec 8) :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint (v.signExtend 64)
def optUint32Field (tag : ℕ) : Option (BitVec 32) → List (BitVec 8)
  | none => [] | some v => encodeKey tag .varint ++ encodeVarint (v.setWidth 64)
def msgField (tag : ℕ) : Option (List (BitVec 8)) → List (BitVec 8)
  | none => [] | some body => lenField tag body
def encChainKey (ck : ChainKey) : List (BitVec 8) :=
  uint32Field 1 ck.index ++ bytesField 2 (HMAC.keyToBytes32 ck.key)
def encMessageKey (mk : MessageKeyGenerator) : List (BitVec 8) :=
  uint32Field 1 mk.counter ++ bytesField 5 mk.seed
def encSenderChain (c : SenderChain) : List (BitVec 8) :=
  bytesField 1 c.ratchetKey.publicKey.serialize ++ bytesField 2 c.ratchetKey.privateKey.bytes.toList ++
    msgField 3 (some (encChainKey c.chainKey))
def encReceiverChain (c : ReceiverChain) : List (BitVec 8) :=
  bytesField 1 c.senderRatchetKey.serialize ++ msgField 3 (c.chainKey.map encChainKey) ++
    (c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten
def encPendingPreKey (p : PendingPreKey) : List (BitVec 8) :=
  optUint32Field 1 p.preKeyId ++ bytesField 2 p.baseKey.serialize ++ int32Field 3 p.signedPreKeyId ++
    uint64Field 4 p.timestamp
def encPendingKyber (p : PendingKyberPreKey) : List (BitVec 8) :=
  uint32Field 1 p.preKeyId ++ bytesField 2 p.ciphertext
def encSession (s : Session (List (BitVec 8))) : List (BitVec 8) :=
  let st := s.state
  uint32Field 1 st.sessionVersion ++ bytesField 2 st.localIdentity.serialize ++
  bytesField 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++ uint32Field 5 st.previousCounter ++
  msgField 6 (st.senderChain.map encSenderChain) ++
  (st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten ++
  msgField 9 (s.pendingPreKey.map encPendingPreKey) ++
  uint32Field 10 s.remoteRegistrationId ++ uint32Field 11 s.localRegistrationId ++
  bytesField 13 s.aliceBaseKey ++ msgField 14 (s.pendingKyberPreKey.map encPendingKyber) ++
  bytesField 15 st.pqRatchetState
def encodeRecord (r : SessionRecord (List (BitVec 8))) : List (BitVec 8) :=
  msgField 1 (r.currentSession.map encSession)
def RecordPqEmpty (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s → s.state.pqRatchetState = []
def RecordRepr (r : SessionRecord Bytes) : Prop :=
  ∀ s, r.currentSession = some s →
    (∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys) ∧
      (∀ sc, s.state.senderChain = some sc →
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) ∧
      s.Wf ∧ s.aliceBaseKey.length < 2 ^ 32
def SessionScopeP (s : Session Bytes) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧
    (∀ p, s.pendingPreKey = some p → p.timestamp = 0) ∧
    (∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length = 1569) ∧
    (s.aliceBaseKey = [] ∨ s.aliceBaseKey.length = 33)
def RecordInScopeP (r : SessionRecord Bytes) : Prop :=
  ∀ s, r.currentSession = some s →
    SeedsLen32 s.state ∧ s.state.receiverChains.length < 2 ^ 32 ∧
      ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 32
def InScopeP (r : SessionRecord Bytes) : Prop := RecordInScopeP r ∧ RecordPqEmpty r ∧ RecordRepr r
def DeserializeScopeP (r : SessionRecord Bytes) : Prop :=
  InScopeP r ∧ ∃ s, r.currentSession = some s ∧ SessionScopeP s

/-! ## `SessRepr` and `RatchetRepr` preservation -/

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
        · simp only [List.length_dropLast, List.length_cons]; omega
        · simp only [List.length_cons] at hlt ⊢; omega
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
      · rw [hs] at h1; exact h1
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
    · rw [ht] at h1; exact h1
    · rw [ht] at h1; cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    split
    · simpa using h
    · rw [exec_bind]
      have h1 := advanceChain_ratchetRepr F their counter (counter - ck.index).toNat ck r h
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨e | ck1, r1⟩
      · rw [ha] at h1; exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_ratchetRepr their ck2 r1 h1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨e | _, r2⟩ <;>
            · rw [hs] at h2; exact h2

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

theorem length_evictReceiverChains_le (cs : List ReceiverChain) :
    (RatchetState.evictReceiverChains cs).length ≤ maxReceiverChains := by
  unfold RatchetState.evictReceiverChains maxReceiverChains; rw [List.length_drop]; omega
theorem takeSkippedKey_receiverChains_length (their : PublicKey) (counter : BitVec 32) (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.takeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx; · simp [h1]
  rcases h2 : r.receiverChains[chainIdx]? with _ | c; · simp [h1, h2]
  rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos; · simp [h1, h2, h3]
  rcases h4 : c.messageKeys[pos]? with _ | key <;> simp [h1, h2, h3, h4]
theorem storeSkippedKey_receiverChains_length (their : PublicKey) (key : MessageKeyGenerator) (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx; · simp [h1]
  rcases h2 : r.receiverChains[chainIdx]? with _ | c <;> simp [h1, h2]
theorem setReceiverChainKey_receiverChains_length (their : PublicKey) (ck : ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx; · simp [h1]
  rcases h2 : r.receiverChains[chainIdx]? with _ | c <;> simp [h1, h2]
private theorem advanceChain_receiverChains_length (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : ℕ) (ck : ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains.length = r.receiverChains.length := by
  induction fuel generalizing ck r with
  | zero => rfl
  | succ fuel ih =>
    unfold RatchetState.advanceChain; split
    · rw [exec_bind]; have h1 := storeSkippedKey_receiverChains_length their (ck.messageKeys F) r
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with ⟨e | _, r1⟩
      · rw [hs] at h1; exact h1
      · rw [hs] at h1; simp only [exec_bind, exec_liftE]
        rcases hn : ck.nextChainKey F with _ | ck'; · exact h1
        exact (ih ck' r1).trans h1
    · rfl
theorem consumeMessageKey_receiverChains_length (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    have h1 := takeSkippedKey_receiverChains_length their counter r
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨e | opt, r1⟩
    · rw [ht] at h1; exact h1
    · rw [ht] at h1; cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]; split
    · rfl
    · rw [exec_bind]
      have h1 := advanceChain_receiverChains_length F their counter (counter - ck.index).toNat ck r
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨e | ck1, r1⟩
      · rw [ha] at h1; exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_receiverChains_length their ck2 r1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨e | _, r2⟩ <;>
            · rw [hs] at h2; exact h2.trans h1

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

theorem sessRepr_messageEncrypt_gen {PQC : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (S : Spqr Bytes PQC) (addresses : Option Bytes) (ptext : Bytes) (coins : PQC)
    (st st' : SessionState Bytes) (msg : SignalMessage) (hrep : SessRepr st)
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

theorem sessRepr_tryDecryptFromRecord_gen {PQC : Type} (C : Crypto) (S : Spqr Bytes PQC)
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

theorem messageEncrypt_ok_props_gen {PQC : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (S : Spqr Bytes PQC) (addresses : Option Bytes) (ptext : Bytes) (coins : PQC)
    (st st' : SessionState Bytes) (msg : SignalMessage) (hseeds : SeedsLen32 st)
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

theorem tr_decrypt_ok_props_gen {PQC : Type} (C : Crypto) (S : Spqr Bytes PQC)
    (expected : Option Bytes) (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
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

theorem tryDecryptFromRecord_ok_props_gen {PQC : Type} (C : Crypto) (S : Spqr Bytes PQC)
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
          obtain ⟨hlen', key, hrecv⟩ := tr_decrypt_ok_props_gen C S expected m msgType coins
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ tr' pt' hlen hdec
          exact ⟨hseeds', hlen', rfl, rfl, key, hrecv⟩

/-! ## Two-party `Role` and store helpers -/

inductive Role where | alice | bob deriving DecidableEq, Repr
def Role.ofWho (who : BitVec 32) : Option Role :=
  if who = 0#32 then some .alice else if who = 1#32 then some .bob else none
def Role.peer : Role → Role | .alice => .bob | .bob => .alice
def Role.ofParty : Party → Role | .A => .alice | .B => .bob
def evalOpen (who : BitVec 32) (sess : Session (List (BitVec 8))) :
    Option (Role × Session (List (BitVec 8))) :=
  match Role.ofWho who with | some r => some (r, sess) | none => none
def storedSession {Addr PQ : Type} (s0 : Session PQ) (calls : List (StoreCall Addr PQ)) :
    Session PQ :=
  calls.foldl (fun cur c => match c with | .storeSession _ ⟨some s'⟩ => s' | _ => cur) s0
def inMemAnswers (s : Session (List (BitVec 8))) : StoreAnswers (List (BitVec 8)) Unit where
  loadSession := .ok (some ⟨some s⟩)
  isTrustedIdentity := .ok true
  saveIdentity := .ok .newOrUnchanged
  storeSession := .ok ()

def RecordCanonical (stateBytes : List (BitVec 8)) (s : Session (List (BitVec 8))) : Prop :=
  stateBytes = encodeRecord ⟨some s⟩ ∧ DeserializeScopeP ⟨some s⟩
def recordDeserializeOpenSpec : Unit := ()

end Symbolic.Proofs.SpecLemmas.CliPureBytes

namespace CryptoVerification.E2E
export Symbolic.Proofs.SpecLemmas.CliPureBytes (   ghostAfterSend
  ghostAfterRecv send_eq_afterSend receive_eq_afterRecv )
end CryptoVerification.E2E
namespace CryptoVerification.E2E.Record
export Symbolic.Proofs.SpecLemmas.CliPureBytes (   ghostAfterSend
  ghostAfterRecv send_eq_afterSend receive_eq_afterRecv lenField bytesField uint32Field uint64Field
  int32Field optUint32Field msgField encChainKey encMessageKey encSenderChain encReceiverChain
  encPendingPreKey encPendingKyber encSession encodeRecord  RecordPqEmpty RecordRepr )
end CryptoVerification.E2E.Record
namespace CryptoVerification.E2E.RecordX
export Symbolic.Proofs.SpecLemmas.CliPureBytes (SessionScopeP RecordInScopeP InScopeP
  DeserializeScopeP  )
end CryptoVerification.E2E.RecordX
namespace CryptoVerification.E2E.Reach
export Symbolic.Proofs.SpecLemmas.CliPureBytes (SessRepr RatchetRepr clampScalar_idem
  clampScalar_keyPair_generate new_sessRepr addReceiverChain_sessRepr setSenderChain_sessRepr
  setUnacknowledgedPreKeyMessage_sessRepr takeSkippedKey_ratchetRepr storeSkippedKey_ratchetRepr
  setReceiverChainKey_ratchetRepr advanceChain_ratchetRepr consumeMessageKey_ratchetRepr
  dhRatchetStep_ratchetRepr ensureReceiverChain_ratchetRepr length_evictReceiverChains_le
  takeSkippedKey_receiverChains_length storeSkippedKey_receiverChains_length
  setReceiverChainKey_receiverChains_length consumeMessageKey_receiverChains_length
  dhRatchetStep_receiverChains_le ensureReceiverChain_receiverChains_le)
end CryptoVerification.E2E.Reach
namespace CryptoVerification.E2E.V1
export Symbolic.Proofs.SpecLemmas.CliPureBytes (sessRepr_messageEncrypt_gen
  sessRepr_tryDecryptFromRecord_gen messageEncrypt_ok_props_gen tr_decrypt_ok_props_gen
  tryDecryptFromRecord_ok_props_gen  )
end CryptoVerification.E2E.V1
namespace CryptoVerification.E2E.Bin
export Symbolic.Proofs.SpecLemmas.CliPureBytes (
    Role  evalOpen storedSession inMemAnswers
   encodeRecord RecordCanonical recordDeserializeOpenSpec)
namespace Role
export Symbolic.Proofs.SpecLemmas.CliPureBytes.Role (alice bob ofWho peer
      ofParty)
end Role
end CryptoVerification.E2E.Bin
namespace CryptoVerification.TripleRatchet.Seeds
export Symbolic.Proofs.SpecLemmas.CliPureBytes (RatchetSeedsLen32 messageKeys_seed_length
  evictReceiverChains_preserves takeSkippedKey_preserves
  storeSkippedKey_preserves setReceiverChainKey_preserves advanceChain_preserves
  consumeMessageKey_preserves dhRatchetStep_preserves ensureReceiverChain_preserves
  tr_fromSessionState_ratchet tr_fromSessionState_state tr_decrypt_preserves
  tryDecryptWithState_preserves tryDecryptFromRecord_preserves)
end CryptoVerification.TripleRatchet.Seeds
namespace CryptoVerification.LibsignalTripleRatchet.Seeds
export Symbolic.Proofs.SpecLemmas.CliPureBytes (RatchetSeedsLen32 messageKeys_seed_length
  evictReceiverChains_preserves takeSkippedKey_preserves
  storeSkippedKey_preserves setReceiverChainKey_preserves advanceChain_preserves
  consumeMessageKey_preserves dhRatchetStep_preserves ensureReceiverChain_preserves
  tr_fromSessionState_ratchet tr_fromSessionState_state tr_decrypt_preserves
  tryDecryptWithState_preserves tryDecryptFromRecord_preserves)
end CryptoVerification.LibsignalTripleRatchet.Seeds
namespace CryptoVerification.LibsignalPublicApi end CryptoVerification.LibsignalPublicApi
namespace CryptoVerification.E2E.Pqxdh.WireEntries end CryptoVerification.E2E.Pqxdh.WireEntries
