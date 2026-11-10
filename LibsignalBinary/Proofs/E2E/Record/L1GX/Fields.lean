/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP

/-!
# Pure field list for PQXDH-scope session deserialization

Connects `genFieldsX` and `recFieldsX` to `encSession` and `encodeRecord` on `DeserializeScopeP`
records: byte-level field decomposition, per-field well-formedness and freshness invariants, final
decoded state `ssgxOf`, and the `2 ^ 20` encoded-length bound.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.RecordX

/-! ## Base session projection -/

/-- Projects `s` onto its `DeserializeGeneral` subset by clearing pending pre-keys, registration
IDs, `aliceBaseKey`, and `pqRatchetState`. -/
def baseSession (s : Session (List (BitVec 8))) : Session (List (BitVec 8)) :=
  { s with
    state := { s.state with pendingPreKey := false, pqRatchetState := [] }
    localRegistrationId := 0
    remoteRegistrationId := 0
    pendingPreKey := none
    pendingKyberPreKey := none
    aliceBaseKey := [] }

/-- Single-session record wrapping `baseSession s`. -/
def baseRecord (s : Session (List (BitVec 8))) : SessionRecord (List (BitVec 8)) :=
  ⟨some (baseSession s)⟩


private theorem serialize_pk_ne_nil_x (pk : PublicKey) : pk.serialize ≠ [] := by
  intro h
  have hlen := serialize_pk_length' pk
  rw [h] at hlen
  cases hlen

private theorem identityKey_serialize_length_x (ik : IdentityKey) : ik.serialize.length = 33 :=
  serialize_pk_length' ik.publicKey

private theorem keyToBytes32_length_x (k : BitVec 256) : (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]

/-- Extracts `SessionScopeP s` for the current session of a `DeserializeScopeP` record. -/
theorem deserializeScopeP_session {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP r)
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s) : SessionScopeP s := by
  obtain ⟨_, s', hs', hsc⟩ := hr
  rw [hs] at hs'
  cases hs'
  exact hsc

theorem recFields_baseRecord (s : Session (List (BitVec 8))) :
    recFields (baseRecord s) = genFields (baseSession s) := rfl

private theorem genField_enc_lenField_x (fl : GenField) :
    (∀ b, fl = .lik b → fl.enc = lenField 2 b) ∧
    (∀ b, fl = .rik b → fl.enc = lenField 3 b) ∧
    (∀ b, fl = .root b → fl.enc = lenField 4 b) ∧
    (∀ c, fl = .sender c → fl.enc = lenField 6 c.enc) ∧
    (∀ c, fl = .recv c → fl.enc = lenField 7 c.enc) ∧
    (∀ k, fl = .pending k → fl.enc = lenField 9 (lenField 2 k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rintro _ rfl; simp [GenField.enc, GenField.tag, GenField.wt, GenField.payload,
      ChainG.payload, lenField, List.append_assoc])

private theorem senderChainG_enc_eq_x (c : SenderChain) :
    (senderChainG c).enc = encSenderChain c := by
  simp [senderChainG, ChainG.enc, encSenderChain, encChainKey]

private theorem recvChainG_enc_eq_x (c : ReceiverChain) :
    (recvChainG c).enc = encReceiverChain c := by
  unfold recvChainG ChainG.enc encReceiverChain
  rcases c.chainKey with _ | ck <;>
    simp [bytesField, encChainKey]

private theorem recvChains_flatMap_enc_x (cs : List ReceiverChain) :
    (cs.map (fun c => GenField.recv (recvChainG c))).flatMap GenField.enc =
      (cs.map (fun c => lenField 7 (encReceiverChain c))).flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.flatMap_cons, List.flatten_cons, ← ih,
      (genField_enc_lenField_x (.recv (recvChainG c))).2.2.2.2.1 _ rfl, recvChainG_enc_eq_x]

private theorem encSession_baseSession_eq (s : Session (List (BitVec 8))) :
    encSession (baseSession s) = (genFields (baseSession s)).flatMap GenField.enc := by
  unfold encSession genFields baseSession
  dsimp only
  simp only [List.flatMap_append, recvChains_flatMap_enc_x,
    show uint32Field 10 0 = [] from rfl,
    show uint32Field 11 0 = [] from rfl,
    show bytesField 13 [] = [] from rfl,
    show msgField 9 (none.map encPendingPreKey) = [] from rfl,
    show msgField 14 (none.map encPendingKyber) = [] from rfl,
    show bytesField 15 [] = [] from rfl,
    List.append_nil]
  have h1 : uint32Field 1 s.state.sessionVersion =
      (if s.state.sessionVersion = 0 then [] else [GenField.version s.state.sessionVersion]).flatMap
        GenField.enc := by
    unfold uint32Field; split_ifs <;> simp [GenField.enc, GenField.tag, GenField.wt, GenField.payload]
  have h2 : bytesField 2 s.state.localIdentity.serialize =
      (if s.state.localIdentity.serialize = [] then []
       else [GenField.lik s.state.localIdentity.serialize]).flatMap GenField.enc := by
    unfold bytesField; split_ifs <;>
      simp [(genField_enc_lenField_x _).1 _ rfl]
  have h3 : bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD []) =
      (match s.state.remoteIdentity with
       | some ik => if ik.serialize = [] then [] else [GenField.rik ik.serialize]
       | none => []).flatMap GenField.enc := by
    rcases s.state.remoteIdentity with _ | ik
    · rfl
    · dsimp only [Option.map_some, Option.getD_some]
      unfold bytesField; split_ifs <;>
        simp [(genField_enc_lenField_x _).2.1 _ rfl]
  have h4 : bytesField 4 (HMAC.keyToBytes32 s.state.rootKey) =
      (if HMAC.keyToBytes32 s.state.rootKey = [] then []
       else [GenField.root (HMAC.keyToBytes32 s.state.rootKey)]).flatMap GenField.enc := by
    unfold bytesField; split_ifs <;>
      simp [(genField_enc_lenField_x _).2.2.1 _ rfl]
  have h5 : uint32Field 5 s.state.previousCounter =
      (if s.state.previousCounter = 0 then [] else [GenField.prevCounter s.state.previousCounter]).flatMap
        GenField.enc := by
    unfold uint32Field; split_ifs <;> simp [GenField.enc, GenField.tag, GenField.wt, GenField.payload]
  have h6 : msgField 6 (s.state.senderChain.map encSenderChain) =
      (match s.state.senderChain with
       | some c => [GenField.sender (senderChainG c)]
       | none => []).flatMap GenField.enc := by
    rcases s.state.senderChain with _ | c
    · rfl
    · simp [msgField, (genField_enc_lenField_x _).2.2.2.1 _ rfl, senderChainG_enc_eq_x]
  rw [h1, h2, h3, h4, h5, h6]
  rcases s.state.remoteIdentity with _ | ik <;>
    rcases s.state.senderChain with _ | c <;>
    simp only [List.append_assoc]

/-! ## Encoded byte decomposition -/

private theorem encSession_eq_base (s : Session (List (BitVec 8))) :
    encSession s = encSession (baseSession s) ++ msgField 9 (s.pendingPreKey.map encPendingPreKey) ++
      uint32Field 10 s.remoteRegistrationId ++ uint32Field 11 s.localRegistrationId ++
      bytesField 13 s.aliceBaseKey ++ msgField 14 (s.pendingKyberPreKey.map encPendingKyber) ++
      bytesField 15 s.state.pqRatchetState := by
  unfold encSession baseSession
  simp only [Option.map_none,
    show uint32Field 10 0 = [] from rfl, show uint32Field 11 0 = [] from rfl,
    show bytesField 13 [] = [] from rfl, show msgField 9 none = [] from rfl,
    show msgField 14 none = [] from rfl, show bytesField 15 [] = [] from rfl,
    List.append_nil, List.append_assoc]

private theorem flatMap_map_base (xs : List GenField) :
    (xs.map GenFieldX.base).flatMap GenFieldX.enc = xs.flatMap GenField.enc := by
  induction xs with
  | nil => rfl
  | cons f xs ih =>
    simp only [List.map_cons, List.flatMap_cons, ih]
    rfl

private theorem pending_eq (o : Option PendingPreKey)
    (hp : ∀ p, o = some p → p.timestamp = 0) :
    msgField 9 (o.map encPendingPreKey) = (pendingFieldX o).flatMap GenFieldX.enc := by
  rcases o with _ | p
  · rfl
  · have hts := hp p rfl
    dsimp only [pendingFieldX]
    split_ifs with hspk
    · rcases hid : p.preKeyId with _ | i <;>
        simp [hspk, hid, msgField, encPendingPreKey, optUint32Field, int32Field,
          uint64Field, bytesField, serialize_pk_ne_nil_x, hts, GenFieldX.enc, GenFieldX.tag,
          GenFieldX.wt, GenFieldX.payload, GenField.tag, GenField.wt, GenField.payload,
          pendingIdBody, lenField]
    · simp [msgField, encPendingPreKey, uint64Field, bytesField, serialize_pk_ne_nil_x,
        hts, GenFieldX.enc, GenFieldX.tag, GenFieldX.wt, GenFieldX.payload, pendingSpkBody, lenField]

private theorem remReg_eq (v : BitVec 32) :
    uint32Field 10 v = (if v = 0 then [] else [GenFieldX.remReg v]).flatMap GenFieldX.enc := by
  unfold uint32Field
  split_ifs <;> simp [GenFieldX.enc, GenFieldX.tag, GenFieldX.wt, GenFieldX.payload]

private theorem locReg_eq (v : BitVec 32) :
    uint32Field 11 v = (if v = 0 then [] else [GenFieldX.locReg v]).flatMap GenFieldX.enc := by
  unfold uint32Field
  split_ifs <;> simp [GenFieldX.enc, GenFieldX.tag, GenFieldX.wt, GenFieldX.payload]

private theorem abk_eq (b : List (BitVec 8)) :
    bytesField 13 b = (if b = [] then [] else [GenFieldX.abk b]).flatMap GenFieldX.enc := by
  unfold bytesField
  split_ifs <;> simp [GenFieldX.enc, GenFieldX.tag, GenFieldX.wt, GenFieldX.payload, lenField]

private theorem kyber_eq (o : Option PendingKyberPreKey)
    (hk : ∀ k, o = some k → k.ciphertext.length = 1569) :
    msgField 14 (o.map encPendingKyber) =
      (match o with
       | some k => [GenFieldX.kyber k.preKeyId k.ciphertext]
       | none => []).flatMap GenFieldX.enc := by
  rcases o with _ | k
  · rfl
  · have hlen := hk k rfl
    have hne : k.ciphertext ≠ [] := by
      intro h; rw [h] at hlen; cases hlen
    simp [msgField, encPendingKyber, bytesField, hne, GenFieldX.enc,
      GenFieldX.tag, GenFieldX.wt, GenFieldX.payload, kyberBody, lenField]

private theorem pq_eq (b : List (BitVec 8)) :
    bytesField 15 b = (if b = [] then [] else [GenFieldX.pq b]).flatMap GenFieldX.enc := by
  unfold bytesField
  split_ifs <;> simp [GenFieldX.enc, GenFieldX.tag, GenFieldX.wt, GenFieldX.payload, lenField]

/-- For a PQXDH-scope session, `encSession s` equals the concatenation of `GenFieldX.enc` over `genFieldsX s`. -/
theorem encSession_eq_genFieldsX (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    encSession s = (genFieldsX s).flatMap GenFieldX.enc := by
  have hsc := deserializeScopeP_session hr hs
  have hb := encSession_baseSession_eq s
  obtain ⟨-, hpend, hky, -⟩ := hsc
  rw [encSession_eq_base s, hb]
  unfold genFieldsX
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_append, List.flatMap_append,
    List.flatMap_append, List.flatMap_append, flatMap_map_base,
    pending_eq _ hpend, remReg_eq, locReg_eq, abk_eq, kyber_eq _ hky, pq_eq]
  rfl

/-- Encodes a `DeserializeScopeP` record as outer key `0x0a`, payload-length varint, and encoded `recFieldsX r`. -/
theorem encodeRecord_eq_recFieldsX (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP r) :
    encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFieldsX r).flatMap GenFieldX.enc).length) ++
      (recFieldsX r).flatMap GenFieldX.enc := by
  have ⟨_, s, hs, _⟩ := hr
  have hrec : recFieldsX r = genFieldsX s := by simp [recFieldsX, hs]
  rw [hrec, ← encSession_eq_genFieldsX r hr s hs]
  simp [encodeRecord, hs, msgField, lenField]

/-! ## Field well-formedness -/

private theorem genFields_baseSession_ok (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    ∀ fl ∈ genFields { s with pendingPreKey := none }, fl.Ok := by
  obtain ⟨⟨hRecInScope, _, hRecRepr⟩, _⟩ := hr
  have hSeeds := (hRecInScope s hs).1
  have hMaxKeys := (hRecRepr s hs).1
  simp only [genFields, List.mem_append, List.mem_map]
  rintro fl (((((((h1 | h2) | h3) | h4) | h5) | h6) | ⟨c, hc, rfl⟩) | h9)
  · split_ifs at h1; · cases h1
    simp only [List.mem_singleton] at h1; subst h1; trivial
  · split_ifs at h2; · cases h2
    simp only [List.mem_singleton] at h2; subst h2
    exact identityKey_serialize_length_x _
  · rcases hrem : s.state.remoteIdentity with _ | ik <;> rw [hrem] at h3
    · cases h3
    · dsimp only at h3; split_ifs at h3; · cases h3
      simp only [List.mem_singleton] at h3; subst h3
      exact identityKey_serialize_length_x _
  · split_ifs at h4; · cases h4
    simp only [List.mem_singleton] at h4; subst h4
    exact keyToBytes32_length_x _
  · split_ifs at h5; · cases h5
    simp only [List.mem_singleton] at h5; subst h5; trivial
  · rcases hsc : s.state.senderChain with _ | c <;> rw [hsc] at h6
    · cases h6
    · simp only [List.mem_singleton] at h6; subst h6
      refine ⟨⟨serialize_pk_length' _, Or.inr (List.Vector.toList_length _), ?_, ?_,
        Nat.zero_le _⟩, List.Vector.toList_length _, rfl, rfl⟩
      · rintro ik hik
        simp only [senderChainG, Option.some.injEq] at hik
        subst hik
        exact keyToBytes32_length_x _
      · rintro m hm; cases hm
  · refine ⟨⟨serialize_pk_length' _, Or.inl rfl, ?_, ?_, hMaxKeys c hc⟩, rfl⟩
    · rintro ik hik
      dsimp only [recvChainG] at hik
      rcases hck : c.chainKey with _ | ck <;> rw [hck] at hik
      · cases hik
      · simp only [Option.map_some, Option.some.injEq] at hik
        subst hik
        exact keyToBytes32_length_x _
    · intro m hm
      exact hSeeds c hc m hm
  · cases h9

/-- Every field in `recFieldsX r` of a `DeserializeScopeP` record satisfies `GenFieldX.Ok`. -/
theorem recFieldsX_ok (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP r) :
    ∀ fl ∈ recFieldsX r, fl.Ok := by
  obtain ⟨s, hs, -⟩ := hr.2
  have hbase := genFields_baseSession_ok r hr s hs
  obtain ⟨-, -, hky, habk⟩ := deserializeScopeP_session hr hs
  simp only [recFieldsX, hs, genFieldsX, List.mem_append, List.mem_map]
  rintro fl ((((((⟨f, hf, rfl⟩ | h9) | h10) | h11) | h13) | h14) | h15)
  · exact hbase f hf
  · rcases hp : s.pendingPreKey with _ | p <;> rw [hp] at h9
    · cases h9
    · dsimp only [pendingFieldX] at h9
      split_ifs at h9 with hspk
      · rcases hid : p.preKeyId with _ | i <;> rw [hid] at h9 <;>
          simp only [List.mem_singleton] at h9 <;> subst h9
        · exact serialize_pk_length' _
        · exact serialize_pk_length' _
      · simp only [List.mem_singleton] at h9
        subst h9
        exact ⟨serialize_pk_length' _, hspk⟩
  · split_ifs at h10
    · cases h10
    · simp only [List.mem_singleton] at h10; subst h10; trivial
  · split_ifs at h11
    · cases h11
    · simp only [List.mem_singleton] at h11; subst h11; trivial
  · split_ifs at h13 with h
    · cases h13
    simp only [List.mem_singleton] at h13
    subst h13
    rcases habk with h' | h'
    · exact absurd h' h
    · exact h'
  · rcases hk : s.pendingKyberPreKey with _ | k <;> rw [hk] at h14
    · cases h14
    · simp only [List.mem_singleton] at h14
      subst h14
      exact hky k hk
  · split_ifs at h15
    · cases h15
    · simp only [List.mem_singleton] at h15; subst h15; trivial

/-! ## Freshness and final decoded value -/

private def FreshListB (v : SSG) (xs : List GenField) : Prop :=
  ∀ k (hk : k < xs.length), (xs[k]'hk).Fresh ((xs.take k).foldl SSG.apply v)

private theorem freshListB_nil (v : SSG) : FreshListB v [] := by
  intro k hk; cases hk

private theorem freshListB_singleton {v : SSG} {fl : GenField} (h : fl.Fresh v) :
    FreshListB v [fl] := by
  intro k hk
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0
  exact h

private theorem freshListB_append {v : SSG} {xs ys : List GenField}
    (hxs : FreshListB v xs) (hys : FreshListB (xs.foldl SSG.apply v) ys) :
    FreshListB v (xs ++ ys) := by
  intro k hk
  by_cases hlt : k < xs.length
  · rw [List.getElem_append_left hlt, List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact hxs k hlt
  · have hle : xs.length ≤ k := Nat.le_of_not_lt hlt
    have hj : k - xs.length < ys.length := by rw [List.length_append] at hk; omega
    have htake : (xs ++ ys).take k = xs ++ ys.take (k - xs.length) := by
      rw [List.take_append, List.take_of_length_le hle]
    rw [List.getElem_append_right hle, htake, List.foldl_append]
    exact hys (k - xs.length) hj

private theorem foldl_recvChains_x (ver : BitVec 32) (lik rik root : List (BitVec 8))
    (pc : BitVec 32) (acc : List ChainG) (snd : Option ChainG) (pnd : Option (List (BitVec 8)))
    (cs : List ReceiverChain) :
    (cs.map (fun c => GenField.recv (recvChainG c))).foldl SSG.apply
        ⟨ver, lik, rik, root, pc, acc, snd, pnd⟩ =
      ⟨ver, lik, rik, root, pc, acc ++ cs.map recvChainG, snd, pnd⟩ := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons, SSG.apply, ih, List.append_assoc,
      List.singleton_append]

private theorem freshListB_recvChains (ver : BitVec 32) (lik rik root : List (BitVec 8))
    (pc : BitVec 32) (acc : List ChainG) (snd : Option ChainG) (pnd : Option (List (BitVec 8)))
    (cs : List ReceiverChain) (hbound : acc.length + cs.length ≤ maxReceiverChains) :
    FreshListB ⟨ver, lik, rik, root, pc, acc, snd, pnd⟩
      (cs.map (fun c => GenField.recv (recvChainG c))) := by
  induction cs generalizing acc with
  | nil => exact freshListB_nil _
  | cons c cs ih =>
    rw [List.map_cons, ← List.singleton_append]
    refine freshListB_append (freshListB_singleton ?_) ?_
    · simp only [GenField.Fresh]
      simp only [List.length_cons] at hbound
      omega
    · dsimp only [List.foldl, SSG.apply]
      apply ih
      simp only [List.length_append, List.length_cons, List.length_nil] at hbound ⊢
      omega

private theorem foldl_step1_x (s : Session (List (BitVec 8))) :
    (if s.state.sessionVersion = 0 then [] else [GenField.version s.state.sessionVersion]).foldl
      SSG.apply SSG.empty = ⟨s.state.sessionVersion, [], [], [], 0, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.empty, SSG.apply, h]

private theorem foldl_step2_x (s : Session (List (BitVec 8))) (v1 : BitVec 32) :
    (if s.state.localIdentity.serialize = [] then []
     else [GenField.lik s.state.localIdentity.serialize]).foldl
      SSG.apply ⟨v1, [], [], [], 0, [], none, none⟩ =
      ⟨v1, s.state.localIdentity.serialize, [], [], 0, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.apply, h]

private theorem foldl_step3_some_x (ik : IdentityKey) (v1 : BitVec 32) (v2 : List (BitVec 8)) :
    (if ik.serialize = [] then [] else [GenField.rik ik.serialize]).foldl
      SSG.apply ⟨v1, v2, [], [], 0, [], none, none⟩ =
      ⟨v1, v2, ik.serialize, [], 0, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.apply, h]

private theorem foldl_step4_x (s : Session (List (BitVec 8))) (v1 : BitVec 32)
    (v2 v3 : List (BitVec 8)) :
    (if HMAC.keyToBytes32 s.state.rootKey = [] then []
     else [GenField.root (HMAC.keyToBytes32 s.state.rootKey)]).foldl
      SSG.apply ⟨v1, v2, v3, [], 0, [], none, none⟩ =
      ⟨v1, v2, v3, HMAC.keyToBytes32 s.state.rootKey, 0, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.apply, h]

private theorem foldl_step5_x (s : Session (List (BitVec 8))) (v1 : BitVec 32)
    (v2 v3 v4 : List (BitVec 8)) :
    (if s.state.previousCounter = 0 then [] else [GenField.prevCounter s.state.previousCounter]).foldl
      SSG.apply ⟨v1, v2, v3, v4, 0, [], none, none⟩ =
      ⟨v1, v2, v3, v4, s.state.previousCounter, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.apply, h]

private theorem genFields_baseSession_fresh (s : Session (List (BitVec 8)))
    (hmax : s.state.receiverChains.length ≤ maxReceiverChains) :
    FreshListB SSG.empty (genFields { s with pendingPreKey := none }) := by
  simp only [genFields]
  have hscalar : ∀ (v : SSG) (b : List GenField),
      (b = [] ∨ ∃ fl, b = [fl] ∧ fl.Fresh v) → FreshListB v b := by
    rintro v b (rfl | ⟨fl, rfl, hfl⟩)
    · exact freshListB_nil v
    · exact freshListB_singleton hfl
  rcases hrem : s.state.remoteIdentity with _ | ik <;>
    rcases hsc : s.state.senderChain with _ | c <;>
    dsimp only
  all_goals
    refine freshListB_append ?_ (freshListB_nil _)
    refine freshListB_append ?_ ?_
    · refine freshListB_append ?_ ?_
      · refine freshListB_append ?_ (hscalar _ _ (by split_ifs <;> simp [GenField.Fresh]))
        refine freshListB_append ?_ (hscalar _ _ (by split_ifs <;> simp [GenField.Fresh]))
        refine freshListB_append ?_ ?_
        · refine freshListB_append
            (hscalar _ _ (by split_ifs <;> simp [GenField.Fresh]))
            (hscalar _ _ (by split_ifs <;> simp [GenField.Fresh]))
        · first
          | exact freshListB_nil _
          | exact hscalar _ _ (by split_ifs <;> simp [GenField.Fresh])
      · simp only [List.foldl_append, foldl_step1_x, foldl_step2_x, foldl_step3_some_x,
          foldl_step4_x, foldl_step5_x, List.foldl_nil]
        first
        | exact freshListB_nil _
        | exact freshListB_singleton rfl
    · simp only [List.foldl_append, foldl_step1_x, foldl_step2_x, foldl_step3_some_x,
        foldl_step4_x, foldl_step5_x, List.foldl_nil, List.foldl_cons, SSG.apply]
      exact freshListB_recvChains _ _ _ _ _ [] _ _ _ (by simpa using hmax)

/-- Sequential freshness of `xs` starting from `v`: each field is fresh with respect to the state folded from earlier fields. -/
def FreshListX (v : SSGX) (xs : List GenFieldX) : Prop :=
  ∀ k (hk : k < xs.length), (xs[k]'hk).Fresh ((xs.take k).foldl SSGX.apply v)

private theorem freshListX_nil (v : SSGX) : FreshListX v [] := by
  intro k hk; cases hk

private theorem freshListX_singleton {v : SSGX} {fl : GenFieldX} (h : fl.Fresh v) :
    FreshListX v [fl] := by
  intro k hk
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0
  exact h

private theorem freshListX_append {v : SSGX} {xs ys : List GenFieldX}
    (hxs : FreshListX v xs) (hys : FreshListX (xs.foldl SSGX.apply v) ys) :
    FreshListX v (xs ++ ys) := by
  intro k hk
  by_cases hlt : k < xs.length
  · rw [List.getElem_append_left hlt, List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact hxs k hlt
  · have hle : xs.length ≤ k := Nat.le_of_not_lt hlt
    have hj : k - xs.length < ys.length := by rw [List.length_append] at hk; omega
    have htake : (xs ++ ys).take k = xs ++ ys.take (k - xs.length) := by
      rw [List.take_append, List.take_of_length_le hle]
    rw [List.getElem_append_right hle, htake, List.foldl_append]
    exact hys (k - xs.length) hj

/-- Folding `.base` fields updates only the `SSG` component of `SSGX`, leaving `ExtraG` unchanged. -/
theorem foldl_map_base (v : SSG) (e : ExtraG) (xs : List GenField) :
    (xs.map GenFieldX.base).foldl SSGX.apply ⟨v, e⟩ = ⟨xs.foldl SSG.apply v, e⟩ := by
  induction xs generalizing v with
  | nil => rfl
  | cons f xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih (v.apply f)

private theorem freshListX_base (xs : List GenField)
    (h : FreshListB SSG.empty xs) :
    FreshListX SSGX.empty (xs.map GenFieldX.base) := by
  intro k hk
  have hk' : k < xs.length := by simpa using hk
  rw [List.getElem_map, ← List.map_take,
    show SSGX.empty = ⟨SSG.empty, ExtraG.empty⟩ from rfl, foldl_map_base]
  exact ⟨rfl, h k hk'⟩

private theorem foldl_base_eq (s : Session (List (BitVec 8))) :
    ((genFields { s with pendingPreKey := none }).map GenFieldX.base).foldl SSGX.apply
      SSGX.empty = ⟨ssgOf (baseSession s), ExtraG.empty⟩ := by
  rw [show SSGX.empty = ⟨SSG.empty, ExtraG.empty⟩ from rfl, foldl_map_base]
  congr 1
  simp only [genFields, baseSession]
  rcases s.state.remoteIdentity with _ | ik <;>
    rcases s.state.senderChain with _ | c <;>
    simp only [ssgOf, List.foldl_append, foldl_step1_x, foldl_step2_x,
      foldl_step3_some_x, foldl_step4_x, foldl_step5_x, List.foldl_nil, List.foldl_cons,
      SSG.apply, foldl_recvChains_x, List.nil_append, Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some]

private theorem foldl_pendingFieldX (b : SSG) (hb : b.pending = none) (o : Option PendingPreKey) :
    (pendingFieldX o).foldl SSGX.apply ⟨b, ExtraG.empty⟩ =
      ⟨{ b with pending := o.map (·.baseKey.serialize) },
       ⟨o.bind (·.preKeyId), (o.map (·.signedPreKeyId)).getD 0, 0, 0, [], none, []⟩⟩ := by
  rcases o with _ | p
  · cases b; dsimp only at hb; subst hb; rfl
  · dsimp only [pendingFieldX]
    split_ifs with hspk
    · rcases hid : p.preKeyId with _ | i <;>
        simp [hspk, hid, SSGX.apply, SSG.apply, ExtraG.empty]
    · simp [SSGX.apply, ExtraG.empty]

private theorem freshListX_pendingFieldX (b : SSG) (hb : b.pending = none)
    (o : Option PendingPreKey) :
    FreshListX ⟨b, ExtraG.empty⟩ (pendingFieldX o) := by
  rcases o with _ | p
  · exact freshListX_nil _
  · dsimp only [pendingFieldX]
    split_ifs with hspk
    · rcases hid : p.preKeyId with _ | i
      · exact freshListX_singleton ⟨rfl, hb⟩
      · exact freshListX_singleton ⟨hb, rfl⟩
    · exact freshListX_singleton ⟨hb, rfl⟩

private theorem foldl_remReg (b : SSG) (pid : Option (BitVec 32)) (spkId remReg : BitVec 32) :
    (if remReg = 0 then [] else [GenFieldX.remReg remReg]).foldl SSGX.apply
      ⟨b, ⟨pid, spkId, 0, 0, [], none, []⟩⟩ = ⟨b, ⟨pid, spkId, remReg, 0, [], none, []⟩⟩ := by
  split_ifs with h <;> simp [h, SSGX.apply]

private theorem foldl_locReg (b : SSG) (pid : Option (BitVec 32)) (spkId remReg locReg : BitVec 32) :
    (if locReg = 0 then [] else [GenFieldX.locReg locReg]).foldl SSGX.apply
      ⟨b, ⟨pid, spkId, remReg, 0, [], none, []⟩⟩ = ⟨b, ⟨pid, spkId, remReg, locReg, [], none, []⟩⟩ := by
  split_ifs with h <;> simp [h, SSGX.apply]

private theorem foldl_abk (b : SSG) (pid : Option (BitVec 32)) (spkId remReg locReg : BitVec 32)
    (abk : List (BitVec 8)) :
    (if abk = [] then [] else [GenFieldX.abk abk]).foldl SSGX.apply
      ⟨b, ⟨pid, spkId, remReg, locReg, [], none, []⟩⟩ =
      ⟨b, ⟨pid, spkId, remReg, locReg, abk, none, []⟩⟩ := by
  split_ifs with h <;> simp [h, SSGX.apply]

private theorem foldl_kyber (b : SSG) (pid : Option (BitVec 32)) (spkId remReg locReg : BitVec 32)
    (abk : List (BitVec 8)) (ky : Option PendingKyberPreKey) :
    (match ky with
     | some k => [GenFieldX.kyber k.preKeyId k.ciphertext]
     | none => []).foldl SSGX.apply
      ⟨b, ⟨pid, spkId, remReg, locReg, abk, none, []⟩⟩ =
      ⟨b, ⟨pid, spkId, remReg, locReg, abk, ky.map (fun k => (k.preKeyId, k.ciphertext)), []⟩⟩ := by
  rcases ky with _ | k <;> simp [SSGX.apply]

private theorem freshListX_tail (b : SSG) (hb : b.pending = none) (o : Option PendingPreKey)
    (remReg locReg : BitVec 32) (abk : List (BitVec 8)) (ky : Option PendingKyberPreKey)
    (pq : List (BitVec 8)) :
    FreshListX ⟨b, ExtraG.empty⟩
      (pendingFieldX o ++
        (if remReg = 0 then [] else [GenFieldX.remReg remReg]) ++
        (if locReg = 0 then [] else [GenFieldX.locReg locReg]) ++
        (if abk = [] then [] else [GenFieldX.abk abk]) ++
        (match ky with
         | some k => [GenFieldX.kyber k.preKeyId k.ciphertext]
         | none => []) ++
        (if pq = [] then [] else [GenFieldX.pq pq])) := by
  refine freshListX_append (freshListX_append (freshListX_append (freshListX_append
    (freshListX_append (freshListX_pendingFieldX b hb o) ?_) ?_) ?_) ?_) ?_
  · rw [foldl_pendingFieldX _ hb]
    split_ifs
    · exact freshListX_nil _
    · exact freshListX_singleton rfl
  · rw [List.foldl_append, foldl_pendingFieldX _ hb, foldl_remReg]
    split_ifs
    · exact freshListX_nil _
    · exact freshListX_singleton rfl
  · rw [List.foldl_append, List.foldl_append, foldl_pendingFieldX _ hb, foldl_remReg, foldl_locReg]
    split_ifs
    · exact freshListX_nil _
    · exact freshListX_singleton rfl
  · rw [List.foldl_append, List.foldl_append, List.foldl_append, foldl_pendingFieldX _ hb,
      foldl_remReg, foldl_locReg, foldl_abk]
    rcases ky with _ | k
    · exact freshListX_nil _
    · exact freshListX_singleton rfl
  · rw [List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append,
      foldl_pendingFieldX _ hb, foldl_remReg, foldl_locReg, foldl_abk, foldl_kyber]
    split_ifs
    · exact freshListX_nil _
    · exact freshListX_singleton rfl

/-- The `k`-th field of `recFieldsX r` is fresh with respect to the prefix state `ssgxAfter r k`. -/
theorem recFieldsX_fresh (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP r) (k : Nat)
    (hk : k < (recFieldsX r).length) :
    ((recFieldsX r)[k]'hk).Fresh (ssgxAfter r k) := by
  obtain ⟨s, hs, hsc⟩ := hr.2
  revert k hk
  change FreshListX SSGX.empty (recFieldsX r)
  simp only [recFieldsX, hs, genFieldsX]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc]
  refine freshListX_append ?_ ?_
  · exact freshListX_base _ (genFields_baseSession_fresh s hsc.1)
  · rw [foldl_base_eq s, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
      ← List.append_assoc]
    exact freshListX_tail _ rfl _ _ _ _ _ _

/-- Folding all fields of `recFieldsX r` yields `ssgxOf s`. -/
theorem ssgxAfter_recFieldsX (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    ssgxAfter r (recFieldsX r).length = ssgxOf s := by
  have _ := hr
  unfold ssgxAfter
  rw [List.take_length]
  simp only [recFieldsX, hs, genFieldsX, List.foldl_append]
  rw [foldl_base_eq s, foldl_pendingFieldX _ rfl, foldl_remReg, foldl_locReg, foldl_abk]
  rcases hk : s.pendingKyberPreKey with _ | k <;>
    split_ifs with hpq <;>
    simp [ssgxOf, ssgOf, baseSession, hk, hpq, SSGX.apply]

/-! ## Encoded record length bound -/


private theorem encChainKey_length_le_x (ck : ChainKey) :
    (encChainKey ck).length ≤ 72 := by
  unfold encChainKey
  have h1 : (uint32Field 1 ck.index).length ≤ 20 := uint32Field_length_le' 1 ck.index
  have h2 : (bytesField 2 (HMAC.keyToBytes32 ck.key)).length ≤
      (HMAC.keyToBytes32 ck.key).length + 20 :=
    bytesField_length_le' 2 (HMAC.keyToBytes32 ck.key)
  rw [keyToBytes32_length_x] at h2
  simp only [List.length_append]
  omega

private theorem lenField_encMessageKey_length_le_x (mk : MessageKeyGenerator)
    (hseed : mk.seed.length = 32) :
    (lenField 4 (encMessageKey mk)).length ≤ 92 := by
  have h0 : (lenField 4 (encMessageKey mk)).length ≤ (encMessageKey mk).length + 20 :=
    lenField_length_le' 4 (encMessageKey mk)
  have heq : (encMessageKey mk).length =
      (uint32Field 1 mk.counter).length + (bytesField 5 mk.seed).length := by
    simp [encMessageKey]
  have h1 : (uint32Field 1 mk.counter).length ≤ 20 := uint32Field_length_le' 1 mk.counter
  have h2 : (bytesField 5 mk.seed).length ≤ mk.seed.length + 20 :=
    bytesField_length_le' 5 mk.seed
  rw [hseed] at h2
  omega

private theorem flatten_encMessageKeys_length_le_x (mks : List MessageKeyGenerator)
    (hseeds : ∀ mk ∈ mks, mk.seed.length = 32) :
    ((mks.map fun mk => lenField 4 (encMessageKey mk)).flatten).length ≤ 92 * mks.length := by
  induction mks with
  | nil => simp
  | cons mk mks ih =>
    have hmk := lenField_encMessageKey_length_le_x mk (hseeds mk (by simp))
    have hmks := ih (fun m hm => hseeds m (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

private theorem lenField_encReceiverChain_length_le_x (c : ReceiverChain)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32)
    (hmax : c.messageKeys.length ≤ maxMessageKeys) :
    (lenField 7 (encReceiverChain c)).length ≤ 184165 := by
  have h0 : (lenField 7 (encReceiverChain c)).length ≤ (encReceiverChain c).length + 20 :=
    lenField_length_le' 7 (encReceiverChain c)
  have heq : (encReceiverChain c).length =
      (bytesField 1 c.senderRatchetKey.serialize).length +
      (msgField 3 (c.chainKey.map encChainKey)).length +
      ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length := by
    simp only [encReceiverChain, List.length_append]
  have h1 : (bytesField 1 c.senderRatchetKey.serialize).length ≤
      c.senderRatchetKey.serialize.length + 20 :=
    bytesField_length_le' 1 c.senderRatchetKey.serialize
  rw [serialize_pk_length'] at h1
  have h2 : (msgField 3 (c.chainKey.map encChainKey)).length ≤ 92 := by
    rcases c.chainKey with _ | ck
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have hck := encChainKey_length_le_x ck
      have hlf : (lenField 3 (encChainKey ck)).length ≤ (encChainKey ck).length + 20 :=
        lenField_length_le' 3 (encChainKey ck)
      omega
  have h3 := flatten_encMessageKeys_length_le_x c.messageKeys hseeds
  have hmax_val : maxMessageKeys = 2000 := rfl
  omega

private theorem flatten_encReceiverChains_length_le_x (cs : List ReceiverChain)
    (hseeds : ∀ c ∈ cs, ∀ mk ∈ c.messageKeys, mk.seed.length = 32)
    (hmax : ∀ c ∈ cs, c.messageKeys.length ≤ maxMessageKeys) :
    ((cs.map fun c => lenField 7 (encReceiverChain c)).flatten).length ≤ 184165 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := lenField_encReceiverChain_length_le_x c (hseeds c (by simp)) (hmax c (by simp))
    have hcs := ih (fun c' hc' => hseeds c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hmax c' (List.mem_cons_of_mem _ hc'))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- Any `DeserializeScopeP` record encodes to fewer than `2 ^ 20` bytes. -/
theorem encodeRecord_length_ltX {r : SessionRecord (List (BitVec 8))} (h : DeserializeScopeP r) :
    (encodeRecord r).length < 2 ^ 20 := by
  obtain ⟨s, hs, -⟩ := h.2
  have hsc := deserializeScopeP_session h hs
  obtain ⟨⟨hRecInScope, hPqEmpty, hRecRepr⟩, -⟩ := h
  have hSeeds := (hRecInScope s hs).1
  have hMaxKeys := (hRecRepr s hs).1
  obtain ⟨hMaxChains, -, hky, habk⟩ := hsc
  have hMaxChains_val : maxReceiverChains = 5 := rfl
  have hrec : (lenField 1 (encSession s)).length ≤ (encSession s).length + 20 :=
    lenField_length_le' 1 (encSession s)
  have henc : encodeRecord r = lenField 1 (encSession s) := by
    simp [encodeRecord, hs, msgField]
  rw [henc]
  have hlen : (encSession s).length =
      (uint32Field 1 s.state.sessionVersion).length +
      (bytesField 2 s.state.localIdentity.serialize).length +
      (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length +
      (bytesField 4 (HMAC.keyToBytes32 s.state.rootKey)).length +
      (uint32Field 5 s.state.previousCounter).length +
      (msgField 6 (s.state.senderChain.map encSenderChain)).length +
      ((s.state.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten).length +
      (msgField 9 (s.pendingPreKey.map encPendingPreKey)).length +
      (uint32Field 10 s.remoteRegistrationId).length +
      (uint32Field 11 s.localRegistrationId).length +
      (bytesField 13 s.aliceBaseKey).length +
      (msgField 14 (s.pendingKyberPreKey.map encPendingKyber)).length +
      (bytesField 15 s.state.pqRatchetState).length := by
    simp only [encSession, List.length_append]
  have h1 : (uint32Field 1 s.state.sessionVersion).length ≤ 20 :=
    uint32Field_length_le' 1 s.state.sessionVersion
  have h2 : (bytesField 2 s.state.localIdentity.serialize).length ≤
      s.state.localIdentity.serialize.length + 20 :=
    bytesField_length_le' 2 s.state.localIdentity.serialize
  rw [show s.state.localIdentity.serialize.length = 33 from
    serialize_pk_length' s.state.localIdentity.publicKey] at h2
  have h3 : (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤
      53 := by
    rcases s.state.remoteIdentity with _ | ik
    · simp [bytesField]
    · dsimp only [Option.map_some, Option.getD_some]
      have : (bytesField 3 ik.serialize).length ≤ ik.serialize.length + 20 :=
        bytesField_length_le' 3 ik.serialize
      rw [show ik.serialize.length = 33 from serialize_pk_length' ik.publicKey] at this
      exact this
  have h4 : (bytesField 4 (HMAC.keyToBytes32 s.state.rootKey)).length ≤
      (HMAC.keyToBytes32 s.state.rootKey).length + 20 :=
    bytesField_length_le' 4 (HMAC.keyToBytes32 s.state.rootKey)
  rw [keyToBytes32_length_x] at h4
  have h5 : (uint32Field 5 s.state.previousCounter).length ≤ 20 :=
    uint32Field_length_le' 5 s.state.previousCounter
  have h6 : (msgField 6 (s.state.senderChain.map encSenderChain)).length ≤ 217 := by
    rcases s.state.senderChain with _ | sc
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have h0 : (lenField 6 (encSenderChain sc)).length ≤ (encSenderChain sc).length + 20 :=
        lenField_length_le' 6 (encSenderChain sc)
      have heq : (encSenderChain sc).length =
          (bytesField 1 sc.ratchetKey.publicKey.serialize).length +
          (bytesField 2 sc.ratchetKey.privateKey.bytes.toList).length +
          (lenField 3 (encChainKey sc.chainKey)).length := by
        simp only [encSenderChain, msgField, List.length_append]
      have ha : (bytesField 1 sc.ratchetKey.publicKey.serialize).length ≤
          sc.ratchetKey.publicKey.serialize.length + 20 :=
        bytesField_length_le' 1 sc.ratchetKey.publicKey.serialize
      rw [serialize_pk_length'] at ha
      have hb : (bytesField 2 sc.ratchetKey.privateKey.bytes.toList).length ≤
          sc.ratchetKey.privateKey.bytes.toList.length + 20 :=
        bytesField_length_le' 2 sc.ratchetKey.privateKey.bytes.toList
      rw [List.Vector.toList_length] at hb
      have hc : (lenField 3 (encChainKey sc.chainKey)).length ≤
          (encChainKey sc.chainKey).length + 20 :=
        lenField_length_le' 3 (encChainKey sc.chainKey)
      have hd := encChainKey_length_le_x sc.chainKey
      omega
  have h7 := flatten_encReceiverChains_length_le_x s.state.receiverChains hSeeds hMaxKeys
  have h9 := msgField9_length_leP s.pendingPreKey
  have h10 : (uint32Field 10 s.remoteRegistrationId).length ≤ 20 :=
    uint32Field_length_le' 10 s.remoteRegistrationId
  have h11 : (uint32Field 11 s.localRegistrationId).length ≤ 20 :=
    uint32Field_length_le' 11 s.localRegistrationId
  have h13 : (bytesField 13 s.aliceBaseKey).length ≤ 53 := by
    have : (bytesField 13 s.aliceBaseKey).length ≤ s.aliceBaseKey.length + 20 :=
      bytesField_length_le' 13 s.aliceBaseKey
    rcases habk with ha | ha
    · rw [ha]; simp [bytesField]
    · omega
  have h14 : (msgField 14 (s.pendingKyberPreKey.map encPendingKyber)).length ≤ 1649 := by
    rcases hk : s.pendingKyberPreKey with _ | k
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have h0 : (lenField 14 (encPendingKyber k)).length ≤ (encPendingKyber k).length + 20 :=
        lenField_length_le' 14 (encPendingKyber k)
      have heq : (encPendingKyber k).length =
          (uint32Field 1 k.preKeyId).length + (bytesField 2 k.ciphertext).length := by
        simp only [encPendingKyber, List.length_append]
      have ha : (uint32Field 1 k.preKeyId).length ≤ 20 := uint32Field_length_le' 1 k.preKeyId
      have hb : (bytesField 2 k.ciphertext).length ≤ k.ciphertext.length + 20 :=
        bytesField_length_le' 2 k.ciphertext
      rw [hky k hk] at hb
      omega
  have h15 : (bytesField 15 s.state.pqRatchetState).length = 0 := by
    rw [hPqEmpty s hs]; rfl
  omega

end CryptoVerification.E2E.Record.L1GX
