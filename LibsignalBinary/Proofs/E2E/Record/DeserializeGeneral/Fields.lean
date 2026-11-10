/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs

/-!
# Pure Wire-Field Decomposition and Length Bounds for General `SessionRecord`

Proves wire-byte equivalence (`encSession_eq_genFields`, `encodeRecord_eq_recFields`,
`chainG_enc_eq_fields`), per-field well-formedness and freshness (`recFields_ok`,
`recFields_fresh`), fold reconstruction (`ssgAfter_recFields`, `chainGAfter_fields`), and the
`< 2 ^ 20` byte-length bound (`encodeRecord_length_lt`) for in-scope records.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record

/-! ## Helper Lemmas -/

private theorem serialize_pk_length (pk : PublicKey) : pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

private theorem serialize_pk_ne_nil (pk : PublicKey) : pk.serialize ≠ [] := by
  intro h
  have hlen := serialize_pk_length pk
  rw [h] at hlen
  cases hlen

private theorem identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 :=
  serialize_pk_length ik.publicKey

private theorem keyToBytes32_length (k : BitVec 256) : (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]

private theorem genField_enc_lenField (fl : GenField) :
    (∀ b, fl = .lik b → fl.enc = lenField 2 b) ∧
    (∀ b, fl = .rik b → fl.enc = lenField 3 b) ∧
    (∀ b, fl = .root b → fl.enc = lenField 4 b) ∧
    (∀ c, fl = .sender c → fl.enc = lenField 6 c.enc) ∧
    (∀ c, fl = .recv c → fl.enc = lenField 7 c.enc) ∧
    (∀ k, fl = .pending k → fl.enc = lenField 9 (lenField 2 k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rintro _ rfl; simp [GenField.enc, GenField.tag, GenField.wt, GenField.payload,
      ChainG.payload, lenField, List.append_assoc])

private theorem senderChainG_enc_eq (c : SenderChain) :
    (senderChainG c).enc = encSenderChain c := by
  simp [senderChainG, ChainG.enc, encSenderChain, encChainKey]

private theorem recvChainG_enc_eq (c : ReceiverChain) :
    (recvChainG c).enc = encReceiverChain c := by
  unfold recvChainG ChainG.enc encReceiverChain
  rcases c.chainKey with _ | ck <;>
    simp [bytesField, encChainKey]

private theorem recvChains_flatMap_enc (cs : List ReceiverChain) :
    (cs.map (fun c => GenField.recv (recvChainG c))).flatMap GenField.enc =
      (cs.map (fun c => lenField 7 (encReceiverChain c))).flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.flatMap_cons, List.flatten_cons, ← ih,
      (genField_enc_lenField (.recv (recvChainG c))).2.2.2.2.1 _ rfl, recvChainG_enc_eq]

private theorem encPendingPreKey_of_scope (p : PendingPreKey)
    (hp : p.preKeyId = none ∧ p.signedPreKeyId = 0 ∧ p.timestamp = 0) :
    encPendingPreKey p = lenField 2 p.baseKey.serialize := by
  obtain ⟨h1, h2, h3⟩ := hp
  simp [encPendingPreKey, h1, h2, h3, optUint32Field, int32Field, uint64Field,
    bytesField, serialize_pk_ne_nil p.baseKey]

/-- For an in-scope session, `encSession` equals the concatenation of the encoded `genFields`. -/
theorem encSession_eq_genFields (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    encSession s = (genFields s).flatMap GenField.enc := by
  rcases hr with ⟨⟨_, hPqEmpty, _⟩, s', hs', hSessScope⟩
  rw [hs] at hs'
  injection hs' with hs_eq
  subst hs_eq
  have hpq : s.state.pqRatchetState = [] := hPqEmpty s hs
  obtain ⟨_, hkyber, hlreg, hrreg, halice, hpend⟩ := hSessScope
  unfold encSession genFields
  dsimp only
  simp only [List.flatMap_append, recvChains_flatMap_enc,
    hrreg, hlreg, halice, hkyber, hpq,
    show uint32Field 10 0 = [] from rfl,
    show uint32Field 11 0 = [] from rfl,
    show bytesField 13 [] = [] from rfl,
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
      simp [(genField_enc_lenField _).1 _ rfl]
  have h3 : bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD []) =
      (match s.state.remoteIdentity with
       | some ik => if ik.serialize = [] then [] else [GenField.rik ik.serialize]
       | none => []).flatMap GenField.enc := by
    rcases s.state.remoteIdentity with _ | ik
    · rfl
    · dsimp only [Option.map_some, Option.getD_some]
      unfold bytesField; split_ifs <;>
        simp [(genField_enc_lenField _).2.1 _ rfl]
  have h4 : bytesField 4 (HMAC.keyToBytes32 s.state.rootKey) =
      (if HMAC.keyToBytes32 s.state.rootKey = [] then []
       else [GenField.root (HMAC.keyToBytes32 s.state.rootKey)]).flatMap GenField.enc := by
    unfold bytesField; split_ifs <;>
      simp [(genField_enc_lenField _).2.2.1 _ rfl]
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
    · simp [msgField, (genField_enc_lenField _).2.2.2.1 _ rfl, senderChainG_enc_eq]
  have h9 : msgField 9 (s.pendingPreKey.map encPendingPreKey) =
      (match s.pendingPreKey with
       | some p => [GenField.pending p.baseKey.serialize]
       | none => []).flatMap GenField.enc := by
    rcases hp : s.pendingPreKey with _ | p
    · rfl
    · simp [msgField, (genField_enc_lenField _).2.2.2.2.2 _ rfl,
        encPendingPreKey_of_scope p (hpend p hp)]
  rw [h1, h2, h3, h4, h5, h6, h9]
  rcases s.state.remoteIdentity with _ | ik <;>
    rcases s.state.senderChain with _ | c <;>
    rcases s.pendingPreKey with _ | p <;>
    simp only [List.append_assoc]

/-- For an in-scope record with current session `s`, `encodeRecord r` consists of key `0x0a`, the
varint length of `encSession`, and the concatenated bytes of `recFields r`. -/
theorem encodeRecord_eq_recFields (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r) :
    encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields r).flatMap GenField.enc).length) ++
      (recFields r).flatMap GenField.enc := by
  have ⟨_, s, hs, _⟩ := hr
  have hrec : recFields r = genFields s := by simp [recFields, hs]
  rw [hrec, ← encSession_eq_genFields r hr s hs]
  simp [encodeRecord, hs, msgField, lenField]

/-- Every field in `recFields r` of an in-scope record satisfies `GenField.Ok`. -/
theorem recFields_ok (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r) :
    ∀ fl ∈ recFields r, fl.Ok := by
  obtain ⟨⟨hRecInScope, _, hRecRepr⟩, s, hs, _⟩ := hr
  have hSeeds := (hRecInScope s hs).2.1
  have hMaxKeys := (hRecRepr s hs).1
  simp only [recFields, hs, genFields, List.mem_append, List.mem_map]
  rintro fl (((((((h1 | h2) | h3) | h4) | h5) | h6) | ⟨c, hc, rfl⟩) | h9)
  · split_ifs at h1; · cases h1
    simp only [List.mem_singleton] at h1; subst h1; trivial
  · split_ifs at h2; · cases h2
    simp only [List.mem_singleton] at h2; subst h2
    exact identityKey_serialize_length _
  · rcases hrem : s.state.remoteIdentity with _ | ik <;> rw [hrem] at h3
    · cases h3
    · dsimp only at h3; split_ifs at h3; · cases h3
      simp only [List.mem_singleton] at h3; subst h3
      exact identityKey_serialize_length _
  · split_ifs at h4; · cases h4
    simp only [List.mem_singleton] at h4; subst h4
    exact keyToBytes32_length _
  · split_ifs at h5; · cases h5
    simp only [List.mem_singleton] at h5; subst h5; trivial
  · rcases hsc : s.state.senderChain with _ | c <;> rw [hsc] at h6
    · cases h6
    · simp only [List.mem_singleton] at h6; subst h6
      refine ⟨⟨serialize_pk_length _, Or.inr (List.Vector.toList_length _), ?_, ?_,
        Nat.zero_le _⟩, List.Vector.toList_length _, rfl, rfl⟩
      · rintro ik hik
        simp only [senderChainG, Option.some.injEq] at hik
        subst hik
        exact keyToBytes32_length _
      · rintro m hm; cases hm
  · refine ⟨⟨serialize_pk_length _, Or.inl rfl, ?_, ?_, hMaxKeys c hc⟩, rfl⟩
    · rintro ik hik
      dsimp only [recvChainG] at hik
      rcases hck : c.chainKey with _ | ck <;> rw [hck] at hik
      · cases hik
      · simp only [Option.map_some, Option.some.injEq] at hik
        subst hik
        exact keyToBytes32_length _
    · intro m hm
      exact hSeeds c hc m hm
  · rcases hpp : s.pendingPreKey with _ | p <;> rw [hpp] at h9
    · cases h9
    · simp only [List.mem_singleton] at h9; subst h9
      exact serialize_pk_length _

/-! ## Freshness and Fold Reconstruction -/

private def FreshList (v : SSG) (xs : List GenField) : Prop :=
  ∀ k (hk : k < xs.length), (xs[k]'hk).Fresh ((xs.take k).foldl SSG.apply v)

private theorem freshList_nil (v : SSG) : FreshList v [] := by
  intro k hk; cases hk

private theorem freshList_singleton {v : SSG} {fl : GenField} (h : fl.Fresh v) :
    FreshList v [fl] := by
  intro k hk
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0
  exact h

private theorem freshList_append {v : SSG} {xs ys : List GenField}
    (hxs : FreshList v xs) (hys : FreshList (xs.foldl SSG.apply v) ys) :
    FreshList v (xs ++ ys) := by
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

private theorem foldl_recvChains (ver : BitVec 32) (lik rik root : List (BitVec 8))
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

private theorem freshList_recvChains (ver : BitVec 32) (lik rik root : List (BitVec 8))
    (pc : BitVec 32) (acc : List ChainG) (snd : Option ChainG) (pnd : Option (List (BitVec 8)))
    (cs : List ReceiverChain) (hbound : acc.length + cs.length ≤ maxReceiverChains) :
    FreshList ⟨ver, lik, rik, root, pc, acc, snd, pnd⟩
      (cs.map (fun c => GenField.recv (recvChainG c))) := by
  induction cs generalizing acc with
  | nil => exact freshList_nil _
  | cons c cs ih =>
    rw [List.map_cons, ← List.singleton_append]
    refine freshList_append (freshList_singleton ?_) ?_
    · simp only [GenField.Fresh]
      simp only [List.length_cons] at hbound
      omega
    · dsimp only [List.foldl, SSG.apply]
      apply ih
      simp only [List.length_append, List.length_cons, List.length_nil] at hbound ⊢
      omega

private theorem foldl_step1 (s : Session (List (BitVec 8))) :
    (if s.state.sessionVersion = 0 then [] else [GenField.version s.state.sessionVersion]).foldl
      SSG.apply SSG.empty = ⟨s.state.sessionVersion, [], [], [], 0, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.empty, SSG.apply, h]

private theorem foldl_step2 (s : Session (List (BitVec 8))) (v1 : BitVec 32) :
    (if s.state.localIdentity.serialize = [] then []
     else [GenField.lik s.state.localIdentity.serialize]).foldl
      SSG.apply ⟨v1, [], [], [], 0, [], none, none⟩ =
      ⟨v1, s.state.localIdentity.serialize, [], [], 0, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.apply, h]

private theorem foldl_step3_some (ik : IdentityKey) (v1 : BitVec 32) (v2 : List (BitVec 8)) :
    (if ik.serialize = [] then [] else [GenField.rik ik.serialize]).foldl
      SSG.apply ⟨v1, v2, [], [], 0, [], none, none⟩ =
      ⟨v1, v2, ik.serialize, [], 0, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.apply, h]

private theorem foldl_step4 (s : Session (List (BitVec 8))) (v1 : BitVec 32)
    (v2 v3 : List (BitVec 8)) :
    (if HMAC.keyToBytes32 s.state.rootKey = [] then []
     else [GenField.root (HMAC.keyToBytes32 s.state.rootKey)]).foldl
      SSG.apply ⟨v1, v2, v3, [], 0, [], none, none⟩ =
      ⟨v1, v2, v3, HMAC.keyToBytes32 s.state.rootKey, 0, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.apply, h]

private theorem foldl_step5 (s : Session (List (BitVec 8))) (v1 : BitVec 32)
    (v2 v3 v4 : List (BitVec 8)) :
    (if s.state.previousCounter = 0 then [] else [GenField.prevCounter s.state.previousCounter]).foldl
      SSG.apply ⟨v1, v2, v3, v4, 0, [], none, none⟩ =
      ⟨v1, v2, v3, v4, s.state.previousCounter, [], none, none⟩ := by
  split_ifs with h <;> simp [SSG.apply, h]

/-- Every field `k` in `recFields r` satisfies `GenField.Fresh` against `ssgAfter r k`. -/
theorem recFields_fresh (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r) (k : Nat)
    (hk : k < (recFields r).length) :
    ((recFields r)[k]'hk).Fresh (ssgAfter r k) := by
  obtain ⟨_, s, hs, hSessScope⟩ := hr
  have hmax := hSessScope.1
  revert k hk
  change FreshList SSG.empty (recFields r)
  simp only [recFields, hs, genFields]
  have hscalar : ∀ (v : SSG) (b : List GenField),
      (b = [] ∨ ∃ fl, b = [fl] ∧ fl.Fresh v) → FreshList v b := by
    rintro v b (rfl | ⟨fl, rfl, hfl⟩)
    · exact freshList_nil v
    · exact freshList_singleton hfl
  rcases hrem : s.state.remoteIdentity with _ | ik <;>
    rcases hsc : s.state.senderChain with _ | c <;>
    rcases hpp : s.pendingPreKey with _ | p <;>
    dsimp only
  all_goals
    refine freshList_append ?_ ?_
    · refine freshList_append ?_ ?_
      · refine freshList_append ?_ ?_
        · refine freshList_append ?_ (hscalar _ _ (by split_ifs <;> simp [GenField.Fresh]))
          refine freshList_append ?_ (hscalar _ _ (by split_ifs <;> simp [GenField.Fresh]))
          refine freshList_append ?_ ?_
          · refine freshList_append
              (hscalar _ _ (by split_ifs <;> simp [GenField.Fresh]))
              (hscalar _ _ (by split_ifs <;> simp [GenField.Fresh]))
          · first
            | exact freshList_nil _
            | exact hscalar _ _ (by split_ifs <;> simp [GenField.Fresh])
        · simp only [List.foldl_append, foldl_step1, foldl_step2, foldl_step3_some,
            foldl_step4, foldl_step5, List.foldl_nil]
          first
          | exact freshList_nil _
          | exact freshList_singleton rfl
      · simp only [List.foldl_append, foldl_step1, foldl_step2, foldl_step3_some,
          foldl_step4, foldl_step5, List.foldl_nil, List.foldl_cons, SSG.apply]
        exact freshList_recvChains _ _ _ _ _ [] _ _ _ (by simpa using hmax)
    · simp only [List.foldl_append, foldl_step1, foldl_step2, foldl_step3_some,
        foldl_step4, foldl_step5, List.foldl_nil, List.foldl_cons, SSG.apply, foldl_recvChains]
      first
      | exact freshList_nil _
      | exact freshList_singleton rfl

/-- Folding `SSG.apply` across `recFields r` from `SSG.empty` yields `ssgOf s`. -/
theorem ssgAfter_recFields (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    ssgAfter r (recFields r).length = ssgOf s := by
  have _ := hr
  unfold ssgAfter
  rw [List.take_length]
  simp only [recFields, hs, genFields]
  rcases hrem : s.state.remoteIdentity with _ | ik <;>
    rcases hsc : s.state.senderChain with _ | c <;>
    rcases hpp : s.pendingPreKey with _ | p <;>
    simp only [ssgOf, hrem, hsc, hpp, List.foldl_append, foldl_step1, foldl_step2,
      foldl_step3_some, foldl_step4, foldl_step5, List.foldl_nil, List.foldl_cons,
      SSG.apply, foldl_recvChains, List.nil_append, Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some]

/-- `c.enc` equals the concatenation of `(c.fields.map ChainField.enc)`. -/
theorem chainG_enc_eq_fields (c : ChainG) : c.enc = c.fields.flatMap ChainField.enc := by
  unfold ChainG.enc ChainG.fields
  simp only [List.flatMap_append, List.flatMap_map]
  congr 1
  congr 1
  · congr 1
    · unfold bytesField; split_ifs <;> simp [ChainField.enc]
    · unfold bytesField; split_ifs <;> simp [ChainField.enc]
  · rcases c.ck with _ | ⟨i, k⟩ <;> simp [msgField, ChainField.enc]

private theorem foldl_chainG_keys (srk priv : List (BitVec 8))
    (ck : Option (BitVec 32 × List (BitVec 8))) (acc ks : List MessageKeyGenerator) :
    (ks.map ChainField.key).foldl ChainG.apply ⟨srk, priv, ck, acc⟩ =
      ⟨srk, priv, ck, acc ++ ks⟩ := by
  induction ks generalizing acc with
  | nil => simp
  | cons m ks ih =>
    simp only [List.map_cons, List.foldl_cons, ChainG.apply, ih, List.append_assoc,
      List.singleton_append]

/-- Folding `ChainG.apply` across `c.fields` from `ChainG.empty` reconstructs `c`. -/
theorem chainGAfter_fields (c : ChainG) : chainGAfter c c.fields.length = c := by
  unfold chainGAfter
  rw [List.take_length]
  unfold ChainG.fields
  simp only [List.foldl_append]
  have h1 : (if c.srk = [] then [] else [ChainField.srk c.srk]).foldl
      ChainG.apply ChainG.empty = ⟨c.srk, [], none, []⟩ := by
    split_ifs with h <;> simp [ChainG.empty, ChainG.apply, h]
  rw [h1]
  have h2 : (if c.priv = [] then [] else [ChainField.priv c.priv]).foldl
      ChainG.apply ⟨c.srk, [], none, []⟩ = ⟨c.srk, c.priv, none, []⟩ := by
    split_ifs with h <;> simp [ChainG.apply, h]
  rw [h2]
  rcases hck : c.ck with _ | ⟨i, k⟩
  · dsimp only [List.foldl]
    rw [foldl_chainG_keys, List.nil_append]
    cases c
    dsimp only at hck ⊢
    subst hck
    rfl
  · dsimp only [List.foldl, ChainG.apply]
    rw [foldl_chainG_keys, List.nil_append]
    cases c
    dsimp only at hck ⊢
    subst hck
    rfl

/-! ## Record Encoding Length Bound -/

private theorem encodeVarintAux_length_le (n : Nat) (v : BitVec 64) :
    (encodeVarintAux n v).length ≤ n := by
  induction n generalizing v with
  | zero => simp [encodeVarintAux]
  | succ n ih =>
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have := ih (v >>> 7)
      omega

private theorem encodeVarint_length_le_10 (v : BitVec 64) :
    (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v

private theorem encodeKey_length_le_10 (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le_10 _

private theorem lenField_length_le (tag : Nat) (b : List (BitVec 8)) :
    (lenField tag b).length ≤ b.length + 20 := by
  unfold lenField
  have h1 := encodeKey_length_le_10 tag .lengthDelimited
  have h2 := encodeVarint_length_le_10 (BitVec.ofNat 64 b.length)
  simp only [List.length_append]
  omega

private theorem bytesField_length_le (tag : Nat) (b : List (BitVec 8)) :
    (bytesField tag b).length ≤ b.length + 20 := by
  unfold bytesField
  split_ifs
  · simp
  · exact lenField_length_le tag b

private theorem uint32Field_length_le (tag : Nat) (v : BitVec 32) :
    (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 (v.setWidth 64)
    simp only [List.length_append]
    omega

private theorem uint64Field_length_le (tag : Nat) (v : BitVec 64) :
    (uint64Field tag v).length ≤ 20 := by
  unfold uint64Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 v
    simp only [List.length_append]
    omega

private theorem int32Field_length_le (tag : Nat) (v : BitVec 32) :
    (int32Field tag v).length ≤ 20 := by
  unfold int32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 (v.signExtend 64)
    simp only [List.length_append]
    omega

private theorem optUint32Field_length_le (tag : Nat) (ov : Option (BitVec 32)) :
    (optUint32Field tag ov).length ≤ 20 := by
  rcases ov with _ | v
  · simp [optUint32Field]
  · unfold optUint32Field
    have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 (v.setWidth 64)
    simp only [List.length_append]
    omega

private theorem encChainKey_length_le (ck : ChainKey) :
    (encChainKey ck).length ≤ 72 := by
  unfold encChainKey
  have h1 := uint32Field_length_le 1 ck.index
  have h2 := bytesField_length_le 2 (HMAC.keyToBytes32 ck.key)
  rw [keyToBytes32_length] at h2
  simp only [List.length_append]
  omega

private theorem lenField_encMessageKey_length_le (mk : MessageKeyGenerator)
    (hseed : mk.seed.length = 32) :
    (lenField 4 (encMessageKey mk)).length ≤ 92 := by
  have h0 := lenField_length_le 4 (encMessageKey mk)
  have heq : (encMessageKey mk).length =
      (uint32Field 1 mk.counter).length + (bytesField 5 mk.seed).length := by
    simp [encMessageKey]
  have h1 := uint32Field_length_le 1 mk.counter
  have h2 := bytesField_length_le 5 mk.seed
  rw [hseed] at h2
  omega

private theorem flatten_encMessageKeys_length_le (mks : List MessageKeyGenerator)
    (hseeds : ∀ mk ∈ mks, mk.seed.length = 32) :
    ((mks.map fun mk => lenField 4 (encMessageKey mk)).flatten).length ≤ 92 * mks.length := by
  induction mks with
  | nil => simp
  | cons mk mks ih =>
    have hmk := lenField_encMessageKey_length_le mk (hseeds mk (by simp))
    have hmks := ih (fun m hm => hseeds m (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

private theorem lenField_encReceiverChain_length_le (c : ReceiverChain)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32)
    (hmax : c.messageKeys.length ≤ maxMessageKeys) :
    (lenField 7 (encReceiverChain c)).length ≤ 184165 := by
  have h0 := lenField_length_le 7 (encReceiverChain c)
  have heq : (encReceiverChain c).length =
      (bytesField 1 c.senderRatchetKey.serialize).length +
      (msgField 3 (c.chainKey.map encChainKey)).length +
      ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length := by
    simp only [encReceiverChain, List.length_append]
  have h1 := bytesField_length_le 1 c.senderRatchetKey.serialize
  rw [serialize_pk_length] at h1
  have h2 : (msgField 3 (c.chainKey.map encChainKey)).length ≤ 92 := by
    rcases c.chainKey with _ | ck
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have hck := encChainKey_length_le ck
      have hlf := lenField_length_le 3 (encChainKey ck)
      omega
  have h3 := flatten_encMessageKeys_length_le c.messageKeys hseeds
  have hmax_val : maxMessageKeys = 2000 := rfl
  omega

private theorem flatten_encReceiverChains_length_le (cs : List ReceiverChain)
    (hseeds : ∀ c ∈ cs, ∀ mk ∈ c.messageKeys, mk.seed.length = 32)
    (hmax : ∀ c ∈ cs, c.messageKeys.length ≤ maxMessageKeys) :
    ((cs.map fun c => lenField 7 (encReceiverChain c)).flatten).length ≤ 184165 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := lenField_encReceiverChain_length_le c (hseeds c (by simp)) (hmax c (by simp))
    have hcs := ih (fun c' hc' => hseeds c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hmax c' (List.mem_cons_of_mem _ hc'))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- Every record `r` in `DeserializeScope` encodes to strictly fewer than `2 ^ 20` bytes. -/
theorem encodeRecord_length_lt {r : SessionRecord (List (BitVec 8))} (h : DeserializeScope r) :
    (encodeRecord r).length < 2 ^ 20 := by
  obtain ⟨⟨hRecInScope, hPqEmpty, hRecRepr⟩, s, hs, hSessScope⟩ := h
  have hSeeds := (hRecInScope s hs).2.1
  have hMaxKeys := (hRecRepr s hs).1
  have hMaxChains := hSessScope.1
  have hMaxChains_val : maxReceiverChains = 5 := rfl
  have hrec := lenField_length_le 1 (encSession s)
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
  have h1 := uint32Field_length_le 1 s.state.sessionVersion
  have h2 := bytesField_length_le 2 s.state.localIdentity.serialize
  rw [identityKey_serialize_length] at h2
  have h3 : (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤ 53 := by
    rcases s.state.remoteIdentity with _ | ik
    · simp [bytesField]
    · dsimp only [Option.map_some, Option.getD_some]
      have := bytesField_length_le 3 ik.serialize
      rw [identityKey_serialize_length] at this
      exact this
  have h4 := bytesField_length_le 4 (HMAC.keyToBytes32 s.state.rootKey)
  rw [keyToBytes32_length] at h4
  have h5 := uint32Field_length_le 5 s.state.previousCounter
  have h6 : (msgField 6 (s.state.senderChain.map encSenderChain)).length ≤ 217 := by
    rcases s.state.senderChain with _ | sc
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have h0 := lenField_length_le 6 (encSenderChain sc)
      have heq : (encSenderChain sc).length =
          (bytesField 1 sc.ratchetKey.publicKey.serialize).length +
          (bytesField 2 sc.ratchetKey.privateKey.bytes.toList).length +
          (lenField 3 (encChainKey sc.chainKey)).length := by
        simp only [encSenderChain, msgField, List.length_append]
      have ha := bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
      rw [serialize_pk_length] at ha
      have hb := bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
      rw [List.Vector.toList_length] at hb
      have hc := lenField_length_le 3 (encChainKey sc.chainKey)
      have hd := encChainKey_length_le sc.chainKey
      omega
  have h7 := flatten_encReceiverChains_length_le s.state.receiverChains hSeeds hMaxKeys
  have h9 : (msgField 9 (s.pendingPreKey.map encPendingPreKey)).length ≤ 133 := by
    rcases s.pendingPreKey with _ | p
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have h0 := lenField_length_le 9 (encPendingPreKey p)
      have heq : (encPendingPreKey p).length =
          (optUint32Field 1 p.preKeyId).length +
          (bytesField 2 p.baseKey.serialize).length +
          (int32Field 3 p.signedPreKeyId).length +
          (uint64Field 4 p.timestamp).length := by
        simp only [encPendingPreKey, List.length_append]
      have ha := optUint32Field_length_le 1 p.preKeyId
      have hb := bytesField_length_le 2 p.baseKey.serialize
      rw [serialize_pk_length] at hb
      have hc := int32Field_length_le 3 p.signedPreKeyId
      have hd := uint64Field_length_le 4 p.timestamp
      omega
  have h10 := uint32Field_length_le 10 s.remoteRegistrationId
  have h11 := uint32Field_length_le 11 s.localRegistrationId
  have h13 : (bytesField 13 s.aliceBaseKey).length = 0 := by
    rw [hSessScope.2.2.2.2.1]; rfl
  have h14 : (msgField 14 (s.pendingKyberPreKey.map encPendingKyber)).length = 0 := by
    rw [hSessScope.2.1]; rfl
  have h15 : (bytesField 15 s.state.pqRatchetState).length = 0 := by
    rw [hPqEmpty s hs]; rfl
  omega

end CryptoVerification.E2E.Record.DeserializeGeneral

