/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.L1GX.Fields
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push

/-!
# Representation conversion from `prostSSGXAt` to `sessionStateReprAt`

Proves `prostSSGX_repr` and `deserReprX_ok`: the decoded PQXDH-scope `SessionStructure`
(`prostSSGXAt A0 a (ssgxOf s)`) entails `sessionStateReprAt` with canonical ghost witnesses,
and `deserOutRecordX out r` entails `sessionRecordAt` with `CanonRecord`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.ProstSSGXRepr

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonCur CanonSession CanonChain CanonSender
  CanonPending)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoGames.HMAC

set_option linter.unusedSimpArgs false

private theorem deserialize_serialize_pk_ssg (pk : PublicKey) :
    PublicKey.deserialize pk.serialize = .ok pk := by
  unfold PublicKey.serialize PublicKey.deserialize
  rcases pk with ⟨⟨bs, hbs⟩⟩
  simp [hbs]
  congr 1
  exact Subtype.ext (List.take_of_length_le (Nat.le_of_eq hbs))

private theorem serialize_pk_length_ssg (pk : PublicKey) :
    pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

private theorem serialize_ik_length_ssg (ik : IdentityKey) :
    ik.serialize.length = 33 :=
  serialize_pk_length_ssg ik.publicKey

private theorem arrayAt_map_entails_zip {α β γ : Type}
    (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (stride : Nat) :
    ∀ (xs : List α) (base : BitVec 64),
      (∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) →
      arrayAt elem1 stride base (xs.map f) ⊢
        ∃∗ gs : List γ,
          ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
            arrayAt elem2 stride base (gs.zip xs)
  | [], base, _ => by
    dsimp only [List.map, arrayAt]
    refine Entails.sepExists_right [] ?_
    have hall : ∀ gx ∈ ([] : List γ).zip ([] : List α), P gx := by
      intro _ h; cases h
    exact Entails.pure_right ⟨rfl, hall⟩ (Entails.refl _)
  | x :: xs, base, h => by
    dsimp only [List.map, arrayAt]
    have hx := h x List.mem_cons_self base
    have hxs := arrayAt_map_entails_zip elem1 elem2 P f stride xs
      (base + BitVec.ofNat 64 stride) (fun y hy b => h y (List.mem_cons_of_mem x hy) b)
    refine Entails.trans (sepConj_mono hx hxs) ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro gs
    apply Entails.sepExists_elim; intro g
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hpx
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hpz⟩
    refine Entails.sepExists_right (g :: gs) ?_
    have hlen' : (g :: gs).length = (x :: xs).length := by simp [hlen]
    have hpz' : ∀ gx ∈ (g :: gs).zip (x :: xs), P gx := by
      intro gx hgx
      simp only [List.zip_cons_cons, List.mem_cons] at hgx
      rcases hgx with rfl | hgx
      · exact hpx
      · exact hpz gx hgx
    refine Entails.pure_right ⟨hlen', hpz'⟩ ?_
    dsimp only [List.zip_cons_cons, arrayAt]
    exact Entails.refl _

private theorem vecAt_map_entails_zip {α β γ : Type} (A : RustAlloc)
    (stride align : Nat) (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (v cap ptr : BitVec 64) (xs : List α)
    (h : ∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) :
    vecAt A stride align elem1 v cap ptr (xs.map f) ⊢
      ∃∗ gs : List γ,
        ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
          vecAt A stride align elem2 v cap ptr (gs.zip xs) := by
  unfold vecAt vecBuf
  rw [List.length_map]
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbuf
  by_cases hcap : cap = 0
  · subst hcap
    have hxs0 : xs.length = 0 := Nat.eq_zero_of_le_zero hbuf.1
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero hxs0
    subst hnil
    refine Entails.sepExists_right [] ?_
    have hall : ∀ gx ∈ ([] : List γ).zip ([] : List α), P gx := by intro _ h; cases h
    refine Entails.pure_right ⟨rfl, hall⟩ ?_
    rw [sepConj_pure_left_comm]
    exact Entails.pure_right hbuf (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    have harr := arrayAt_map_entails_zip elem1 elem2 P f stride xs ptr h
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left harr))) ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro gs
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hpz⟩
    refine Entails.sepExists_right gs ?_
    refine Entails.pure_right ⟨hlen, hpz⟩ ?_
    have hzip_len : (gs.zip xs).length = xs.length := by
      rw [List.length_zip, hlen, Nat.min_self]
    rw [hzip_len]
    rw [sepConj_pure_left_comm]
    exact Entails.pure_right hbuf (Entails.refl _)

private theorem vecOf_map_entails_vecAt_zip {α β γ : Type} (A : RustAlloc)
    (stride align : Nat) (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (v : BitVec 64) (xs : List α)
    (h : ∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) :
    vecOf A stride align elem1 v (xs.map f) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ gs : List γ,
        ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
          vecAt A stride align elem2 v cap ptr (gs.zip xs) := by
  unfold vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap ?_
  refine Entails.sepExists_right ptr ?_
  exact vecAt_map_entails_zip A stride align elem1 elem2 P f v cap ptr xs h

private theorem prostMsgKeyAt_entails_messageKeyAt (mk : MessageKeyGenerator)
    (hseed : mk.seed.length = 32) (a : BitVec 64) :
    prostMsgKeyAt A0 mk a ⊢
      ∃∗ mg : MessageKeyGhost, ⌜True⌝ ∗ messageKeyAt A0 (mg, mk) a := by
  have hne : mk.seed ≠ [] := by
    intro h; rw [h] at hseed; cases hseed
  unfold prostMsgKeyAt vecU8
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro seedCap
  apply Entails.sepExists_elim; intro seedPtr
  apply Entails.sepExists_elim; intro ivCap
  apply Entails.sepExists_elim; intro ivPtr
  apply Entails.sepExists_elim; intro macCap
  apply Entails.sepExists_elim; intro macPtr
  apply Entails.sepExists_elim; intro cipherCap
  apply Entails.sepExists_elim; intro cipherPtr
  let mg : MessageKeyGhost := {
    cipher := ⟨cipherCap, cipherPtr⟩
    mac := ⟨macCap, macPtr⟩
    iv := ⟨ivCap, ivPtr⟩
    seed := ⟨seedCap, seedPtr⟩
  }
  refine Entails.sepExists_right mg ?_
  refine Entails.pure_right trivial ?_
  unfold messageKeyAt
  exact Entails.pure_right hne (Entails.refl _)

private theorem prostChainKey_entails_optChainKeyAt (o : Option ChainKey) (a : BitVec 64) :
    (match o.map (fun ck => (ck.index, HMAC.keyToBytes32 ck.key)) with
     | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
     | some (i, k) => vecU8 A0 (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
         memRegion (a + 0x64#64) 4) ⊢
      ∃∗ ckPin : VecPin, optChainKeyAt A0 ckPin o (a + 72#64) := by
  rcases o with _ | ck
  · dsimp only [Option.map, optChainKeyAt]
    refine Entails.sepExists_right ⟨0, 0⟩ ?_
    have ha : a + 72#64 + 8#64 = a + 0x50#64 := by rw [BitVec.add_assoc]; rfl
    rw [ha]
    exact Entails.refl _
  · dsimp only [Option.map, optChainKeyAt]
    unfold vecU8
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
    have ha1 : a + 72#64 + 24#64 = a + 0x60#64 := by rw [BitVec.add_assoc]; rfl
    have ha2 : a + 72#64 + 28#64 = a + 0x64#64 := by rw [BitVec.add_assoc]; rfl
    rw [ha1, ha2]
    exact Entails.refl _

private theorem prostChainGAt_recv_entails_chainAt (c : ReceiverChain)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32)
    (hmax : c.messageKeys.length ≤ maxMessageKeys) (a : BitVec 64) :
    prostChainGAt A0 a (recvChainG c) ⊢
      ∃∗ cg : ChainGhost,
        ⌜CanonChain (cg, c)⌝ ∗ chainAt A0 (cg, c) a := by
  unfold prostChainGAt recvChainG
  dsimp only
  have hkeys :
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c.messageKeys ⊢
        ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64, ∃∗ keys : List MessageKeyGhost,
          ⌜keys.length = c.messageKeys.length ∧
            (∀ gx ∈ keys.zip c.messageKeys, True)⌝ ∗
            vecAt A0 104 8 (messageKeyAt A0) (a + 0x30#64) mkCap mkPtr
              (keys.zip c.messageKeys) := by
    conv_lhs => rw [show c.messageKeys = c.messageKeys.map id by simp]
    exact vecOf_map_entails_vecAt_zip A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b)
      (messageKeyAt A0) (fun _ => True) id (a + 0x30#64) c.messageKeys
      (fun mk hmk b => prostMsgKeyAt_entails_messageKeyAt mk (hseeds mk hmk) b)
  have hck := prostChainKey_entails_optChainKeyAt c.chainKey a
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hkeys hck))) ?_
  unfold vecU8
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ckPin
  apply Entails.sepExists_elim; intro mkCap
  apply Entails.sepExists_elim; intro mkPtr
  apply Entails.sepExists_elim; intro keys
  apply Entails.sepExists_elim; intro privCap
  apply Entails.sepExists_elim; intro privPtr
  apply Entails.sepExists_elim; intro srkCap
  apply Entails.sepExists_elim; intro srkPtr
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hkeyslen, -⟩
  let cg : ChainGhost := {
    srk := ⟨srkCap, srkPtr, c.senderRatchetKey.serialize⟩
    priv := ⟨privCap, privPtr, []⟩
    mkCap := mkCap
    mkPtr := mkPtr
    keys := keys
    ck := ckPin
  }
  refine Entails.sepExists_right cg ?_
  have hcanon : CanonChain (cg, c) := ⟨rfl, rfl⟩
  refine Entails.pure_right hcanon ?_
  unfold chainAt
  refine Entails.pure_right
    ⟨deserialize_serialize_pk_ssg c.senderRatchetKey, hmax, hkeyslen,
      serialize_pk_length_ssg c.senderRatchetKey, rfl⟩ ?_
  dsimp only [cg, vecGhostAt]
  exact Entails.refl _

private theorem prostRecvG_entails_vecAt_chainAt (s : Session (List (BitVec 8)))
    (hseeds : SeedsLen32 s.state)
    (hmax : ∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (a : BitVec 64) :
    vecOf A0 104 8 (fun c p => prostChainGAt A0 p c) a (s.state.receiverChains.map recvChainG) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ chains : List ChainGhost,
        ⌜chains.length = s.state.receiverChains.length ∧
          (∀ gc ∈ chains.zip s.state.receiverChains, CanonChain gc)⌝ ∗
          vecAt A0 104 8 (chainAt A0) a cap ptr (chains.zip s.state.receiverChains) := by
  exact vecOf_map_entails_vecAt_zip A0 104 8 (fun c p => prostChainGAt A0 p c)
    (chainAt A0) CanonChain recvChainG a s.state.receiverChains
    (fun c hc b => prostChainGAt_recv_entails_chainAt c (hseeds c hc) (hmax c hc) b)

private theorem vecAt_nil_prostMsgKeyAt_eq_messageKeyAt (A : RustAlloc) (v cap ptr : BitVec 64) :
    vecAt A 104 8 (fun mk b => prostMsgKeyAt A mk b) v cap ptr [] =
      vecAt A 104 8 (messageKeyAt A) v cap ptr [] := by
  unfold vecAt vecBuf arrayAt
  rfl

private theorem prostSenderG_entails_optSenderChainAt (scOpt : Option SenderChain)
    (hclamp : ∀ sc, scOpt = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (ss : BitVec 64) :
    (match scOpt.map senderChainG with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A0 (ss + 0x90#64) c) ⊢
      ∃∗ sg : Option SenderChainGhost,
        ⌜CanonSender sg scOpt⌝ ∗
          optSenderChainAt A0 (ss + 0x90#64) sg scOpt := by
  rcases scOpt with _ | sc
  · dsimp only [Option.map]
    refine Entails.sepExists_right none ?_
    refine Entails.pure_right trivial ?_
    unfold optSenderChainAt
    rw [show ss + 0x90#64 + 8#64 = ss + 0x98#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map]
    unfold prostChainGAt senderChainG vecU8 vecOf
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ckCap
    apply Entails.sepExists_elim; intro ckPtr
    apply Entails.sepExists_elim; intro mkCap
    apply Entails.sepExists_elim; intro mkPtr
    apply Entails.sepExists_elim; intro privCap
    apply Entails.sepExists_elim; intro privPtr
    apply Entails.sepExists_elim; intro srkCap
    apply Entails.sepExists_elim; intro srkPtr
    let g : SenderChainGhost := {
      srk := ⟨srkCap, srkPtr, sc.ratchetKey.publicKey.serialize⟩
      priv := ⟨privCap, privPtr, sc.ratchetKey.privateKey.bytes.toList⟩
      mkCap := mkCap
      mkPtr := mkPtr
      ck := ⟨ckCap, ckPtr⟩
    }
    refine Entails.sepExists_right (some g) ?_
    have hcanon : CanonSender (some g) (some sc) := ⟨rfl, rfl⟩
    refine Entails.pure_right hcanon ?_
    unfold optSenderChainAt
    refine Entails.pure_right
      ⟨deserialize_serialize_pk_ssg _, rfl, hclamp sc rfl, serialize_pk_length_ssg _⟩ ?_
    dsimp only [g, vecGhostAt, optChainKeyAt]
    rw [vecAt_nil_prostMsgKeyAt_eq_messageKeyAt,
      show ss + 0x90#64 + 72#64 + 24#64 = ss + 0x90#64 + 0x60#64 by rw [BitVec.add_assoc]; rfl,
      show ss + 0x90#64 + 72#64 + 28#64 = ss + 0x90#64 + 0x64#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _

/-! ## Pending pre-key representation (`pre_key_id` and `signed_pre_key_id`) -/

private def pendingTailX (w0 w1 spkId w2 : BitVec 32) : List (BitVec 8) :=
  unpack32 w0 ++ (unpack32 w1 ++ (unpack64 0#64 ++ (unpack32 spkId ++ unpack32 w2)))

private theorem pendingTailX_length (w0 w1 spkId w2 : BitVec 32) :
    (pendingTailX w0 w1 spkId w2).length = 24 := rfl

private theorem pendingTailX_pointsToBytes (ss : BitVec 64) (w0 w1 spkId w2 : BitVec 32) :
    ((ss + 0x110#64) ↦₃₂ w0) ∗ ((ss + 0x114#64) ↦₃₂ w1) ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ spkId) ∗ ((ss + 0x124#64) ↦₃₂ w2) =
      ((ss + 0xf8#64 + 24#64) ↦ₛ pendingTailX w0 w1 spkId w2) := by
  have ha0 : ss + 0xf8#64 + 24#64 = ss + 0x110#64 := by rw [BitVec.add_assoc]; rfl
  have ha1 : ss + 0x110#64 + 4#64 = ss + 0x114#64 := by rw [BitVec.add_assoc]; rfl
  have ha2 : ss + 0x114#64 + 4#64 = ss + 0x118#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : ss + 0x118#64 + 8#64 = ss + 0x120#64 := by rw [BitVec.add_assoc]; rfl
  have ha4 : ss + 0x120#64 + 4#64 = ss + 0x124#64 := by rw [BitVec.add_assoc]; rfl
  unfold pendingTailX
  rw [ha0, pointsToBytes_append, unpack32_length,
    ha1, pointsToBytes_append, unpack32_length,
    ha2, pointsToBytes_append, unpack64_length,
    ha3, pointsToBytes_append, unpack32_length, ha4]
  simp only [← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

private theorem prostPendingX_entails_optTailVecAt (s : Session (List (BitVec 8)))
    (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p → p.timestamp = 0)
    (ss : BitVec 64) (pid : Option (BitVec 32)) (spkId : BitVec 32)
    (hpid : ∀ p, s.pendingPreKey = some p → pid = p.preKeyId ∧ spkId = p.signedPreKeyId) :
    (match s.pendingPreKey.map (fun p => p.baseKey.serialize) with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A0 (ss + 0xf8#64) k ∗
         pidAt ss pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4)) ⊢
      ∃∗ pg : Option TailVecGhost,
        ⌜CanonPending pg s.pendingPreKey ∧
          PendingRel pg s.pendingPreKey ∧
          pg.isSome = s.state.pendingPreKey⌝ ∗
          optTailVecAt A0 48 (ss + 0xf8#64) pg := by
  unfold Session.Wf at hwf
  rcases hpend : s.pendingPreKey with _ | p
  · dsimp only [Option.map]
    refine Entails.sepExists_right none ?_
    have hsome : (none : Option TailVecGhost).isSome = s.state.pendingPreKey := by
      rw [hwf, hpend]; rfl
    refine Entails.pure_right ⟨trivial, trivial, hsome⟩ ?_
    unfold optTailVecAt
    rw [show ss + 0xf8#64 + 8#64 = ss + 0x100#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map]
    have hts := hp p hpend
    obtain ⟨hpid', hspk'⟩ := hpid p hpend
    have hsome : (some (⟨⟨0, 0, []⟩, []⟩ : TailVecGhost)).isSome = s.state.pendingPreKey := by
      rw [hwf, hpend]; rfl
    subst hspk'
    rcases hpre : p.preKeyId with _ | i <;> rw [hpre] at hpid' <;> subst hpid'
    · -- `pre_key_id = None`
      unfold pidAt vecU8
      rw [memRegion_four (ss + 0x114#64), memRegion_four (ss + 0x124#64)]
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w1 =>
        Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
      let g : TailVecGhost := {
        vec := ⟨cap, ptr, p.baseKey.serialize⟩
        tail := pendingTailX 0#32 w1 p.signedPreKeyId w2
      }
      refine Entails.sepExists_right (some g) ?_
      have hcanon : CanonPending (some g) (some p) := rfl
      have hrel : PendingRel (some g) (some p) := by
        refine ⟨deserialize_serialize_pk_ssg p.baseKey, ?_, ?_, ?_, serialize_pk_length_ssg p.baseKey⟩
        · rw [hpre]; rfl
        · rw [hts]; rfl
        · simp only [g, pendingTailX, leBytes, unpack32, unpack64, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
      refine Entails.pure_right ⟨hcanon, hrel, hsome⟩ ?_
      unfold optTailVecAt
      refine Entails.pure_right (pendingTailX_length 0#32 w1 p.signedPreKeyId w2) ?_
      dsimp only [g, vecGhostAt]
      rw [← pendingTailX_pointsToBytes ss 0#32 w1 p.signedPreKeyId w2]
      exact Entails.refl _
    · -- `pre_key_id = Some i`
      unfold pidAt vecU8
      rw [memRegion_four (ss + 0x124#64)]
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine Entails.sepExists_elim fun w2 =>
        Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
      let g : TailVecGhost := {
        vec := ⟨cap, ptr, p.baseKey.serialize⟩
        tail := pendingTailX 1#32 i p.signedPreKeyId w2
      }
      refine Entails.sepExists_right (some g) ?_
      have hcanon : CanonPending (some g) (some p) := rfl
      have hrel : PendingRel (some g) (some p) := by
        refine ⟨deserialize_serialize_pk_ssg p.baseKey, ?_, ?_, ?_, serialize_pk_length_ssg p.baseKey⟩
        · rw [hpre]; exact ⟨rfl, by simp only [g, pendingTailX, leBytes, unpack32, unpack64, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl⟩
        · rw [hts]; rfl
        · simp only [g, pendingTailX, leBytes, unpack32, unpack64, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
      refine Entails.pure_right ⟨hcanon, hrel, hsome⟩ ?_
      unfold optTailVecAt
      refine Entails.pure_right (pendingTailX_length 1#32 i p.signedPreKeyId w2) ?_
      dsimp only [g, vecGhostAt]
      rw [← pendingTailX_pointsToBytes ss 1#32 i p.signedPreKeyId w2]
      exact Entails.refl _

/-! ## Pending Kyber pre-key representation -/

private theorem kyberAt_split (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (R : SepProp) :
    kyberAt A ss kyber R =
      (match kyber with
       | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24
       | some (i, ct) => vecU8 A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
           memRegion (ss + 0x144#64) 4) ∗ R := by
  rcases kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt, sepConj_assoc]

private def kyberTailX (i w : BitVec 32) : List (BitVec 8) := unpack32 i ++ unpack32 w

private theorem kyberTailX_pointsToBytes (ss : BitVec 64) (i w : BitVec 32) :
    ((ss + 0x140#64) ↦₃₂ i) ∗ ((ss + 0x144#64) ↦₃₂ w) =
      ((ss + 0x128#64 + 24#64) ↦ₛ kyberTailX i w) := by
  have ha0 : ss + 0x128#64 + 24#64 = ss + 0x140#64 := by rw [BitVec.add_assoc]; rfl
  have ha1 : ss + 0x140#64 + 4#64 = ss + 0x144#64 := by rw [BitVec.add_assoc]; rfl
  unfold kyberTailX
  rw [ha0, pointsToBytes_append, unpack32_length, ha1]
  simp only [← pointsTo32_eq_pointsToBytes]

private theorem prostKyberX_entails_optTailVecAt (o : Option PendingKyberPreKey)
    (ss : BitVec 64) :
    (match o.map (fun k => (k.preKeyId, k.ciphertext)) with
     | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24
     | some (i, ct) => vecU8 A0 (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
         memRegion (ss + 0x144#64) 4) ⊢
      ∃∗ kg : Option TailVecGhost, ⌜KyberRel kg o⌝ ∗ optTailVecAt A0 32 (ss + 0x128#64) kg := by
  rcases ho : o with _ | k
  · dsimp only [Option.map]
    refine Entails.sepExists_right none ?_
    refine Entails.pure_right trivial ?_
    unfold optTailVecAt
    rw [show ss + 0x128#64 + 8#64 = ss + 0x130#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map]
    unfold vecU8
    rw [memRegion_four (ss + 0x144#64)]
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun w =>
      Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    let g : TailVecGhost := {
      vec := ⟨cap, ptr, k.ciphertext⟩
      tail := kyberTailX k.preKeyId w
    }
    refine Entails.sepExists_right (some g) ?_
    have hrel : KyberRel (some g) (some k) := by
      refine ⟨rfl, ?_⟩
      dsimp only [g, kyberTailX]
      simp only [g, pendingTailX, kyberTailX, leBytes, unpack32, unpack64, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
    refine Entails.pure_right hrel ?_
    unfold optTailVecAt
    refine Entails.pure_right (rfl : (kyberTailX k.preKeyId w).length = 8) ?_
    dsimp only [g, vecGhostAt]
    rw [← kyberTailX_pointsToBytes ss k.preKeyId w]
    exact Entails.refl _

/-- Converts the decoded `prostSSGXAt A0 a (ssgxOf s)` of a `DeserializeScopeP` session into `sessionStateReprAt` with canonical ghost state. -/
theorem prostSSGX_repr (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) (a : BitVec 64) :
    prostSSGXAt A0 a (ssgxOf s) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G s⌝ ∗ sessionStateReprAt A0 a G s := by
  obtain ⟨⟨hr_in, _, hr_repr⟩, s', hs', hscope⟩ := hr
  have hss' : s = s' := Option.some.inj (hs.symm.trans hs')
  subst hss'
  obtain ⟨hseeds, -, -⟩ := hr_in s hs
  obtain ⟨hmax_mk, hclamp, hwf, -⟩ := hr_repr s hs
  obtain ⟨-, hpend_fields, -⟩ := hscope
  unfold prostSSGXAt ssgxOf ssgOf
  dsimp only
  rw [kyberAt_split]
  have hrecv := prostRecvG_entails_vecAt_chainAt s hseeds hmax_mk (a + 0x48#64)
  have hsender := prostSenderG_entails_optSenderChainAt s.state.senderChain hclamp a
  have hpending := prostPendingX_entails_optTailVecAt s hwf hpend_fields a
    (s.pendingPreKey.bind (·.preKeyId))
    ((s.pendingPreKey.map (·.signedPreKeyId)).getD 0#32)
    (fun p hp => by rw [hp]; exact ⟨rfl, rfl⟩)
  have hky := prostKyberX_entails_optTailVecAt s.pendingKyberPreKey a
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left hrecv)))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro chainsCap
  apply Entails.sepExists_elim; intro chainsPtr
  apply Entails.sepExists_elim; intro chains
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hchains_len, hchains_canon⟩
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hsender))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro sg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hsender_canon
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hpending)))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hpending_canon, hpending_rel, hpending_some⟩
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hky))))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro kg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hkyber_rel
  unfold vecU8
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pqCap
  apply Entails.sepExists_elim; intro pqPtr
  apply Entails.sepExists_elim; intro aliceCap
  apply Entails.sepExists_elim; intro alicePtr
  apply Entails.sepExists_elim; intro rootCap
  apply Entails.sepExists_elim; intro rootPtr
  apply Entails.sepExists_elim; intro rikCap
  apply Entails.sepExists_elim; intro rikPtr
  apply Entails.sepExists_elim; intro likCap
  apply Entails.sepExists_elim; intro likPtr
  let G : SessionGhost := {
    localIk := ⟨likCap, likPtr, s.state.localIdentity.serialize⟩
    remoteIk := ⟨rikCap, rikPtr, (s.state.remoteIdentity.map IdentityKey.serialize).getD []⟩
    root := ⟨rootCap, rootPtr⟩
    chainsCap := chainsCap
    chainsPtr := chainsPtr
    chains := chains
    alice := ⟨aliceCap, alicePtr, s.aliceBaseKey⟩
    pq := ⟨pqCap, pqPtr⟩
    sender := sg
    pending := pg
    kyber := kg
    regIds := unpack32 s.remoteRegistrationId ++ unpack32 s.localRegistrationId
  }
  refine Entails.sepExists_right G ?_
  have hcanon : CanonSession G s :=
    ⟨rfl, rfl, hsender_canon, hchains_len, hchains_canon, hpending_canon⟩
  refine Entails.pure_right hcanon ?_
  unfold sessionStateReprAt
  have halice_eq : G.alice.bytes = s.aliceBaseKey := rfl
  have hreg1 : G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat := by
    simp only [G, leBytes, unpack32, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
  have hreg2 : (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat := by
    simp only [G, leBytes, unpack32, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
  refine Entails.pure_right ⟨hpending_rel, hkyber_rel, halice_eq, hreg1, hreg2⟩ ?_
  unfold sessionStateAt
  have hrem_deser :
      match s.state.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey := by
    dsimp only [G]
    rcases s.state.remoteIdentity with _ | ik
    · rfl
    · exact deserialize_serialize_pk_ssg ik.publicKey
  have hrem_len : s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33 := by
    dsimp only [G]
    rcases s.state.remoteIdentity with _ | ik <;> simp [serialize_ik_length_ssg]
  have hst_pure :
      PublicKey.deserialize G.localIk.bytes = .ok s.state.localIdentity.publicKey ∧
      (match s.state.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
      G.chains.length = s.state.receiverChains.length ∧
      G.pending.isSome = s.state.pendingPreKey ∧
      G.regIds.length = 8 ∧
      G.localIk.bytes.length = 33 ∧
      (s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33) :=
    ⟨deserialize_serialize_pk_ssg s.state.localIdentity.publicKey,
      hrem_deser, hchains_len, hpending_some, rfl,
      serialize_ik_length_ssg s.state.localIdentity, hrem_len⟩
  refine Entails.pure_right hst_pure ?_
  dsimp only [G, vecGhostAt]
  have ha150 : a + 0x150#64 + 4#64 = a + 0x154#64 := by rw [BitVec.add_assoc]; rfl
  rw [pointsToBytes_append, unpack32_length, ha150,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  exact Entails.refl _

/-! ## Record-level representation -/

private theorem vecAt_prev_zero_eq_x (out : BitVec 64) :
    vecAt A0 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    SeedLengthFacts.pure_true_sepConj hpure]

/-- Converts `deserOutRecordX out r` for a `DeserializeScopeP` record into `sessionRecordAt` with a `CanonRecord` ghost witness. -/
theorem deserReprX_ok (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP r) (out : BitVec 64) :
    deserOutRecordX out r ⊢
      ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r := by
  obtain ⟨s, hs, _⟩ := hr.2
  have hdef :
      deserOutRecordX out r =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          prostSSGXAt A0 (out + 0x18#64) (ssgxOf s) := by
    unfold deserOutRecordX
    rw [ssgxAfter_recFieldsX r hr s hs]
    ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right (prostSSGX_repr r hr s hs (out + 0x18#64))) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜CanonSession G s⌝ ∗ sessionStateReprAt A0 (out + 0x18#64) G s)) =
      (⌜CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          sessionStateReprAt A0 (out + 0x18#64) G s)) := by
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right ⟨0#64, 8#64, some G⟩ ?_
  refine Entails.pure_right ?_ ?_
  · unfold CanonRecord CanonCur
    rw [hs]
    exact hcanon
  · unfold sessionRecordAt
    rw [hs]
    dsimp only
    rw [vecAt_prev_zero_eq_x]
    exact Entails.refl _

end CryptoVerification.E2E.Record.L1GX.Leaf.ProstSSGXRepr
