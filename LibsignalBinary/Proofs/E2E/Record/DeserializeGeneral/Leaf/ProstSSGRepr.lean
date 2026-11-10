/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push

/-!
# Session Representation Leaf (`prostSSG_repr`) for General `SessionStructure`

Proves `prostSSG_repr`, converting `prostSSGAt A ss (ssgOf s)` for an in-scope session `s` into
`sessionStateReprAt` with a canonical `SessionGhost` (`CanonSession`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ProstSSGRepr

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession CanonChain CanonSender CanonPending)
open CryptoGames.HMAC

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

private def pendingTail_ssg (w1 w2 : BitVec 32) : List (BitVec 8) :=
  unpack32 0#32 ++ (unpack32 w1 ++ (unpack64 0#64 ++ (unpack32 0#32 ++ unpack32 w2)))

private theorem pendingTail_length_ssg (w1 w2 : BitVec 32) :
    (pendingTail_ssg w1 w2).length = 24 := rfl

private theorem pendingTail_optU32Rel_ssg (w1 w2 : BitVec 32) :
    OptU32Rel (pendingTail_ssg w1 w2) none := rfl

private theorem pendingTail_timestamp_ssg (w1 w2 : BitVec 32) :
    ((pendingTail_ssg w1 w2).drop 8).take 8 = leBytes 8 (0#64).toNat := rfl

private theorem pendingTail_spkId_ssg (w1 w2 : BitVec 32) :
    ((pendingTail_ssg w1 w2).drop 16).take 4 = leBytes 4 (0#32).toNat := rfl

private theorem pendingTail_pointsToBytes_ssg (ss : BitVec 64) (w1 w2 : BitVec 32) :
    ((ss + 0x110#64) ↦₃₂ 0#32) ∗ ((ss + 0x114#64) ↦₃₂ w1) ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ 0#32) ∗ ((ss + 0x124#64) ↦₃₂ w2) =
      ((ss + 0xf8#64 + 24#64) ↦ₛ pendingTail_ssg w1 w2) := by
  have ha0 : ss + 0xf8#64 + 24#64 = ss + 0x110#64 := by rw [BitVec.add_assoc]; rfl
  have ha1 : ss + 0x110#64 + 4#64 = ss + 0x114#64 := by rw [BitVec.add_assoc]; rfl
  have ha2 : ss + 0x114#64 + 4#64 = ss + 0x118#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : ss + 0x118#64 + 8#64 = ss + 0x120#64 := by rw [BitVec.add_assoc]; rfl
  have ha4 : ss + 0x120#64 + 4#64 = ss + 0x124#64 := by rw [BitVec.add_assoc]; rfl
  unfold pendingTail_ssg
  rw [ha0, pointsToBytes_append, unpack32_length,
    ha1, pointsToBytes_append, unpack32_length,
    ha2, pointsToBytes_append, unpack64_length,
    ha3, pointsToBytes_append, unpack32_length, ha4]
  simp only [← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

private theorem prostPendingG_entails_optTailVecAt (s : Session (List (BitVec 8)))
    (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p →
      p.preKeyId = none ∧ p.signedPreKeyId = 0 ∧ p.timestamp = 0)
    (ss : BitVec 64) :
    (match s.pendingPreKey.map (fun p => p.baseKey.serialize) with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A0 (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ⊢
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
    obtain ⟨hpre, hspk, hts⟩ := hp p hpend
    unfold vecU8
    rw [memRegion_four (ss + 0x114#64), memRegion_four (ss + 0x124#64)]
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    let g : TailVecGhost := {
      vec := ⟨cap, ptr, p.baseKey.serialize⟩
      tail := pendingTail_ssg w1 w2
    }
    refine Entails.sepExists_right (some g) ?_
    have hcanon : CanonPending (some g) (some p) := rfl
    have hrel : PendingRel (some g) (some p) := by
      refine ⟨deserialize_serialize_pk_ssg p.baseKey, ?_, ?_, ?_, serialize_pk_length_ssg p.baseKey⟩
      · rw [hpre]; exact pendingTail_optU32Rel_ssg w1 w2
      · rw [hts]; exact pendingTail_timestamp_ssg w1 w2
      · rw [hspk]; exact pendingTail_spkId_ssg w1 w2
    have hsome : (some g).isSome = s.state.pendingPreKey := by
      rw [hwf, hpend]; rfl
    refine Entails.pure_right ⟨hcanon, hrel, hsome⟩ ?_
    unfold optTailVecAt
    refine Entails.pure_right (pendingTail_length_ssg w1 w2) ?_
    dsimp only [g, vecGhostAt]
    rw [← pendingTail_pointsToBytes_ssg ss w1 w2]
    exact Entails.refl _

theorem prostSSG_repr_impl (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) (ss : BitVec 64) :
    prostSSGAt A0 ss (ssgOf s) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G s⌝ ∗ sessionStateReprAt A0 ss G s := by
  obtain ⟨⟨hr_in, hr_pq, hr_repr⟩, s', hs', hscope⟩ := hr
  have hss' : s = s' := Option.some.inj (hs.symm.trans hs')
  subst hss'
  obtain ⟨-, hseeds, -, -⟩ := hr_in s hs
  have hpq : s.state.pqRatchetState = [] := hr_pq s hs
  obtain ⟨hmax_mk, hclamp, hwf, -⟩ := hr_repr s hs
  obtain ⟨-, hkyber, hlocReg, hremReg, halice, hpend_fields⟩ := hscope
  unfold prostSSGAt ssgOf
  dsimp only
  have hrecv := prostRecvG_entails_vecAt_chainAt s hseeds hmax_mk (ss + 0x48#64)
  have hsender := prostSenderG_entails_optSenderChainAt s.state.senderChain hclamp ss
  have hpending := prostPendingG_entails_optTailVecAt s hwf hpend_fields ss
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
    alice := ⟨aliceCap, alicePtr, []⟩
    pq := ⟨pqCap, pqPtr⟩
    sender := sg
    pending := pg
    kyber := none
    regIds := unpack64 0#64
  }
  refine Entails.sepExists_right G ?_
  have hcanon : CanonSession G s :=
    ⟨rfl, rfl, hsender_canon, hchains_len, hchains_canon, hpending_canon⟩
  refine Entails.pure_right hcanon ?_
  unfold sessionStateReprAt
  have hkyber_rel : KyberRel G.kyber s.pendingKyberPreKey := by
    rw [hkyber]; trivial
  have halice_eq : G.alice.bytes = s.aliceBaseKey := halice.symm
  have hreg1 : G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat := by
    dsimp only [G]; rw [hremReg]; rfl
  have hreg2 : (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat := by
    dsimp only [G]; rw [hlocReg]; rfl
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
  dsimp only [G, vecGhostAt, optTailVecAt]
  rw [hpq,
    show ss + 0x128#64 + 8#64 = ss + 0x130#64 by rw [BitVec.add_assoc]; rfl,
    ← pointsTo64_eq_pointsToBytes]
  simp only [sepConj_assoc]
  exact Entails.refl _

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ProstSSGRepr
