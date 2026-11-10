/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure

/-!
# Reversible `SepProp` layout decompositions for `sessionStateReprAt` (`0x25fd0`)

Decomposes `sessionStateReprAt A ss G s` into read atoms (`tags1to5Cells`, `optSenderChainAt`,
`vecAt` for `receiver_chains`, `pendingUnpacked`, `tags10to15Cells`, `kyberUnpacked`) and untouched
`Vec` headers/buffers (`sessionUnused`) via exact `SepProp` equalities.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.SessionLenAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization

/-! ## Byte-slice splitting for `regIds`, `PendingPreKey`, and `PendingKyberPreKey` tails -/

private theorem list_split_4_4 {α : Type} (bs : List α) (h : bs.length = 8) :
    bs = bs.take 4 ++ (bs.drop 4).take 4 := by
  have h1 : (bs.drop 4).take 4 = bs.drop 4 := List.take_of_length_le (by simp [h])
  rw [h1, List.take_append_drop]

theorem regIds_pointsToBytes_eq (a : BitVec 64) (bs : List (BitVec 8)) (rem loc : BitVec 32)
    (hlen : bs.length = 8)
    (hrem : bs.take 4 = leBytes 4 rem.toNat)
    (hloc : (bs.drop 4).take 4 = leBytes 4 loc.toNat) :
    (a ↦ₛ bs) = (a ↦₃₂ rem) ∗ ((a + 4#64) ↦₃₂ loc) := by
  conv => lhs; rw [list_split_4_4 bs hlen]
  rw [pointsToBytes_append, hrem, hloc, leBytes_4_eq_unpack32, leBytes_4_eq_unpack32,
    unpack32_length, ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]

private theorem list_split_8_4 {α : Type} (bs : List α) :
    bs = bs.take 4 ++ bs.drop 4 :=
  (List.take_append_drop 4 bs).symm

theorem kyberTail_pointsToBytes_eq (a : BitVec 64) (tail : List (BitVec 8)) (id : BitVec 32)
    (htake : tail.take 4 = leBytes 4 id.toNat) :
    (a ↦ₛ tail) = (a ↦₃₂ id) ∗ ((a + 4#64) ↦ₛ tail.drop 4) := by
  conv => lhs; rw [list_split_8_4 tail]
  rw [pointsToBytes_append, htake, leBytes_4_eq_unpack32, unpack32_length,
    ← pointsTo32_eq_pointsToBytes]

/-- Value word at offset +4 of a `PendingPreKey`'s `pre_key_id: Option<u32>`. -/
def pendingPreKeyIdValAt (a : BitVec 64) (tail : List (BitVec 8)) : Option (BitVec 32) → SepProp
  | none => a ↦ₛ (tail.drop 4).take 4
  | some v => a ↦₃₂ v

private theorem list_split_24 (bs : List (BitVec 8)) :
    bs = bs.take 4 ++ ((bs.drop 4).take 4 ++ ((bs.drop 8).take 8 ++
      ((bs.drop 16).take 4 ++ bs.drop 20))) := by
  have h16 : (bs.drop 16).take 4 ++ bs.drop 20 = bs.drop 16 := by
    rw [show bs.drop 20 = (bs.drop 16).drop 4 by simp, List.take_append_drop]
  have h8 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
    rw [show bs.drop 16 = (bs.drop 8).drop 8 by simp, List.take_append_drop]
  have h4 : (bs.drop 4).take 4 ++ bs.drop 8 = bs.drop 4 := by
    rw [show bs.drop 8 = (bs.drop 4).drop 4 by simp, List.take_append_drop]
  rw [h16, h8, h4, List.take_append_drop]

theorem pendingTail_pointsToBytes_eq (a : BitVec 64) (tail : List (BitVec 8)) (p : PendingPreKey)
    (hlen : tail.length = 24)
    (hopt : OptU32Rel tail p.preKeyId)
    (hts : (tail.drop 8).take 8 = leBytes 8 p.timestamp.toNat)
    (hspk : (tail.drop 16).take 4 = leBytes 4 p.signedPreKeyId.toNat) :
    (a ↦ₛ tail) =
      (a ↦₃₂ optU32Tag p.preKeyId) ∗
      pendingPreKeyIdValAt (a + 4#64) tail p.preKeyId ∗
      ((a + 8#64) ↦₆₄ p.timestamp) ∗
      ((a + 16#64) ↦₃₂ p.signedPreKeyId) ∗
      ((a + 20#64) ↦ₛ tail.drop 20) := by
  have hlen4 : (tail.take 4).length = 4 := by simp [hlen]
  have hlen4' : ((tail.drop 4).take 4).length = 4 := by simp [hlen]
  have hlen8 : ((tail.drop 8).take 8).length = 8 := by simp [hlen]
  have hlen16 : ((tail.drop 16).take 4).length = 4 := by simp [hlen]
  conv => lhs; rw [list_split_24 tail]
  rw [pointsToBytes_append, hlen4,
      pointsToBytes_append (a + 4#64), hlen4',
      pointsToBytes_append (a + 4#64 + 4#64), hlen8,
      pointsToBytes_append (a + 4#64 + 4#64 + 8#64), hlen16]
  have ha8 : a + 4#64 + 4#64 = a + 8#64 := by bv_omega
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha20 : a + 16#64 + 4#64 = a + 20#64 := by bv_omega
  rw [ha8, ha16, ha20, hts, leBytes_8_eq_unpack64, ← pointsTo64_eq_pointsToBytes,
      hspk, leBytes_4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]
  cases hpk : p.preKeyId with
  | none =>
    rw [hpk] at hopt
    dsimp [OptU32Rel] at hopt
    rw [hopt, zeroBytes4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]
    simp only [optU32Tag, pendingPreKeyIdValAt]
  | some v =>
    rw [hpk] at hopt
    rcases hopt with ⟨htag, hval⟩
    rw [htag, oneBytes4_eq_unpack32, ← pointsTo32_eq_pointsToBytes,
        hval, leBytes_4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]
    simp only [optU32Tag, pendingPreKeyIdValAt]

/-! ## Unpacked `PendingPreKey` and `PendingKyberPreKey` predicates -/

def pendingUnpacked (A : RustAlloc) (a : BitVec 64) :
    Option TailVecGhost → Option PendingPreKey → SepProp
  | none, none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some g, some p =>
    (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
      ((a + 24#64) ↦₃₂ optU32Tag p.preKeyId) ∗
      pendingPreKeyIdValAt (a + 28#64) g.tail p.preKeyId ∗
      ((a + 32#64) ↦₆₄ p.timestamp) ∗
      ((a + 40#64) ↦₃₂ p.signedPreKeyId) ∗
      ((a + 44#64) ↦ₛ g.tail.drop 20) ∗
      vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes
  | _, _ => ⌜False⌝

theorem optTailVecAt_pending_eq (A : RustAlloc) (a : BitVec 64)
    (gp : Option TailVecGhost) (mp : Option PendingPreKey)
    (hrel : PendingRel gp mp) :
    optTailVecAt A 48 a gp =
      ⌜match gp with | none => True | some g => g.tail.length = 24⌝ ∗
        pendingUnpacked A a gp mp := by
  cases gp with
  | none =>
    cases mp with
    | none =>
      simp only [optTailVecAt, pendingUnpacked, Nat.reduceSub, pure_true_sepConj]
    | some _ => contradiction
  | some g =>
    cases mp with
    | none => contradiction
    | some p =>
      rcases hrel with ⟨_, hopt, hts, hspk, _⟩
      simp only [optTailVecAt, Nat.reduceSub, pendingUnpacked]
      apply pure_sepConj_congr
      intro hlen
      have htail := pendingTail_pointsToBytes_eq (a + 24#64) g.tail p hlen hopt hts hspk
      have hvec : vecGhostAt A g.vec a =
          (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes := by
        simp only [vecGhostAt, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc]
      have ha28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
      have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
      have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
      have ha44 : a + 24#64 + 20#64 = a + 44#64 := by bv_omega
      rw [ha28, ha32, ha40, ha44] at htail
      rw [hvec, htail]
      ac_rfl

def kyberUnpacked (A : RustAlloc) (a : BitVec 64) :
    Option TailVecGhost → Option PendingKyberPreKey → SepProp
  | none, none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 24
  | some g, some k =>
    (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
      ((a + 24#64) ↦₃₂ k.preKeyId) ∗ ((a + 28#64) ↦ₛ g.tail.drop 4) ∗
      vecU8Buf A g.vec.cap g.vec.ptr k.ciphertext
  | _, _ => ⌜False⌝

theorem optTailVecAt_kyber_eq (A : RustAlloc) (a : BitVec 64)
    (gk : Option TailVecGhost) (mk : Option PendingKyberPreKey)
    (hrel : KyberRel gk mk) :
    optTailVecAt A 32 a gk =
      ⌜match gk with | none => True | some g => g.tail.length = 8⌝ ∗
        kyberUnpacked A a gk mk := by
  cases gk with
  | none =>
    cases mk with
    | none =>
      simp only [optTailVecAt, kyberUnpacked, Nat.reduceSub, pure_true_sepConj]
    | some _ => contradiction
  | some g =>
    cases mk with
    | none => contradiction
    | some k =>
      rcases hrel with ⟨hbs, htake⟩
      simp only [optTailVecAt, Nat.reduceSub, kyberUnpacked]
      have htail := kyberTail_pointsToBytes_eq (a + 24#64) g.tail k.preKeyId htake
      have ha28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
      rw [ha28] at htail
      have hvec : vecGhostAt A g.vec a =
          (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
          vecU8Buf A g.vec.cap g.vec.ptr k.ciphertext := by
        simp only [vecGhostAt, hbs, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc]
      rw [hvec, htail]
      ac_rfl

theorem pendingUnpacked_cap_lt {A : RustAlloc} {a : BitVec 64} {g : TailVecGhost} {p : PendingPreKey}
    {R : SepProp} {m : Memory} (hm : m ⊨ pendingUnpacked A a (some g) (some p) ∗ R) :
    g.vec.cap.toNat < 2 ^ 63 := by
  dsimp only [pendingUnpacked] at hm
  have hm' : m ⊨ vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes ∗
      ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
       ((a + 24#64) ↦₃₂ optU32Tag p.preKeyId) ∗
       pendingPreKeyIdValAt (a + 28#64) g.tail p.preKeyId ∗
       ((a + 32#64) ↦₆₄ p.timestamp) ∗ ((a + 40#64) ↦₃₂ p.signedPreKeyId) ∗
       ((a + 44#64) ↦ₛ g.tail.drop 20) ∗ R) := by
    convert hm using 1; ac_rfl
  exact vecU8Buf_cap_lt hm'

theorem kyberUnpacked_cap_lt {A : RustAlloc} {a : BitVec 64} {g : TailVecGhost} {k : PendingKyberPreKey}
    {R : SepProp} {m : Memory} (hm : m ⊨ kyberUnpacked A a (some g) (some k) ∗ R) :
    g.vec.cap.toNat < 2 ^ 63 := by
  dsimp only [kyberUnpacked] at hm
  have hm' : m ⊨ vecU8Buf A g.vec.cap g.vec.ptr k.ciphertext ∗
      ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
       ((a + 24#64) ↦₃₂ k.preKeyId) ∗ ((a + 28#64) ↦ₛ g.tail.drop 4) ∗ R) := by
    convert hm using 1; ac_rfl
  exact vecU8Buf_cap_lt hm'

theorem length_le_bytesField_length (t : Nat) (bs : List (BitVec 8)) :
    bs.length ≤ (bytesField t bs).length := by
  by_cases h : bs = []
  · subst h; simp [bytesField]
  · simp [bytesField, h, lenField]; omega

theorem ofNat64_length_beq_zero_of_bytesField_lt {t : Nat} {bs : List (BitVec 8)}
    (h : (bytesField t bs).length < 2 ^ 64) :
    (BitVec.ofNat 64 bs.length == 0#64) = (bs == []) := by
  have hlt : bs.length < 2 ^ 64 := Nat.lt_of_le_of_lt (length_le_bytesField_length t bs) h
  rw [ofNat64_beq_zero_of_lt hlt]
  cases bs <;> rfl

theorem ofNat64_length_bne_zero_of_bytesField_lt {t : Nat} {bs : List (BitVec 8)}
    (h : (bytesField t bs).length < 2 ^ 64) :
    (BitVec.ofNat 64 bs.length != 0#64) = (bs != []) := by
  simp [bne, ofNat64_length_beq_zero_of_bytesField_lt h]

/-! ## Sender chain view (`optSenderChainAt` ↔ `protoChainAt`) -/

theorem chainAt_eq_protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      ⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ protoChainAt A gc a := by
  dsimp only [chainAt, protoChainAt]
  rw [pure_sepConj_pure_assoc]
  congr 1
  apply congrArg SepProp.pure
  exact propext ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h4, h5⟩, h1, h2, h3⟩,
    fun ⟨⟨h4, h5⟩, h1, h2, h3⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

theorem optSenderChainAt_some_eq_sessLen (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) =
      ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
        protoChainAt A (senderGhostAsChain g, senderAsChain sc) a := by
  dsimp only [optSenderChainAt, protoChainAt, senderGhostAsChain, senderAsChain]
  rw [pure_sepConj_pure_assoc]
  congr 1
  apply congrArg SepProp.pure
  have hmk : ([] : List MessageKeyGenerator).length ≤ maxMessageKeys := Nat.zero_le _
  exact propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h2, h3, h4⟩, h1, hmk, rfl⟩,
    fun ⟨⟨h2, h3, h4⟩, h1, _, _⟩ => ⟨h1, h2, h3, h4⟩⟩

theorem chainAt_expose_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    protoChainAt A gc a =
      (a ↦₆₄ gc.1.srk.cap) ∗
      (⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
        ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        vecU8Buf A gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
        vecGhostAt A gc.1.priv (a + 24#64) ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (gc.1.keys.zip gc.2.messageKeys) ∗
        optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) := by
  unfold protoChainAt
  have hsrk : vecGhostAt A gc.1.srk a =
      (a ↦₆₄ gc.1.srk.cap) ∗ ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      vecU8Buf A gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes := by
    simp only [vecGhostAt, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc]
  rw [hsrk]
  ac_rfl

theorem chainAt_srk_cap_lt {A : RustAlloc} {gc : ChainGhost × ReceiverChain} {a : BitVec 64}
    {R : SepProp} {m : Memory} (hm : m ⊨ protoChainAt A gc a ∗ R) :
    gc.1.srk.cap.toNat < 2 ^ 63 := by
  rw [chainAt_expose_cap] at hm
  have hm' : m ⊨ vecU8Buf A gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
      ((a ↦₆₄ gc.1.srk.cap) ∗
       ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
         gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
       ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
       vecGhostAt A gc.1.priv (a + 24#64) ∗
       vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
         (gc.1.keys.zip gc.2.messageKeys) ∗
       optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗ R) := by
    convert hm using 1; ac_rfl
  exact vecU8Buf_cap_lt hm'

/-! ## Cell bundles and `sessionStateReprAt` decomposition -/

/-- The 8 saved-register stack slots of `SessionStructure::encoded_len` (`sp - 64 .. sp - 8`). -/
def frameCells (sp v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) : SepProp :=
  ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
  ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
  ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
  ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)

theorem stackAt_sessionLen_eq (sp : BitVec 64) :
    stackAt sp sessionLenStack =
      stackAt (sp - 64#64) chainLenStack ∗
      (∃∗ v64 : BitVec 64, ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
       ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        frameCells sp v64 v56 v48 v40 v32 v24 v16 v8) := by
  have hsplit := ProofLib.stackAt_split_cells sp chainLenStack 8 (by decide)
  have heq : chainLenStack + 8 * 8 = sessionLenStack := rfl
  rw [← heq, hsplit]
  congr 1
  unfold frameCells
  cells_unfold

/-- Cells of `ss` read in Tags 1–5 (`+0x000..+0x110`). -/
def tags1to5Cells (ss : BitVec 64) (G : SessionGhost) (s : Session (List (BitVec 8))) : SepProp :=
  ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
  ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 G.remoteIk.bytes.length) ∗
  ((ss + 64#64) ↦₆₄ 32#64) ∗
  ((ss + 328#64) ↦₃₂ s.state.sessionVersion) ∗
  ((ss + 332#64) ↦₃₂ s.state.previousCounter)

/-- Cells of `ss` read in Tags 10, 11, 13, 15 (`+0x2bc..+0x358` and `+0x3e0..+0x41c`). -/
def tags10to15Cells (ss : BitVec 64) (s : Session (List (BitVec 8))) : SepProp :=
  ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 s.aliceBaseKey.length) ∗
  ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 s.state.pqRatchetState.length) ∗
  ((ss + 336#64) ↦₃₂ s.remoteRegistrationId) ∗
  ((ss + 340#64) ↦₃₂ s.localRegistrationId)

/-- Untouched `cap`/`ptr` header words and `Vec<u8>` heap buffers of `ss`. -/
def sessionUnused (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) : SepProp :=
  (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
    vecU8Buf A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
  ((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗
    vecU8Buf A G.remoteIk.cap G.remoteIk.ptr G.remoteIk.bytes ∗
  ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
    vecU8Buf A G.root.cap G.root.ptr (HMAC.keyToBytes32 s.state.rootKey) ∗
  ((ss + 72#64) ↦₆₄ G.chainsCap) ∗
  ((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗
    vecU8Buf A G.alice.cap G.alice.ptr s.aliceBaseKey ∗
  ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
    vecU8Buf A G.pq.cap G.pq.ptr s.state.pqRatchetState

/-- Unpacked heap body of `sessionStateAt` (after extracting pure invariants). -/
def sessionBodyUnpacked (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) : SepProp :=
  tags1to5Cells ss G s ∗
  optSenderChainAt A (ss + 144#64) G.sender s.state.senderChain ∗
  ((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
  ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip s.state.receiverChains).length) ∗
  vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip s.state.receiverChains) ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗
  tags10to15Cells ss s ∗
  optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  sessionUnused A ss G s

theorem sessionStateAt_body_eq (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8)))
    (halice : G.alice.bytes = s.aliceBaseKey)
    (hreg_len : G.regIds.length = 8)
    (hrem : G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat)
    (hloc : (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat) :
    (vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (HMAC.keyToBytes32 s.state.rootKey) ∗
      vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
        (G.chains.zip s.state.receiverChains) ∗
      vecGhostAt A G.alice (ss + 0x60#64) ∗
      vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr s.state.pqRatchetState ∗
      optSenderChainAt A (ss + 0x90#64) G.sender s.state.senderChain ∗
      optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      ((ss + 0x148#64) ↦₃₂ s.state.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ s.state.previousCounter) ∗
      ((ss + 0x150#64) ↦ₛ G.regIds)) =
      sessionBodyUnpacked A ss G s := by
  have h1 : vecGhostAt A G.localIk ss =
      (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
      ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
      vecU8Buf A G.localIk.cap G.localIk.ptr G.localIk.bytes := by
    simp only [vecGhostAt, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc]
  have h2 : vecGhostAt A G.remoteIk (ss + 0x18#64) =
      ((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗
      ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 G.remoteIk.bytes.length) ∗
      vecU8Buf A G.remoteIk.cap G.remoteIk.ptr G.remoteIk.bytes := by
    simp only [vecGhostAt, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc, arm64_norm]
  have h3 : vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (HMAC.keyToBytes32 s.state.rootKey) =
      ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
      ((ss + 64#64) ↦₆₄ 32#64) ∗
      vecU8Buf A G.root.cap G.root.ptr (HMAC.keyToBytes32 s.state.rootKey) := by
    simp only [vecU8At_eq_header_sep_buf, vecHeader, keyToBytes32_length_sessLen, sepConj_assoc, arm64_norm]
  have h4 : vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip s.state.receiverChains) =
      ((ss + 72#64) ↦₆₄ G.chainsCap) ∗ ((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip s.state.receiverChains).length) ∗
      vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip s.state.receiverChains) := by
    simp only [vecAt, vecHeader, sepConj_assoc, arm64_norm]
  have h5 : vecGhostAt A G.alice (ss + 0x60#64) =
      ((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 s.aliceBaseKey.length) ∗
      vecU8Buf A G.alice.cap G.alice.ptr s.aliceBaseKey := by
    simp only [vecGhostAt, halice, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc, arm64_norm]
  have h6 : vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr s.state.pqRatchetState =
      ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 s.state.pqRatchetState.length) ∗
      vecU8Buf A G.pq.cap G.pq.ptr s.state.pqRatchetState := by
    simp only [vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc, arm64_norm]
  have h7 : ((ss + 0x150#64) ↦ₛ G.regIds) =
      ((ss + 336#64) ↦₃₂ s.remoteRegistrationId) ∗ ((ss + 340#64) ↦₃₂ s.localRegistrationId) := by
    have h := regIds_pointsToBytes_eq (ss + 336#64) G.regIds s.remoteRegistrationId s.localRegistrationId
      hreg_len hrem hloc
    have ha : ss + 336#64 + 4#64 = ss + 340#64 := by bv_omega
    rw [ha] at h
    exact h
  rw [h1, h2, h3, h4, h5, h6, h7]
  unfold sessionBodyUnpacked tags1to5Cells tags10to15Cells sessionUnused
  ac_rfl

end CryptoVerification.E2E.Record.Serialization.SessionLenAux
