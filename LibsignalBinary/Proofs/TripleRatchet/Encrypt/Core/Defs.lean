/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WPp

/-!
# Shared Definitions, Model Lemmas, and Layout Helpers for `OTR::encrypt`

Provides AES-256-CBC and `OtrEncryptGhost.model` unfolding lemmas, word-level pack/unpack helpers
for `HKDF.Salt`, `SignalMessage`, `Vec<u8>`, and `ChainKey`, and relocatable `[LibsignalPlacement]`
specifications (`otrEncryptPlacedSpecF`, `otrEncryptPlacedSpec`).
-/

@[expose] public section

namespace CryptoVerification

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
gen_ls_blk 125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
gen_ls_blk 428

end CryptoVerification

namespace CryptoVerification.LibsignalTripleRatchet.Encrypt


open Arm64 ProofLib CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


/-! ## Pure model lemmas -/

theorem blockToBytesLE_length (b : BitVec 128) :
    (blockToBytesLE b).length = 16 := by
  simp [blockToBytesLE]

theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
    HKDF.bytesToKey32 (keyToBytes32 k) = k :=
  CryptoVerification.LibsignalAesCbc.Run.Bytes.bytesToKey_keyToBytes k

theorem bytesToBlock_blockToBytesLE (b : BitVec 128) :
    bytesToBlock (CBC.blockToBytesLE b) = b :=
  CryptoVerification.LibsignalAesCbc.Run.Bytes.bytesToBlock_blockToBytes b

theorem aesCbcEncrypt_length (E : BitVec 256 → BitVec 128 → BitVec 128)
    (k : BitVec 256) (iv : BitVec 128) (pt : List (BitVec 8)) :
    (aesCbcEncrypt E k iv pt).length = 16 * (pt.length / 16 + 1) := by
  have hblk : ∀ l : List (BitVec 128),
      (l.flatMap blockToBytesLE).length = 16 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons h t ih =>
      simp only [List.flatMap_cons, List.length_append, ih, List.length_cons,
        blockToBytesLE_length]
      omega
  unfold aesCbcEncrypt
  rw [hblk, List.Vector.toList_length]
  rfl

theorem aesCbcEncrypt_length_le_u32 (E : BitVec 256 → BitVec 128 → BitVec 128)
    (k : BitVec 256) (iv : BitVec 128) (pt : List (BitVec 8)) (hpt : pt.length < 2 ^ 32) :
    (aesCbcEncrypt E k iv pt).length ≤ 2 ^ 32 := by
  rw [aesCbcEncrypt_length]
  omega

theorem aesCbcEncrypt_length_lt_2_63 (E : BitVec 256 → BitVec 128 → BitVec 128)
    (k : BitVec 256) (iv : BitVec 128) (pt : List (BitVec 8)) (hpt : pt.length < 2 ^ 32) :
    (aesCbcEncrypt E k iv pt).length < 2 ^ 63 := by
  have h := aesCbcEncrypt_length_le_u32 E k iv pt hpt
  omega

theorem length_flatMap_toBEBytes :
    ∀ l : List (BitVec 32), (l.flatMap (toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | _ :: xs => by
    simp [List.flatMap_cons, toBEBytes, length_flatMap_toBEBytes xs]
    omega

theorem messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  unfold ChainKey.messageKeys Ratchet.chainHmac hmacWith sha256With
  rw [length_flatMap_toBEBytes]
  simp

/-! ## Model unfolding lemmas for `OtrEncryptGhost.model` -/

set_option linter.unusedSimpArgs false in
theorem model_of_send_none (x : OtrEncryptGhost) (C : Crypto) (S : SpqrModel)
    (hnp : S.sendPanics x.ot.pqrState x.rest = false)
    (hsend : S.send x.ot.pqrState x.rest = none) :
    x.model C S uuidTryParse = (Except.error .invalidState, x.ot) := by
  unfold OtrEncryptGhost.model OutgoingTripleRatchet.encrypt SpqrModel.spqr Mut.exec
  simp only [ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
    ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad,
    MonadState.get, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    StateT.pure, StateT.bind, Functor.map, StateT.map, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.pure, throwThe, liftE, hnp, Bool.false_eq_true,
    ↓reduceIte, hsend]

set_option linter.unusedSimpArgs false in
theorem model_of_send_some_panic (x : OtrEncryptGhost) (C : Crypto) (S : SpqrModel)
    (newPqrState : List (BitVec 8))
    (pqrKey : HKDF.Salt) (pqrMsg : List (BitVec 8))
    (hsend : S.send x.ot.pqrState x.rest = some (newPqrState, pqrKey, pqrMsg))
    (hnck : x.ot.senderChainKey.nextChainKey C.F = Except.error .panic) :
    (x.model C S uuidTryParse).1 = Except.error .panic := by
  unfold OtrEncryptGhost.model OutgoingTripleRatchet.encrypt SpqrModel.spqr Mut.exec
  cases hnp : S.sendPanics x.ot.pqrState x.rest <;>
  simp only [ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
    ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad,
    MonadState.get, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    StateT.pure, StateT.bind, Functor.map, StateT.map, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.pure, throwThe, liftE, hnp, Bool.false_eq_true,
    ↓reduceIte, hsend, hnck]

set_option linter.unusedSimpArgs false in
theorem model_of_send_some_ok (x : OtrEncryptGhost) (C : Crypto) (S : SpqrModel)
    (newPqrState : List (BitVec 8))
    (pqrKey : HKDF.Salt) (pqrMsg : List (BitVec 8)) (ck' : ChainKey)
    (hnp : S.sendPanics x.ot.pqrState x.rest = false)
    (hsend : S.send x.ot.pqrState x.rest = some (newPqrState, pqrKey, pqrMsg))
    (hnck : x.ot.senderChainKey.nextChainKey C.F = Except.ok ck') :
    let mk := (x.ot.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
    let ctext := aesCbcEncrypt C.E mk.cipherKey mk.iv x.ptext
    let msg := SignalMessage.new C.F protoSignalCodec x.ot.sessionVersion mk.macKey
      (x.addresses uuidTryParse) x.ot.senderRatchetKey.publicKey x.ot.senderChainKey.index
      x.ot.previousCounter ctext x.ot.localIdentityKey x.ot.remoteIdentityKey pqrMsg
    x.model C S uuidTryParse =
      (Except.ok msg, { x.ot with senderChainKey := ck', pqrState := newPqrState }) := by
  intro mk ctext msg
  unfold OtrEncryptGhost.model OutgoingTripleRatchet.encrypt SpqrModel.spqr Mut.exec
  simp only [ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
    ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad,
    MonadState.get, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    StateT.pure, StateT.bind, Functor.map, StateT.map, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.pure, throwThe, liftE, hnp, Bool.false_eq_true,
    ↓reduceIte, hsend, hnck, mk, ctext, msg]


/-! ## Region and stack arithmetic -/

/-- Split `memRegion (sp - c) N` at `n` (`N = n + k`, `c' = c - n`). -/
theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

/-- Split `memRegion (a + c) (n + k)` at `n`. -/
theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Carve a smaller `stackAt sp K` out of `stackAt sp N` (`K ≤ N`). -/
theorem stackAt_sub (sp : BitVec 64) (N K : Nat) (hK : K ≤ N := by decide)
    (hN : N < 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) (N - K) ∗ stackAt sp K := by
  simp only [stackAt]
  exact mr_cut' sp N K (N - K) K N (by omega) (by omega) (by omega) hN (by omega)

/-! ## Word-level unpack/pack lemmas for structs and byte slices -/

/-- Heap buffer portion of `spqrSendKeyAt A a pqrKey`, parameterized by the 3 header words `k0 k1 k2`. -/
def optKeyBuf (A : RustAlloc) (k0 k1 k2 : BitVec 64) : HKDF.Salt → SepProp
  | none => ⌜k0 = noneCap⌝
  | some k => ⌜k2 = BitVec.ofNat 64 k.toList.length⌝ ∗ vecU8Buf A k0 k1 k.toList

theorem optKeyAt_unpack (A : RustAlloc) (a : BitVec 64) (pqrKey : HKDF.Salt) :
    spqrSendKeyAt A a pqrKey ⊢
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
        (a ↦₆₄ k0) ∗ ((a + 8#64) ↦₆₄ k1) ∗ ((a + 16#64) ↦₆₄ k2) ∗
        optKeyBuf A k0 k1 k2 pqrKey := by
  cases pqrKey with
  | none =>
    simp only [spqrSendKeyAt, optKeyBuf]
    rw [mr_cut_add a 8 8 8 (by decide)]
    have h16 : a + BitVec.ofNat 64 (8 + 8) = a + 16#64 := rfl
    rw [h16, memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun k2 => ?_
    refine Entails.sepExists_elim fun k1 => ?_
    refine Entails.sepExists_right noneCap (Entails.sepExists_right k1 (Entails.sepExists_right k2 ?_))
    have hpull :
        ((a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ k1) ∗ ((a + 16#64) ↦₆₄ k2) ∗ ⌜noneCap = noneCap⌝) =
        (⌜noneCap = noneCap⌝ ∗ ((a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ k1) ∗ ((a + 16#64) ↦₆₄ k2))) := by
      ac_rfl
    rw [hpull]
    exact Entails.pure_right rfl (Entails.refl _)
  | some k =>
    simp only [spqrSendKeyAt, optKeyBuf, vecU8]
    refine Entails.sepExists_elim fun k0 => ?_
    refine Entails.sepExists_elim fun k1 => ?_
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    refine Entails.sepExists_right k0 (Entails.sepExists_right k1
      (Entails.sepExists_right (BitVec.ofNat 64 k.toList.length) ?_))
    have hpull :
        ((a ↦₆₄ k0) ∗ ((a + 8#64) ↦₆₄ k1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.toList.length) ∗
          (⌜BitVec.ofNat 64 k.toList.length = BitVec.ofNat 64 k.toList.length⌝ ∗
            vecU8Buf A k0 k1 k.toList)) =
        (⌜BitVec.ofNat 64 k.toList.length = BitVec.ofNat 64 k.toList.length⌝ ∗
          (((a ↦₆₄ k0) ∗ ((a + 8#64) ↦₆₄ k1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.toList.length)) ∗
            vecU8Buf A k0 k1 k.toList)) := by
      ac_rfl
    rw [hpull]
    exact Entails.pure_right rfl (Entails.refl _)

theorem optKeyAt_pack (A : RustAlloc) (b k0 k1 k2 : BitVec 64) (pqrKey : HKDF.Salt) :
    ((b ↦₆₄ k0) ∗ ((b + 8#64) ↦₆₄ k1) ∗ ((b + 16#64) ↦₆₄ k2) ∗ optKeyBuf A k0 k1 k2 pqrKey) ⊢
      spqrSendKeyAt A b pqrKey := by
  cases pqrKey with
  | none =>
    simp only [spqrSendKeyAt, optKeyBuf]
    have hpull :
        ((b ↦₆₄ k0) ∗ ((b + 8#64) ↦₆₄ k1) ∗ ((b + 16#64) ↦₆₄ k2) ∗ ⌜k0 = noneCap⌝) =
        (⌜k0 = noneCap⌝ ∗ ((b ↦₆₄ k0) ∗ ((b + 8#64) ↦₆₄ k1) ∗ ((b + 16#64) ↦₆₄ k2))) := by
      ac_rfl
    rw [hpull]
    refine Entails.pure_left fun hk0 => ?_
    subst hk0
    rw [mr_cut_add b 8 8 8 (by decide)]
    have h16 : b + BitVec.ofNat 64 (8 + 8) = b + 16#64 := rfl
    rw [h16]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))
  | some k =>
    simp only [spqrSendKeyAt, optKeyBuf, vecU8]
    have hpull :
        ((b ↦₆₄ k0) ∗ ((b + 8#64) ↦₆₄ k1) ∗ ((b + 16#64) ↦₆₄ k2) ∗
          (⌜k2 = BitVec.ofNat 64 k.toList.length⌝ ∗ vecU8Buf A k0 k1 k.toList)) =
        (⌜k2 = BitVec.ofNat 64 k.toList.length⌝ ∗
          (((b ↦₆₄ k0) ∗ ((b + 8#64) ↦₆₄ k1) ∗ ((b + 16#64) ↦₆₄ k2)) ∗
            vecU8Buf A k0 k1 k.toList)) := by
      ac_rfl
    rw [hpull]
    refine Entails.pure_left fun hk2 => ?_
    subst hk2
    refine Entails.sepExists_right k0 (Entails.sepExists_right k1 ?_)
    rw [vecU8At_eq_header_sep_buf]
    exact Entails.refl _

theorem optKeyAt_entails_optKeyRecvAt (A : RustAlloc) (b : BitVec 64) (pqrKey : HKDF.Salt) :
    spqrSendKeyAt A b pqrKey ⊢ spqrRecvKeyAt A b pqrKey := by
  cases pqrKey with
  | none =>
    dsimp only [spqrSendKeyAt, spqrRecvKeyAt]
    exact Entails.sepExists_right true (Entails.refl _)
  | some _ => exact Entails.refl _

theorem leBytes_4_toNat (v : BitVec 32) :
    leBytes 4 v.toNat = unpack32 v := by
  unfold leBytes unpack32
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  rw [hr]
  simp only [List.map, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']; try omega)

theorem chainKeyBytes_split (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  rw [pointsToBytes_append, length_keyToBytes32, leBytes_4_toNat, ← pointsTo32_eq_pointsToBytes]

def boxU8Buf (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
    (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))

theorem boxU8At_eq_header_sep_buf (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A a ptr bs =
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ boxU8Buf A ptr bs := by
  unfold boxU8At boxU8Buf
  ac_rfl

def optBoxU8Buf (A : RustAlloc) (ptr w0 w1 : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => ⌜w0 = 0#64⌝
  | some bs => ⌜w0 = ptr ∧ w1 = BitVec.ofNat 64 bs.length⌝ ∗ boxU8Buf A ptr bs

theorem optBoxU8At_unpack (A : RustAlloc) (a ptr : BitVec 64) (opt : Option (List (BitVec 8))) :
    optBoxU8At A a ptr opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ optBoxU8Buf A ptr w0 w1 opt := by
  cases opt with
  | none =>
    simp only [optBoxU8At, optBoxU8Buf, memRegion_eight]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w1 => ?_
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right w1 ?_)
    have hpull :
        ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ⌜(0#64 : BitVec 64) = 0#64⌝) =
        (⌜(0#64 : BitVec 64) = 0#64⌝ ∗ ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ w1))) := by
      ac_rfl
    rw [hpull]
    exact Entails.pure_right rfl (Entails.refl _)
  | some bs =>
    simp only [optBoxU8At, optBoxU8Buf, boxU8At_eq_header_sep_buf]
    refine Entails.sepExists_right ptr (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_)
    have hpull :
        ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (⌜ptr = ptr ∧ BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length⌝ ∗
            boxU8Buf A ptr bs)) =
        (⌜ptr = ptr ∧ BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length⌝ ∗
          ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ boxU8Buf A ptr bs)) := by
      ac_rfl
    rw [hpull]
    exact Entails.pure_right ⟨rfl, rfl⟩ (Entails.refl _)

theorem optBoxU8At_pack (A : RustAlloc) (b ptr w0 w1 : BitVec 64) (opt : Option (List (BitVec 8))) :
    ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ optBoxU8Buf A ptr w0 w1 opt) ⊢
      optBoxU8At A b ptr opt := by
  cases opt with
  | none =>
    simp only [optBoxU8At, optBoxU8Buf]
    have hpull :
        ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ ⌜w0 = 0#64⌝) =
        (⌜w0 = 0#64⌝ ∗ ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1))) := by
      ac_rfl
    rw [hpull]
    refine Entails.pure_left fun hw0 => ?_
    subst hw0
    exact sepConj_mono_right (pointsTo64_entails_memRegion _ _)
  | some bs =>
    simp only [optBoxU8At, optBoxU8Buf, boxU8At_eq_header_sep_buf]
    have hpull :
        ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗
          (⌜w0 = ptr ∧ w1 = BitVec.ofNat 64 bs.length⌝ ∗ boxU8Buf A ptr bs)) =
        (⌜w0 = ptr ∧ w1 = BitVec.ofNat 64 bs.length⌝ ∗
          ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ boxU8Buf A ptr bs)) := by
      ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hw0, hw1⟩ => ?_
    subst hw0 hw1
    exact Entails.refl _

def versionPadProp (v : BitVec 8) (w : BitVec 64) : Prop :=
  ∃ pad : List (BitVec 8), pad.length = 7 ∧ (v :: pad) = unpack64 w

theorem versionPad_unpack (a : BitVec 64) (v : BitVec 8) :
    ((a ↦₈ v) ∗ memRegion (a + 1#64) 7) ⊢
      ∃∗ w : BitVec 64, ⌜versionPadProp v w⌝ ∗ (a ↦₆₄ w) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide), sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pad => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hpad => ?_
  have hlen : (v :: pad).length = 8 := by simp [hpad]
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 hlen
  refine Entails.sepExists_right w ?_
  refine Entails.pure_right ⟨pad, hpad, hw⟩ ?_
  rw [← pointsToBytes_cons, hw, ← pointsTo64_eq_pointsToBytes]
  exact Entails.refl _

theorem versionPad_pack (b : BitVec 64) (v : BitVec 8) (w : BitVec 64) :
    (⌜versionPadProp v w⌝ ∗ (b ↦₆₄ w)) ⊢
      ((b ↦₈ v) ∗ memRegion (b + 1#64) 7) := by
  refine Entails.pure_left fun ⟨pad, hpad, hw⟩ => ?_
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons]
  apply sepConj_mono_right
  have h := pointsToBytes_entails_memRegion (b + 1#64) pad
  rwa [hpad] at h

def bytes32WordsProp (bs : List (BitVec 8)) (w0 w1 w2 w3 : BitVec 64) : Prop :=
  bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3

theorem bytes32_unpack (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    (a ↦ₛ bs) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜bytes32WordsProp bs w0 w1 w2 w3⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  obtain ⟨w0, w1, w2, w3, hbs, heq⟩ := exists_unpack64_of_length_32 h
  rw [heq a]
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_)))
  exact Entails.pure_right hbs (Entails.refl _)

theorem bytes32_pack (b : BitVec 64) (bs : List (BitVec 8)) (w0 w1 w2 w3 : BitVec 64) :
    (⌜bytes32WordsProp bs w0 w1 w2 w3⌝ ∗
      (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ ((b + 16#64) ↦₆₄ w2) ∗ ((b + 24#64) ↦₆₄ w3)) ⊢
      (b ↦ₛ bs) := by
  refine Entails.pure_left fun hbs => ?_
  rw [hbs, List.append_assoc, List.append_assoc,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

def signalMessageWordsAt (g : SignalMessageGhost) (m : SignalMessage) (a : BitVec 64)
    (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) : SepProp :=
  (a ↦₆₄ g.pqCap) ∗
    ((a + 8#64) ↦₆₄ g.pqPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
    ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
    ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
    ((a + 56#64) ↦₆₄ m7) ∗ ((a + 64#64) ↦₆₄ m8) ∗
    ((a + 72#64) ↦₆₄ m9) ∗ ((a + 80#64) ↦₆₄ m10) ∗
    ((a + 88#64) ↦₆₄ m11) ∗ ((a + 96#64) ↦₆₄ m12) ∗
    ((a + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) ∗
    ((a + 112#64) ↦₆₄ m14)

def signalMessageHeap (A : RustAlloc) (g : SignalMessageGhost) (m : SignalMessage)
    (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40) ∧
    bytes32WordsProp m.senderRatchetKey.bytes.toList m7 m8 m9 m10 ∧
    versionPadProp m.messageVersion m14⌝ ∗
    vecU8Buf A g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8Buf A g.ctPtr m.ciphertext ∗
    boxU8Buf A g.serPtr m.serialized ∗
    optBoxU8Buf A g.addrPtr m11 m12 m.addresses

theorem vecU8Buf_pqCap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun ⟨hlen, hlt, hptr⟩ => ?_
  exact Entails.pure_right hlt (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

theorem signalMessageAt_unpack (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m ⊢
      ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗
      ∃∗ m7 : BitVec 64, ∃∗ m8 : BitVec 64, ∃∗ m9 : BitVec 64, ∃∗ m10 : BitVec 64,
      ∃∗ m11 : BitVec 64, ∃∗ m12 : BitVec 64, ∃∗ m14 : BitVec 64,
        signalMessageWordsAt g m a m7 m8 m9 m10 m11 m12 m14 ∗
        signalMessageHeap A g m m7 m8 m9 m10 m11 m12 m14 := by
  unfold signalMessageAt
  rw [vecU8At_eq_header_sep_buf, boxU8At_eq_header_sep_buf, boxU8At_eq_header_sep_buf]
  unfold vecHeader
  have h68 :
      (((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter)) =
      ((a + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) := by
    have := pointsTo32_pair (a + 104#64) m.counter m.previousCounter
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using this
  have h70 :
      (((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7) ⊢
      ∃∗ m14 : BitVec 64, ⌜versionPadProp m.messageVersion m14⌝ ∗ ((a + 112#64) ↦₆₄ m14) := by
    have := versionPad_unpack (a + 112#64) m.messageVersion
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using this
  have h38 :
      ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ⊢
      ∃∗ m7 : BitVec 64, ∃∗ m8 : BitVec 64, ∃∗ m9 : BitVec 64, ∃∗ m10 : BitVec 64,
        ⌜bytes32WordsProp m.senderRatchetKey.bytes.toList m7 m8 m9 m10⌝ ∗
        ((a + 56#64) ↦₆₄ m7) ∗ ((a + 64#64) ↦₆₄ m8) ∗
        ((a + 72#64) ↦₆₄ m9) ∗ ((a + 80#64) ↦₆₄ m10) := by
    have := bytes32_unpack (a + 56#64) (bs := m.senderRatchetKey.bytes.toList)
      (List.Vector.toList_length _)
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using this
  have h58 :
      optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ⊢
      ∃∗ m11 : BitVec 64, ∃∗ m12 : BitVec 64,
        ((a + 88#64) ↦₆₄ m11) ∗ ((a + 96#64) ↦₆₄ m12) ∗
        optBoxU8Buf A g.addrPtr m11 m12 m.addresses := by
    have := optBoxU8At_unpack A (a + 88#64) g.addrPtr m.addresses
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using this
  have h68_70 :
      (((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
        ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7) ⊢
      ((a + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) ∗
        (∃∗ m14 : BitVec 64, ⌜versionPadProp m.messageVersion m14⌝ ∗ ((a + 112#64) ↦₆₄ m14)) := by
    rw [← sepConj_assoc ((a + 0x68#64) ↦₃₂ m.counter), h68]
    exact sepConj_mono_right h70
  refine Entails.pure_left fun hbnds => ?_
  refine Entails.trans (sepConj_mono (sepConj_mono_right (vecU8Buf_pqCap_lt A g.pqCap g.pqPtr m.pqRatchet))
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono h38 (sepConj_mono h58 h68_70))))) ?_
  simp (config := { maxSteps := 200000 }) only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_elim fun m14 => ?_
  refine Entails.sepExists_elim fun m11 => ?_
  refine Entails.sepExists_elim fun m12 => ?_
  refine Entails.sepExists_elim fun m7 => ?_
  refine Entails.sepExists_elim fun m8 => ?_
  refine Entails.sepExists_elim fun m9 => ?_
  refine Entails.sepExists_elim fun m10 => ?_
  have hpull1 :
      (((a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length)) ∗
        (⌜g.pqCap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A g.pqCap g.pqPtr m.pqRatchet)) =
      (⌜g.pqCap.toNat < 2 ^ 63⌝ ∗
        ((a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
          vecU8Buf A g.pqCap g.pqPtr m.pqRatchet)) := by
    ac_rfl
  rw [hpull1, sepConj_assoc]
  refine Entails.pure_left fun hpqCap => ?_
  refine Entails.sepExists_right m7 (Entails.sepExists_right m8
    (Entails.sepExists_right m9 (Entails.sepExists_right m10
      (Entails.sepExists_right m11 (Entails.sepExists_right m12
        (Entails.sepExists_right m14 ?_))))))
  refine Entails.pure_right hpqCap ?_
  unfold signalMessageWordsAt signalMessageHeap
  have hpull2 :
      (((a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
          vecU8Buf A g.pqCap g.pqPtr m.pqRatchet) ∗
        (((a + 24#64) ↦₆₄ g.ctPtr) ∗
          ((a + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          boxU8Buf A g.ctPtr m.ciphertext) ∗
        (((a + 40#64) ↦₆₄ g.serPtr) ∗
          ((a + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          boxU8Buf A g.serPtr m.serialized) ∗
        (⌜bytes32WordsProp m.senderRatchetKey.bytes.toList m7 m8 m9 m10⌝ ∗
          ((a + 56#64) ↦₆₄ m7) ∗ ((a + 64#64) ↦₆₄ m8) ∗
          ((a + 72#64) ↦₆₄ m9) ∗ ((a + 80#64) ↦₆₄ m10)) ∗
        (((a + 88#64) ↦₆₄ m11) ∗ ((a + 96#64) ↦₆₄ m12) ∗
          optBoxU8Buf A g.addrPtr m11 m12 m.addresses) ∗
        ((a + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) ∗
        (⌜versionPadProp m.messageVersion m14⌝ ∗ ((a + 112#64) ↦₆₄ m14))) =
      (⌜bytes32WordsProp m.senderRatchetKey.bytes.toList m7 m8 m9 m10⌝ ∗
        ⌜versionPadProp m.messageVersion m14⌝ ∗
        (((a ↦₆₄ g.pqCap) ∗
          ((a + 8#64) ↦₆₄ g.pqPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
          ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          ((a + 56#64) ↦₆₄ m7) ∗ ((a + 64#64) ↦₆₄ m8) ∗
          ((a + 72#64) ↦₆₄ m9) ∗ ((a + 80#64) ↦₆₄ m10) ∗
          ((a + 88#64) ↦₆₄ m11) ∗ ((a + 96#64) ↦₆₄ m12) ∗
          ((a + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) ∗
          ((a + 112#64) ↦₆₄ m14)) ∗
        (vecU8Buf A g.pqCap g.pqPtr m.pqRatchet ∗
          boxU8Buf A g.ctPtr m.ciphertext ∗
          boxU8Buf A g.serPtr m.serialized ∗
          optBoxU8Buf A g.addrPtr m11 m12 m.addresses))) := by
    ac_rfl
  rw [hpull2]
  refine Entails.pure_left fun hsrk => ?_
  refine Entails.pure_left fun hvp => ?_
  apply sepConj_mono_right
  exact Entails.pure_right ⟨hbnds.1, hbnds.2.1, hbnds.2.2.1, hbnds.2.2.2.1, hbnds.2.2.2.2,
    hsrk, hvp⟩ (Entails.refl _)

theorem signalMessageAt_pack (A : RustAlloc) (g : SignalMessageGhost) (b : BitVec 64)
    (m : SignalMessage) (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    (signalMessageWordsAt g m b m7 m8 m9 m10 m11 m12 m14 ∗
      signalMessageHeap A g m m7 m8 m9 m10 m11 m12 m14) ⊢
      signalMessageAt A g b m := by
  unfold signalMessageWordsAt signalMessageHeap signalMessageAt
  rw [vecU8At_eq_header_sep_buf, boxU8At_eq_header_sep_buf, boxU8At_eq_header_sep_buf]
  unfold vecHeader
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hb1, hb2, hb3, hb4, hb5, hsrk, hvp⟩ => ?_
  refine Entails.pure_right ⟨hb1, hb2, hb3, hb4, hb5⟩ ?_
  have h68 :
      ((b + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) =
      (((b + 0x68#64) ↦₃₂ m.counter) ∗ ((b + 0x6c#64) ↦₃₂ m.previousCounter)) := by
    have := (pointsTo32_pair (b + 104#64) m.counter m.previousCounter).symm
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using this
  have h70 :
      ((b + 112#64) ↦₆₄ m14) ⊢
      (((b + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (b + 0x71#64) 7) := by
    have := Entails.trans (Entails.pure_right hvp (Entails.refl _))
      (versionPad_pack (b + 112#64) m.messageVersion m14)
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using this
  have h38 :
      (((b + 56#64) ↦₆₄ m7) ∗ ((b + 64#64) ↦₆₄ m8) ∗
        ((b + 72#64) ↦₆₄ m9) ∗ ((b + 80#64) ↦₆₄ m10)) ⊢
      ((b + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) := by
    have := Entails.trans (Entails.pure_right hsrk (Entails.refl _))
      (bytes32_pack (b + 56#64) m.senderRatchetKey.bytes.toList m7 m8 m9 m10)
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using this
  have h58 :
      (((b + 88#64) ↦₆₄ m11) ∗ ((b + 96#64) ↦₆₄ m12) ∗
        optBoxU8Buf A g.addrPtr m11 m12 m.addresses) ⊢
      optBoxU8At A (b + 0x58#64) g.addrPtr m.addresses := by
    have := optBoxU8At_pack A (b + 88#64) g.addrPtr m11 m12 m.addresses
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using this
  have hpull :
      (((b ↦₆₄ g.pqCap) ∗
        ((b + 8#64) ↦₆₄ g.pqPtr) ∗ ((b + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
        ((b + 24#64) ↦₆₄ g.ctPtr) ∗ ((b + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
        ((b + 40#64) ↦₆₄ g.serPtr) ∗ ((b + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
        ((b + 56#64) ↦₆₄ m7) ∗ ((b + 64#64) ↦₆₄ m8) ∗
        ((b + 72#64) ↦₆₄ m9) ∗ ((b + 80#64) ↦₆₄ m10) ∗
        ((b + 88#64) ↦₆₄ m11) ∗ ((b + 96#64) ↦₆₄ m12) ∗
        ((b + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) ∗
        ((b + 112#64) ↦₆₄ m14)) ∗
      (vecU8Buf A g.pqCap g.pqPtr m.pqRatchet ∗
        boxU8Buf A g.ctPtr m.ciphertext ∗
        boxU8Buf A g.serPtr m.serialized ∗
        optBoxU8Buf A g.addrPtr m11 m12 m.addresses)) =
      ((((b ↦₆₄ g.pqCap) ∗ ((b + 8#64) ↦₆₄ g.pqPtr) ∗
          ((b + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length)) ∗
          vecU8Buf A g.pqCap g.pqPtr m.pqRatchet) ∗
        (((b + 24#64) ↦₆₄ g.ctPtr) ∗
          ((b + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          boxU8Buf A g.ctPtr m.ciphertext) ∗
        (((b + 40#64) ↦₆₄ g.serPtr) ∗
          ((b + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          boxU8Buf A g.serPtr m.serialized) ∗
        (((b + 56#64) ↦₆₄ m7) ∗ ((b + 64#64) ↦₆₄ m8) ∗
          ((b + 72#64) ↦₆₄ m9) ∗ ((b + 80#64) ↦₆₄ m10)) ∗
        (((b + 88#64) ↦₆₄ m11) ∗ ((b + 96#64) ↦₆₄ m12) ∗
          optBoxU8Buf A g.addrPtr m11 m12 m.addresses) ∗
        ((b + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) ∗
        ((b + 112#64) ↦₆₄ m14)) := by
    ac_rfl
  rw [hpull]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _) (sepConj_mono h38 (sepConj_mono h58
      (by rw [h68, sepConj_assoc]; exact sepConj_mono_right (sepConj_mono_right h70))))))

/-- Detached allocation + spare capacity of a `Vec<u8>` when its `(ptr ↦ₛ bs)` slice is borrowed. -/
def vecU8Spare (A : RustAlloc) (cap ptr : BitVec 64) (len : Nat) : SepProp :=
  ⌜len ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 len) (cap.toNat - len))

theorem vecU8Buf_expose_slice (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (ptr ↦ₛ bs) ∗ vecU8Spare A cap ptr bs.length := by
  unfold vecU8Buf vecU8Spare
  refine Entails.pure_left fun ⟨hlen, hlt, hptr⟩ => ?_
  refine Entails.pure_right ⟨hlen, hlt, hptr⟩ ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj, List.length_nil]
    exact Entails.pure_right ⟨Nat.zero_le _, hlt, hptr⟩ (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    have hpull :
        ((ptr ↦ₛ bs) ∗
          (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            (A.live ptr cap.toNat 1 ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))) =
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
      ac_rfl
    rw [hpull]
    exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

theorem vecU8Spare_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((ptr ↦ₛ bs) ∗ vecU8Spare A cap ptr bs.length) ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8Spare
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hlen, hlt, hptr⟩ => ?_
  refine Entails.pure_right ⟨hlen, hlt, hptr⟩ ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    have hpull :
        ((ptr ↦ₛ bs) ∗
          (A.live ptr cap.toNat 1 ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
        (A.live ptr cap.toNat 1 ∗
          ((ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_right
    have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    conv => rhs; rw [hsplit, memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)


theorem chainKeyBytes_unpack (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜bytes32WordsProp (keyToBytes32 ck.key) w0 w1 w2 w3⌝ ∗
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
          ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  rw [chainKeyBytes_split]
  have h32 := bytes32_unpack a (length_keyToBytes32 ck.key)
  refine Entails.trans (sepConj_mono_left h32) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
    Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 => ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_)))
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem chainKeyBytes_pack (b : BitVec 64) (ck : ChainKey) (w0 w1 w2 w3 : BitVec 64) :
    (⌜bytes32WordsProp (keyToBytes32 ck.key) w0 w1 w2 w3⌝ ∗
      (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ ((b + 16#64) ↦₆₄ w2) ∗
      ((b + 24#64) ↦₆₄ w3) ∗ ((b + 32#64) ↦₃₂ ck.index)) ⊢
    (b ↦ₛ chainKeyBytes ck) := by
  rw [chainKeyBytes_split]
  have hpull :
      (⌜bytes32WordsProp (keyToBytes32 ck.key) w0 w1 w2 w3⌝ ∗
        (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ ((b + 16#64) ↦₆₄ w2) ∗
        ((b + 24#64) ↦₆₄ w3) ∗ ((b + 32#64) ↦₃₂ ck.index)) =
      ((⌜bytes32WordsProp (keyToBytes32 ck.key) w0 w1 w2 w3⌝ ∗
        (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ ((b + 16#64) ↦₆₄ w2) ∗
        ((b + 24#64) ↦₆₄ w3)) ∗ ((b + 32#64) ↦₃₂ ck.index)) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_left (bytes32_pack b (keyToBytes32 ck.key) w0 w1 w2 w3)

theorem messageKeysAt_entails_memRegion (r : BitVec 64) (mk : MessageKeys) :
    messageKeysAt r mk ⊢ memRegion r 84 := by
  unfold messageKeysAt
  have h0 : (r ↦ₛ keyToBytes32 mk.cipherKey) ⊢ memRegion r 32 := by
    have h := pointsToBytes_entails_memRegion r (keyToBytes32 mk.cipherKey)
    rwa [length_keyToBytes32] at h
  have h1 : ((r + 0x20#64) ↦ₛ keyToBytes32 mk.macKey) ⊢ memRegion (r + 32#64) 32 := by
    have h := pointsToBytes_entails_memRegion (r + 0x20#64) (keyToBytes32 mk.macKey)
    rwa [length_keyToBytes32] at h
  have h2 : ((r + 0x40#64) ↦ₛ CBC.blockToBytesLE mk.iv) ⊢ memRegion (r + 64#64) 16 := by
    have h := pointsToBytes_entails_memRegion (r + 0x40#64) (CBC.blockToBytesLE mk.iv)
    rwa [blockToBytesLE_length] at h
  have h3 : ((r + 0x50#64) ↦₃₂ mk.counter) ⊢ memRegion (r + 80#64) 4 :=
    pointsTo32_entails_memRegion (r + 80#64) mk.counter
  refine Entails.trans (sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 h3))) ?_
  have hrhs : memRegion r 84 =
      memRegion r 32 ∗ memRegion (r + 32#64) 32 ∗
        memRegion (r + 64#64) 16 ∗ memRegion (r + 80#64) 4 := by
    rw [memRegion_split r 32 52 (by decide), mr_cut_add r 32 32 20 (by decide),
      mr_cut_add r 64 16 4 (by decide)]
  rw [hrhs]
  exact Entails.refl _

/-! ## Relocatable `[LibsignalPlacement]` Specifications (`otrEncryptPlacedSpec`) -/

/-- Relocatable `[LibsignalPlacement]` specification of `OTR::encrypt` (Blocks `125` and `544`)
with arbitrary spatial frame `F`. -/
def otrEncryptPlacedSpecF [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (F : SepProp) : Spec OtrEncryptGhost where
  pre := fun x s =>
    F ∗
      (⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.o ∧ s.readReg64 .x2 = x.ptA ∧
        (s.readReg64 .x3).toNat = x.ptext.length ∧ x.ptext.length < 2 ^ 32 ∧
        s.readReg64 .x4 = (if x.loc.isSome then x.locA else 0#64) ∧
        (x.loc.isSome → x.locA ≠ 0#64) ∧ s.readReg64 .x5 = x.remA⌝ ∗
       otrAt A x.o x.pqCap x.pqPtr x.ot ∗ (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗
       protocolAddressAt A x.rem x.remA ∗ memRegion x.ret 120 ∗ tapeAt ctl x.cur x.rest ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp rootStack ∗ A.pool)
  post := fun x s0 sf =>
    F ∗
      (⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
       (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
         otrAt A x.o pqCap' pqPtr' (x.model C S uuidParse).2) ∗
       signalMessageResultAt A (utf8 "encrypt") x.ret (x.model C S uuidParse).1 ∗
       (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗
       tapeAfter ctl x.cur x.rest (S.draws x.ot.pqrState x.rest) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp rootStack ∗ A.pool)
  onPanic := fun x s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest ∨
        allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- Relocatable `[LibsignalPlacement]` specification of `OTR::encrypt` (Blocks `125` and `544`). -/
def otrEncryptPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec OtrEncryptGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.o ∧ s.readReg64 .x2 = x.ptA ∧
      (s.readReg64 .x3).toNat = x.ptext.length ∧ x.ptext.length < 2 ^ 32 ∧
      s.readReg64 .x4 = (if x.loc.isSome then x.locA else 0#64) ∧
      (x.loc.isSome → x.locA ≠ 0#64) ∧ s.readReg64 .x5 = x.remA⌝ ∗
    otrAt A x.o x.pqCap x.pqPtr x.ot ∗ (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗
    protocolAddressAt A x.rem x.remA ∗ memRegion x.ret 120 ∗ tapeAt ctl x.cur x.rest ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp rootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
    (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
      otrAt A x.o pqCap' pqPtr' (x.model C S uuidParse).2) ∗
    signalMessageResultAt A (utf8 "encrypt") x.ret (x.model C S uuidParse).1 ∗
    (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗
    tapeAfter ctl x.cur x.rest (S.draws x.ot.pqrState x.rest) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp rootStack ∗ A.pool
  onPanic := fun x s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest ∨
        allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap

theorem otrEncrypt_placed_ok_of_frame [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpecF C A ctl uuidParse S emp))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpec C A ctl uuidParse S)) := by
  refine subroutine_ok_mono h ?_ ?_
  · intro x R s0 hm
    simpa only [withLsCodeRoLoaded, otrEncryptPlacedSpecF, otrEncryptPlacedSpec, emp_sepConj] using hm
  · intro x R s0 sf hm
    simpa only [withLsCodeRoLoaded, otrEncryptPlacedSpecF, otrEncryptPlacedSpec, emp_sepConj] using hm

end CryptoVerification.LibsignalTripleRatchet.Encrypt
