/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon

/-!
# Entailment from `apiEncResultAt` to `apiEncResultAtLoose`

Proves `LibsignalPublicApiRepr.apiEncResultAt A ret res ⊢ apiEncResultAtLoose A ret res`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

section ApiEncResultEntailsLoose

private theorem absorb_anyHeap_right {P Q : SepProp} (h : P ⊢ Q ∗ anyHeap) :
    P ∗ anyHeap ⊢ Q ∗ anyHeap := by
  refine Entails.trans (sepConj_mono_left h) ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

private theorem memRegion_anyHeap_join {P Q : SepProp} {a b : BitVec 64} {n k N : Nat}
    (hP : P ⊢ memRegion a n ∗ anyHeap) (hQ : Q ⊢ memRegion b k ∗ anyHeap)
    (hN : n + k = N) (hb : b = a + BitVec.ofNat 64 n) (hle : N ≤ 2 ^ 64) :
    P ∗ Q ⊢ memRegion a N ∗ anyHeap := by
  refine Entails.trans (sepConj_mono hP hQ) ?_
  have h1 : (memRegion a n ∗ anyHeap) ∗ (memRegion b k ∗ anyHeap) =
      (memRegion a n ∗ memRegion b k) ∗ (anyHeap ∗ anyHeap) := by ac_rfl
  rw [h1, ← memRegion_split' (b := a) (b' := b) (N := N) (n := n) (k := k) hN.symm hb hle]
  exact sepConj_mono_right (entails_anyHeap _)

private theorem memRegion_to_memRegion_anyHeap (a : BitVec 64) (n : Nat) :
    memRegion a n ⊢ memRegion a n ∗ anyHeap := by
  have h : memRegion a n = memRegion a n ∗ emp := (sepConj_emp (memRegion a n)).symm
  exact Entails.trans (by rw [← h]; exact Entails.refl _) (sepConj_mono_right (entails_anyHeap emp))

private theorem pointsTo64_to_memRegion_anyHeap (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 ∗ anyHeap := by
  refine Entails.trans ?_ (memRegion_to_memRegion_anyHeap a 8)
  rw [ProofLib.memRegion_eight a]
  exact Entails.sepExists_right v (Entails.refl _)

private theorem pointsTo32_to_memRegion_anyHeap (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 ∗ anyHeap := by
  refine Entails.trans ?_ (memRegion_to_memRegion_anyHeap a 4)
  rw [pointsTo32_eq_pointsToBytes, memRegion_eq_exists_bytes a 4 (by decide)]
  exact Entails.sepExists_right (unpack32 v) (Entails.pure_right (unpack32_length v) (Entails.refl _))

private theorem pointsTo8_to_memRegion_anyHeap (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ v) ⊢ memRegion a 1 ∗ anyHeap :=
  Entails.trans (pointsTo8_entails_memRegion a v) (memRegion_to_memRegion_anyHeap a 1)

private theorem pointsToBytes_to_memRegion_anyHeap (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (h : bs.length = n) (hle : n ≤ 2 ^ 64) :
    (a ↦ₛ bs) ⊢ memRegion a n ∗ anyHeap := by
  refine Entails.trans ?_ (memRegion_to_memRegion_anyHeap a n)
  rw [memRegion_eq_exists_bytes a n hle]
  exact Entails.sepExists_right bs (Entails.pure_right h (Entails.refl _))

private theorem vecHeader_to_memRegion_anyHeap (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len ⊢ memRegion a 24 ∗ anyHeap := by
  unfold vecHeader
  refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a cap)
    (memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap (a + 8#64) ptr)
      (pointsTo64_to_memRegion_anyHeap (a + 16#64) len)
      rfl (by bv_lin) (by decide))
    rfl (by bv_lin) (by decide)

private theorem vecU8At_to_memRegion_anyHeap (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢ memRegion a 24 ∗ anyHeap := by
  unfold vecU8At
  refine Entails.trans (sepConj_mono_right (entails_anyHeap _)) ?_
  exact absorb_anyHeap_right (vecHeader_to_memRegion_anyHeap a cap ptr _)

private theorem vecU8_to_memRegion_anyHeap (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢ memRegion a 24 ∗ anyHeap := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact vecU8At_to_memRegion_anyHeap A a cap ptr bs

private theorem boxU8At_to_memRegion_anyHeap (A : RustAlloc) (a ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    boxU8At A a ptr bs ⊢ memRegion a 16 ∗ anyHeap := by
  unfold boxU8At
  have h1 :
      ((a ↦₆₄ ptr) ∗ ((a + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
        (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))) =
      (((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        (⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
          (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)))) := by
    ac_rfl
  rw [h1]
  refine Entails.trans (sepConj_mono_right (entails_anyHeap _)) ?_
  refine absorb_anyHeap_right ?_
  exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a ptr)
    (pointsTo64_to_memRegion_anyHeap (a + 8#64) _)
    rfl (by bv_lin) (by decide)

private theorem optBoxU8At_to_memRegion_anyHeap (A : RustAlloc) (a ptr : BitVec 64)
    (o : Option (List (BitVec 8))) :
    optBoxU8At A a ptr o ⊢ memRegion a 16 ∗ anyHeap := by
  cases o with
  | none =>
    dsimp only [optBoxU8At]
    exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a 0#64)
      (memRegion_to_memRegion_anyHeap (a + 8#64) 8)
      rfl (by bv_lin) (by decide)
  | some bs =>
    exact boxU8At_to_memRegion_anyHeap A a ptr bs

private theorem strRefAt_to_memRegion_anyHeap (a : BitVec 64) (lit : List (BitVec 8)) :
    strRefAt a lit ⊢ memRegion a 16 ∗ anyHeap := by
  unfold strRefAt
  apply Entails.sepExists_elim; intro p
  have h1 :
      ((a ↦₆₄ p) ∗ ((a + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 lit.length) ∗ (p ↦ᵣ lit)) =
      (((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 lit.length)) ∗ (p ↦ᵣ lit)) := by
    ac_rfl
  rw [h1]
  refine Entails.trans (sepConj_mono_right (entails_anyHeap _)) ?_
  refine absorb_anyHeap_right ?_
  exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a p)
    (pointsTo64_to_memRegion_anyHeap (a + 8#64) _)
    rfl (by bv_lin) (by decide)

private theorem addrCloneAt_to_memRegion_anyHeap (A : RustAlloc) (a : BitVec 64) (v : AddrVal) :
    LibsignalPublicApiRepr.addrCloneAt A a v ⊢ memRegion a 32 ∗ anyHeap := by
  unfold LibsignalPublicApiRepr.addrCloneAt
  refine memRegion_anyHeap_join (vecU8_to_memRegion_anyHeap A a v.name)
    (memRegion_anyHeap_join (pointsTo8_to_memRegion_anyHeap (a + 0x18#64) v.device)
      (memRegion_to_memRegion_anyHeap (a + 0x19#64) 7)
      rfl (by bv_lin) (by decide))
    rfl (by bv_lin) (by decide)

private theorem invalidMessageStrAt_to_memRegion_anyHeap (A : RustAlloc) (a : BitVec 64)
    (r : InvalidMessageReason) :
    invalidMessageStrAt A a r ⊢ memRegion a 24 ∗ anyHeap := by
  cases r with
  | tooFarInFuture => exact vecU8_to_memRegion_anyHeap A a tooFarInFutureStr
  | macFailed => exact vecU8_to_memRegion_anyHeap A a macFailedStr
  | pqRatchet =>
    dsimp only [invalidMessageStrAt]
    apply Entails.sepExists_elim; intro bs
    exact vecU8_to_memRegion_anyHeap A a bs
  | badCiphertext =>
    dsimp only [invalidMessageStrAt]
    apply Entails.sepExists_elim; intro bs
    exact vecU8_to_memRegion_anyHeap A a bs
  | decryptionFailed =>
    dsimp only [invalidMessageStrAt]
    apply Entails.pure_left_only; intro h; exact False.elim h

private theorem speAt_to_memRegion_anyHeap (A : RustAlloc) (fn : List (BitVec 8)) (a : BitVec 64)
    (e : SignalProtocolError) :
    speAt A fn a e ⊢ memRegion a 48 ∗ anyHeap := by
  cases e with
  | invalidState =>
    dsimp only [speAt]
    have hvec : (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ⊢ memRegion (a + 8#64) 24 ∗ anyHeap := by
      apply Entails.sepExists_elim; intro bs
      exact vecU8_to_memRegion_anyHeap A (a + 8#64) bs
    exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join hvec (strRefAt_to_memRegion_anyHeap (a + 0x20#64) fn)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | ciphertextMessageTooShort n =>
    dsimp only [speAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap (a + 8#64) _)
        (memRegion_to_memRegion_anyHeap (a + 16#64) 32)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | legacyCiphertextVersion v =>
    dsimp only [speAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (pointsTo8_to_memRegion_anyHeap (a + 8#64) v)
        (memRegion_to_memRegion_anyHeap (a + 9#64) 39)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | unrecognizedCiphertextVersion v =>
    dsimp only [speAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (pointsTo8_to_memRegion_anyHeap (a + 8#64) v)
        (memRegion_to_memRegion_anyHeap (a + 9#64) 39)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | invalidProtobufEncoding =>
    dsimp only [speAt]
    exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_to_memRegion_anyHeap (a + 8#64) 40)
      rfl (by bv_lin) (by decide)
  | noKeyTypeIdentifier =>
    dsimp only [speAt]
    exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_to_memRegion_anyHeap (a + 8#64) 40)
      rfl (by bv_lin) (by decide)
  | badKeyType t =>
    dsimp only [speAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (pointsTo8_to_memRegion_anyHeap (a + 8#64) t)
        (memRegion_to_memRegion_anyHeap (a + 9#64) 39)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | badKeyLength n =>
    dsimp only [speAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap (a + 8#64) _)
        (memRegion_to_memRegion_anyHeap (a + 16#64) 32)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | invalidKeyAgreement =>
    dsimp only [speAt]
    exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_to_memRegion_anyHeap (a + 8#64) 40)
      rfl (by bv_lin) (by decide)
  | invalidSessionStructure r =>
    dsimp only [speAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (strRefAt_to_memRegion_anyHeap (a + 8#64) (invalidSessionStructureStr r))
        (memRegion_to_memRegion_anyHeap (a + 24#64) 24)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | duplicatedMessage i c =>
    dsimp only [speAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap (a + 8#64) i)
        (memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap (a + 12#64) c)
          (memRegion_to_memRegion_anyHeap (a + 16#64) 32)
          rfl (by bv_lin) (by decide))
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | invalidMessage t r =>
    dsimp only [speAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (invalidMessageStrAt_to_memRegion_anyHeap A (a + 8#64) r)
        (memRegion_anyHeap_join (pointsTo8_to_memRegion_anyHeap (a + 0x20#64) (msgTypeByte t))
          (memRegion_to_memRegion_anyHeap (a + 33#64) 15)
          rfl (by bv_lin) (by decide))
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | panic =>
    dsimp only [speAt]
    apply Entails.pure_left_only; intro h; exact False.elim h

private theorem apiErrAt_to_memRegion_anyHeap (A : RustAlloc) (a : BitVec 64)
    (e : ApiError AddrVal Unit) :
    LibsignalPublicApiRepr.apiErrAt A a e ⊢ memRegion a 48 ∗ anyHeap := by
  cases e with
  | sessionNotFound addr op =>
    dsimp only [LibsignalPublicApiRepr.apiErrAt]
    exact memRegion_anyHeap_join (addrCloneAt_to_memRegion_anyHeap A a addr)
      (strRefAt_to_memRegion_anyHeap (a + 0x20#64) (utf8 op))
      rfl (by bv_lin) (by decide)
  | untrustedIdentity addr =>
    dsimp only [LibsignalPublicApiRepr.apiErrAt]
    refine memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (addrCloneAt_to_memRegion_anyHeap A (a + 8#64) addr)
        (memRegion_to_memRegion_anyHeap (a + 0x28#64) 8)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | store u =>
    cases u
    dsimp only [LibsignalPublicApiRepr.apiErrAt]
    have hd : (∃∗ d : BitVec 64, ⌜d ≠ 0⌝ ∗ ((a + 0x18#64) ↦₆₄ d)) ⊢ memRegion (a + 0x18#64) 8 ∗ anyHeap := by
      apply Entails.sepExists_elim; intro d
      apply Entails.pure_left; intro _
      exact pointsTo64_to_memRegion_anyHeap (a + 0x18#64) d
    have hvt : (∃∗ vt : BitVec 64, (a + 0x20#64) ↦₆₄ vt) ⊢ memRegion (a + 0x20#64) 8 ∗ anyHeap := by
      apply Entails.sepExists_elim; intro vt
      exact pointsTo64_to_memRegion_anyHeap (a + 0x20#64) vt
    exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a _)
      (memRegion_anyHeap_join (strRefAt_to_memRegion_anyHeap (a + 8#64) LibsignalPublicApiRepr.storeHookStr)
        (memRegion_anyHeap_join hd
          (memRegion_anyHeap_join hvt (memRegion_to_memRegion_anyHeap (a + 0x28#64) 8)
            rfl (by bv_lin) (by decide))
          rfl (by bv_lin) (by decide))
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  | protocol _ =>
    dsimp only [LibsignalPublicApiRepr.apiErrAt]
    apply Entails.pure_left_only; intro h; exact False.elim h
  | panic =>
    dsimp only [LibsignalPublicApiRepr.apiErrAt]
    apply Entails.pure_left_only; intro h; exact False.elim h

private theorem optU32At_to_memRegion_anyHeap (a : BitVec 64) (o : Option (BitVec 32)) :
    LibsignalPublicApiRepr.optU32At a o ⊢ memRegion a 8 ∗ anyHeap := by
  cases o with
  | none =>
    dsimp only [LibsignalPublicApiRepr.optU32At]
    exact memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap a 0#32)
      (memRegion_to_memRegion_anyHeap (a + 4#64) 4)
      rfl (by bv_lin) (by decide)
  | some v =>
    dsimp only [LibsignalPublicApiRepr.optU32At]
    exact memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap a 1#32)
      (pointsTo32_to_memRegion_anyHeap (a + 4#64) v)
      rfl (by bv_lin) (by decide)

private theorem optKyberAt_to_memRegion_anyHeap (A : RustAlloc) (a ptr : BitVec 64)
    (o : Option KyberPayload) :
    LibsignalPublicApiRepr.optKyberAt A a ptr o ⊢ memRegion a 24 ∗ anyHeap := by
  cases o with
  | none =>
    dsimp only [LibsignalPublicApiRepr.optKyberAt]
    exact memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap a 0#64)
      (memRegion_to_memRegion_anyHeap (a + 8#64) 16)
      rfl (by bv_lin) (by decide)
  | some k =>
    dsimp only [LibsignalPublicApiRepr.optKyberAt]
    exact memRegion_anyHeap_join (boxU8At_to_memRegion_anyHeap A a ptr k.ciphertext)
      (memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap (a + 0x10#64) k.preKeyId)
        (memRegion_to_memRegion_anyHeap (a + 0x14#64) 4)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)

private theorem signalMessage_tail64_to_memRegion_anyHeap (A : RustAlloc) (g : SignalMessageGhost)
    (a : BitVec 64) (m : SignalMessage) :
    ((a + asm64% smSenderRatchetKeyOff) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
      optBoxU8At A (a + asm64% smAddressesOff) g.addrPtr m.addresses ∗
      ((a + asm64% smCounterOff) ↦₃₂ m.counter) ∗
      ((a + asm64% smPreviousCounterOff) ↦₃₂ m.previousCounter) ∗
      ((a + asm64% smMessageVersionOff) ↦₈ m.messageVersion) ∗
      memRegion (a + asm64% (smMessageVersionOff + 1))
        (asm% (signalMessageSize - (smMessageVersionOff + 1))) ⊢
      memRegion (a + 0x38#64) 64 ∗ anyHeap := by
  refine memRegion_anyHeap_join
    (pointsToBytes_to_memRegion_anyHeap (a + 0x38#64) m.senderRatchetKey.bytes.toList 32
      (List.Vector.toList_length _) (by decide))
    (memRegion_anyHeap_join (optBoxU8At_to_memRegion_anyHeap A (a + 0x58#64) g.addrPtr m.addresses)
      (memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap (a + 0x68#64) m.counter)
        (memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap (a + 0x6c#64) m.previousCounter)
          (memRegion_anyHeap_join (pointsTo8_to_memRegion_anyHeap (a + 0x70#64) m.messageVersion)
            (memRegion_to_memRegion_anyHeap (a + 0x71#64) 7)
            rfl (by bv_lin) (by decide))
          rfl (by bv_lin) (by decide))
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide))
    rfl (by bv_lin) (by decide)

private theorem preKeyMsg_tail128_to_memRegion_anyHeap (A : RustAlloc)
    (g : LibsignalPublicApiRepr.PreKeyMsgGhost) (a : BitVec 64) (m : PreKeySignalMessage) :
    LibsignalPublicApiRepr.optU32At (a + 0x78#64) m.preKeyId ∗
      boxU8At A (a + 0x80#64) g.serPtr m.serialized ∗
      LibsignalPublicApiRepr.optKyberAt A (a + 0x90#64) g.kyberPtr m.kyberPayload ∗
      ((a + 0xa8#64) ↦ₛ m.baseKey.bytes.toList) ∗
      ((a + 0xc8#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
      ((a + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((a + 0xec#64) ↦₃₂ m.signedPreKeyId) ∗
      ((a + 0xf0#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0xf1#64) 7 ⊢
      memRegion (a + 0x78#64) 128 ∗ anyHeap := by
  refine memRegion_anyHeap_join (optU32At_to_memRegion_anyHeap (a + 0x78#64) m.preKeyId)
    (memRegion_anyHeap_join (boxU8At_to_memRegion_anyHeap A (a + 0x80#64) g.serPtr m.serialized)
      (memRegion_anyHeap_join (optKyberAt_to_memRegion_anyHeap A (a + 0x90#64) g.kyberPtr m.kyberPayload)
        (memRegion_anyHeap_join
          (pointsToBytes_to_memRegion_anyHeap (a + 0xa8#64) m.baseKey.bytes.toList 32
            (List.Vector.toList_length _) (by decide))
          (memRegion_anyHeap_join
            (pointsToBytes_to_memRegion_anyHeap (a + 0xc8#64) m.identityKey.publicKey.bytes.toList 32
              (List.Vector.toList_length _) (by decide))
            (memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap (a + 0xe8#64) m.registrationId)
              (memRegion_anyHeap_join (pointsTo32_to_memRegion_anyHeap (a + 0xec#64) m.signedPreKeyId)
                (memRegion_anyHeap_join (pointsTo8_to_memRegion_anyHeap (a + 0xf0#64) m.messageVersion)
                  (memRegion_to_memRegion_anyHeap (a + 0xf1#64) 7)
                  rfl (by bv_lin) (by decide))
                rfl (by bv_lin) (by decide))
              rfl (by bv_lin) (by decide))
            rfl (by bv_lin) (by decide))
          rfl (by bv_lin) (by decide))
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide))
    rfl (by bv_lin) (by decide)

private theorem preKeyMsgAt_entails_loose (A : RustAlloc)
    (g : LibsignalPublicApiRepr.PreKeyMsgGhost) (ret : BitVec 64) (psm : PreKeySignalMessage) :
    LibsignalPublicApiRepr.preKeyMsgAt A g ret psm ⊢
      apiEncResultAtLoose A ret (.ok (.preKeySignalMessage psm)) := by
  unfold LibsignalPublicApiRepr.preKeyMsgAt signalMessageAt
  dsimp only [apiEncResultAtLoose]
  rw [sepConj_assoc]
  apply Entails.pure_left; intro _
  unfold vecU8At vecHeader
  simp only [sepConj_assoc]
  have hrearr :
      (ret ↦₆₄ g.msg.pqCap) ∗ ((ret + 8#64) ↦₆₄ g.msg.pqPtr) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 psm.message.pqRatchet.length) ∗
        ⌜psm.message.pqRatchet.length ≤ g.msg.pqCap.toNat ∧ g.msg.pqCap.toNat < 2 ^ 63 ∧
           g.msg.pqPtr ≠ 0⌝ ∗
        (if g.msg.pqCap = 0 then emp
         else A.live g.msg.pqPtr g.msg.pqCap.toNat 1 ∗ (g.msg.pqPtr ↦ₛ psm.message.pqRatchet) ∗
           memRegion (g.msg.pqPtr + BitVec.ofNat 64 psm.message.pqRatchet.length)
             (g.msg.pqCap.toNat - psm.message.pqRatchet.length)) ∗
        boxU8At A (ret + asm64% smCiphertextOff) g.msg.ctPtr psm.message.ciphertext ∗
        boxU8At A (ret + asm64% smSerializedOff) g.msg.serPtr psm.message.serialized ∗
        ((ret + asm64% smSenderRatchetKeyOff) ↦ₛ psm.message.senderRatchetKey.bytes.toList) ∗
        optBoxU8At A (ret + asm64% smAddressesOff) g.msg.addrPtr psm.message.addresses ∗
        ((ret + asm64% smCounterOff) ↦₃₂ psm.message.counter) ∗
        ((ret + asm64% smPreviousCounterOff) ↦₃₂ psm.message.previousCounter) ∗
        ((ret + asm64% smMessageVersionOff) ↦₈ psm.message.messageVersion) ∗
        memRegion (ret + asm64% (smMessageVersionOff + 1))
          (asm% (signalMessageSize - (smMessageVersionOff + 1))) ∗
        LibsignalPublicApiRepr.optU32At (ret + 0x78#64) psm.preKeyId ∗
        boxU8At A (ret + 0x80#64) g.serPtr psm.serialized ∗
        LibsignalPublicApiRepr.optKyberAt A (ret + 0x90#64) g.kyberPtr psm.kyberPayload ∗
        ((ret + 0xa8#64) ↦ₛ psm.baseKey.bytes.toList) ∗
        ((ret + 0xc8#64) ↦ₛ psm.identityKey.publicKey.bytes.toList) ∗
        ((ret + 0xe8#64) ↦₃₂ psm.registrationId) ∗ ((ret + 0xec#64) ↦₃₂ psm.signedPreKeyId) ∗
        ((ret + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (ret + 0xf1#64) 7 =
      ⌜psm.message.pqRatchet.length ≤ g.msg.pqCap.toNat ∧ g.msg.pqCap.toNat < 2 ^ 63 ∧
        g.msg.pqPtr ≠ 0⌝ ∗
        (ret ↦₆₄ g.msg.pqCap) ∗
        boxU8At A (ret + 0x28#64) g.msg.serPtr psm.message.serialized ∗
        (((ret + 8#64) ↦₆₄ g.msg.pqPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 psm.message.pqRatchet.length) ∗
          boxU8At A (ret + 0x18#64) g.msg.ctPtr psm.message.ciphertext) ∗
        ((((ret + asm64% smSenderRatchetKeyOff) ↦ₛ psm.message.senderRatchetKey.bytes.toList) ∗
          optBoxU8At A (ret + asm64% smAddressesOff) g.msg.addrPtr psm.message.addresses ∗
          ((ret + asm64% smCounterOff) ↦₃₂ psm.message.counter) ∗
          ((ret + asm64% smPreviousCounterOff) ↦₃₂ psm.message.previousCounter) ∗
          ((ret + asm64% smMessageVersionOff) ↦₈ psm.message.messageVersion) ∗
          memRegion (ret + asm64% (smMessageVersionOff + 1))
            (asm% (signalMessageSize - (smMessageVersionOff + 1)))) ∗
         (LibsignalPublicApiRepr.optU32At (ret + 0x78#64) psm.preKeyId ∗
          boxU8At A (ret + 0x80#64) g.serPtr psm.serialized ∗
          LibsignalPublicApiRepr.optKyberAt A (ret + 0x90#64) g.kyberPtr psm.kyberPayload ∗
          ((ret + 0xa8#64) ↦ₛ psm.baseKey.bytes.toList) ∗
          ((ret + 0xc8#64) ↦ₛ psm.identityKey.publicKey.bytes.toList) ∗
          ((ret + 0xe8#64) ↦₃₂ psm.registrationId) ∗ ((ret + 0xec#64) ↦₃₂ psm.signedPreKeyId) ∗
          ((ret + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (ret + 0xf1#64) 7)) ∗
        (if g.msg.pqCap = 0 then emp
         else A.live g.msg.pqPtr g.msg.pqCap.toNat 1 ∗ (g.msg.pqPtr ↦ₛ psm.message.pqRatchet) ∗
           memRegion (g.msg.pqPtr + BitVec.ofNat 64 psm.message.pqRatchet.length)
             (g.msg.pqCap.toNat - psm.message.pqRatchet.length)) := by
    ac_rfl
  rw [hrearr]
  apply Entails.pure_left; rintro ⟨_, hcap, _⟩
  have hw : (ret ↦₆₄ g.msg.pqCap) ⊢ ∃∗ w : BitVec 64, ⌜w.toNat < 2 ^ 63⌝ ∗ (ret ↦₆₄ w) :=
    Entails.sepExists_right g.msg.pqCap (Entails.pure_right hcap (Entails.refl _))
  have hser : boxU8At A (ret + 0x28#64) g.msg.serPtr psm.message.serialized ⊢
      ∃∗ serPtr : BitVec 64, boxU8At A (ret + 0x28#64) serPtr psm.message.serialized :=
    Entails.sepExists_right g.msg.serPtr (Entails.refl _)
  have h32 :
      (((ret + 8#64) ↦₆₄ g.msg.pqPtr) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 psm.message.pqRatchet.length) ∗
        boxU8At A (ret + 0x18#64) g.msg.ctPtr psm.message.ciphertext) ⊢
      memRegion (ret + 8#64) 32 ∗ anyHeap :=
    memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap (ret + 8#64) g.msg.pqPtr)
      (memRegion_anyHeap_join (pointsTo64_to_memRegion_anyHeap (ret + 16#64) _)
        (boxU8At_to_memRegion_anyHeap A (ret + 0x18#64) g.msg.ctPtr psm.message.ciphertext)
        rfl (by bv_lin) (by decide))
      rfl (by bv_lin) (by decide)
  have h192 :
      ((((ret + asm64% smSenderRatchetKeyOff) ↦ₛ psm.message.senderRatchetKey.bytes.toList) ∗
        optBoxU8At A (ret + asm64% smAddressesOff) g.msg.addrPtr psm.message.addresses ∗
        ((ret + asm64% smCounterOff) ↦₃₂ psm.message.counter) ∗
        ((ret + asm64% smPreviousCounterOff) ↦₃₂ psm.message.previousCounter) ∗
        ((ret + asm64% smMessageVersionOff) ↦₈ psm.message.messageVersion) ∗
        memRegion (ret + asm64% (smMessageVersionOff + 1))
          (asm% (signalMessageSize - (smMessageVersionOff + 1)))) ∗
       (LibsignalPublicApiRepr.optU32At (ret + 0x78#64) psm.preKeyId ∗
        boxU8At A (ret + 0x80#64) g.serPtr psm.serialized ∗
        LibsignalPublicApiRepr.optKyberAt A (ret + 0x90#64) g.kyberPtr psm.kyberPayload ∗
        ((ret + 0xa8#64) ↦ₛ psm.baseKey.bytes.toList) ∗
        ((ret + 0xc8#64) ↦ₛ psm.identityKey.publicKey.bytes.toList) ∗
        ((ret + 0xe8#64) ↦₃₂ psm.registrationId) ∗ ((ret + 0xec#64) ↦₃₂ psm.signedPreKeyId) ∗
        ((ret + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (ret + 0xf1#64) 7)) ⊢
      memRegion (ret + 0x38#64) 192 ∗ anyHeap :=
    memRegion_anyHeap_join (signalMessage_tail64_to_memRegion_anyHeap A g.msg ret psm.message)
      (preKeyMsg_tail128_to_memRegion_anyHeap A g ret psm)
      rfl (by bv_lin) (by decide)
  refine Entails.trans (sepConj_mono hw (sepConj_mono hser (sepConj_mono h32
    (sepConj_mono h192 (entails_anyHeap _))))) ?_
  have hgoal :
      (∃∗ w : BitVec 64, ⌜w.toNat < 2 ^ 63⌝ ∗ (ret ↦₆₄ w)) ∗
        (∃∗ serPtr : BitVec 64, boxU8At A (ret + 0x28#64) serPtr psm.message.serialized) ∗
        (memRegion (ret + 8#64) 32 ∗ anyHeap) ∗
        (memRegion (ret + 0x38#64) 192 ∗ anyHeap) ∗ anyHeap =
      (∃∗ w : BitVec 64, ⌜w.toNat < 2 ^ 63⌝ ∗ (ret ↦₆₄ w)) ∗
        memRegion (ret + 8#64) 32 ∗
        (∃∗ serPtr : BitVec 64, boxU8At A (ret + 0x28#64) serPtr psm.message.serialized) ∗
        memRegion (ret + 0x38#64) 192 ∗
        (anyHeap ∗ anyHeap ∗ anyHeap) := by ac_rfl
  rw [hgoal]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (entails_anyHeap _))))

theorem apiEncResultAt_entails_loose (A : RustAlloc) (ret : BitVec 64)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) :
    LibsignalPublicApiRepr.apiEncResultAt A ret res ⊢ apiEncResultAtLoose A ret res := by
  cases res with
  | ok cm =>
    cases cm with
    | signalMessage sm =>
      exact Entails.refl _
    | preKeySignalMessage psm =>
      dsimp only [LibsignalPublicApiRepr.apiEncResultAt]
      apply Entails.sepExists_elim; intro g
      exact preKeyMsgAt_entails_loose A g ret psm
  | error err =>
    cases err with
    | protocol e =>
      dsimp only [LibsignalPublicApiRepr.apiEncResultAt, apiEncResultAtLoose]
      refine sepConj_mono_right ?_
      exact memRegion_anyHeap_join (speAt_to_memRegion_anyHeap A (utf8 "encrypt") (ret + 8#64) e)
        (memRegion_to_memRegion_anyHeap (ret + 56#64) 192)
        rfl (by bv_lin) (by decide)
    | sessionNotFound a op =>
      dsimp only [LibsignalPublicApiRepr.apiEncResultAt, apiEncResultAtLoose]
      refine sepConj_mono_right ?_
      exact memRegion_anyHeap_join
        (apiErrAt_to_memRegion_anyHeap A (ret + 8#64) (.sessionNotFound a op))
        (memRegion_to_memRegion_anyHeap (ret + 56#64) 192)
        rfl (by bv_lin) (by decide)
    | untrustedIdentity a =>
      dsimp only [LibsignalPublicApiRepr.apiEncResultAt, apiEncResultAtLoose]
      refine sepConj_mono_right ?_
      exact memRegion_anyHeap_join
        (apiErrAt_to_memRegion_anyHeap A (ret + 8#64) (.untrustedIdentity a))
        (memRegion_to_memRegion_anyHeap (ret + 56#64) 192)
        rfl (by bv_lin) (by decide)
    | store u =>
      dsimp only [LibsignalPublicApiRepr.apiEncResultAt, apiEncResultAtLoose]
      refine sepConj_mono_right ?_
      exact memRegion_anyHeap_join
        (apiErrAt_to_memRegion_anyHeap A (ret + 8#64) (.store u))
        (memRegion_to_memRegion_anyHeap (ret + 56#64) 192)
        rfl (by bv_lin) (by decide)
    | panic =>
      dsimp only [LibsignalPublicApiRepr.apiEncResultAt, apiEncResultAtLoose]
      refine sepConj_mono_right ?_
      exact memRegion_anyHeap_join
        (apiErrAt_to_memRegion_anyHeap A (ret + 8#64) .panic)
        (memRegion_to_memRegion_anyHeap (ret + 56#64) 192)
        rfl (by bv_lin) (by decide)

end ApiEncResultEntailsLoose

end CryptoVerification.E2E.Bin
