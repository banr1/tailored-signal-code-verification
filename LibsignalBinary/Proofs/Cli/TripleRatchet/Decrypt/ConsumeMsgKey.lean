/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.KeyDeriveBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.TryDecryptStateRatchetCoins
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.Entry

/-!
# `try_decrypt_with_state` Segment S4 (`ConsumeMsgKey`) Proof

Proves segment S4 (`ConsumeMsgKeySpec`, `+0x3e4 → +0x5b8 / +0x30c`), covering
`<ProtocolAddress as Display>::fmt`, `RatchetState::consume_message_key`, and cleanup of the
formatted address string.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc

attribute [local wp_norm] BitVec.add_assoc

attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

private theorem entails_of_false {Q : SepProp} : (⌜False⌝ : SepProp) ⊢ Q := by
  rw [← sepConj_emp ⌜False⌝]
  exact Entails.pure_left False.elim

private theorem pointsToBytes4_eq (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3]) = (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) := by
  apply IsBlock.eq (IsBlock.pointsToBytes a [b0, b1, b2, b3])
    (IsBlock.pointsTo32 a (b3 ++ b2 ++ b1 ++ b0))
  intro m
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Memory.readBytes, Memory.read32,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  generalize m.read8 a = x0
  generalize m.read8 (a + 1#64) = x1
  generalize m.read8 (a + 2#64) = x2
  generalize m.read8 (a + 3#64) = x3
  constructor
  · rintro ⟨_, h⟩
    injection h with h0 h
    injection h with h1 h
    injection h with h2 h
    injection h with h3 _
    subst h0 h1 h2 h3; rfl
  · intro h
    refine ⟨by decide, ?_⟩
    have e0 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 0 8 = u0 := by
      intro _ _ _ _; bv_kernel
    have e1 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 8 8 = u1 := by
      intro _ _ _ _; bv_kernel
    have e2 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 16 8 = u2 := by
      intro _ _ _ _; bv_kernel
    have e3 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 24 8 = u3 := by
      intro _ _ _ _; bv_kernel
    have hx0 : x0 = b0 := by simpa only [e0] using congrArg (fun v => v.extractLsb' 0 8) h
    have hx1 : x1 = b1 := by simpa only [e1] using congrArg (fun v => v.extractLsb' 8 8) h
    have hx2 : x2 = b2 := by simpa only [e2] using congrArg (fun v => v.extractLsb' 16 8) h
    have hx3 : x3 = b3 := by simpa only [e3] using congrArg (fun v => v.extractLsb' 24 8) h
    rw [hx0, hx1, hx2, hx3]

private theorem split_bytes_4 {bs : List (BitVec 8)} {n : Nat} (h : bs.length = 4 + n) :
    ∃ (w : BitVec 32) (rest : List (BitVec 8)),
      rest.length = n ∧
      ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ w) ∗ ((a + 4#64) ↦ₛ rest) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
  · simp only [List.length_nil] at h; omega
  · simp only [List.length_cons, List.length_nil] at h; omega
  · simp only [List.length_cons, List.length_nil] at h; omega
  · simp only [List.length_cons, List.length_nil] at h; omega
  · simp only [List.length_cons] at h
    refine ⟨b3 ++ b2 ++ b1 ++ b0, rest, by omega, fun a => ?_⟩
    have hsplit := pointsToBytes_append a [b0, b1, b2, b3] rest
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hsplit
    change (a ↦ₛ ([b0, b1, b2, b3] ++ rest)) = _
    rw [hsplit, pointsToBytes4_eq]

private theorem split_bytes_4_end {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ (w : BitVec 32), ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ w) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
  · cases h
  · cases h
  · cases h
  · cases h
  · exact ⟨b3 ++ b2 ++ b1 ++ b0, fun a => pointsToBytes4_eq a b0 b1 b2 b3⟩
  · simp only [List.length_cons] at h; omega

private theorem chainKeyBytes_len (ck : ChainKey) :
    (chainKeyBytes ck).length = 36 := by
  simp [chainKeyBytes, keyToBytes32, leBytes]

private theorem split_chainKeyBytes (ck : ChainKey) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 32),
      (∀ a : BitVec 64,
        (a ↦ₛ (chainKeyBytes ck).drop 20) =
          (a ↦₆₄ (w6 ++ w5)) ∗ ((a + 8#64) ↦₆₄ (w8 ++ w7))) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ (chainKeyBytes ck).take 20) =
          (a ↦₆₄ (w1 ++ w0)) ∗ ((a + 8#64) ↦₆₄ (w3 ++ w2)) ∗ ((a + 16#64) ↦₃₂ w4)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ chainKeyBytes ck) =
          (a ↦₆₄ (w1 ++ w0)) ∗ ((a + 8#64) ↦₆₄ (w3 ++ w2)) ∗
          ((a + 16#64) ↦₆₄ (w5 ++ w4)) ∗ ((a + 24#64) ↦₆₄ (w7 ++ w6)) ∗
          ((a + 32#64) ↦₃₂ w8)) := by
  have hlen := chainKeyBytes_len ck
  have htake_len : ((chainKeyBytes ck).take 20).length = 20 := by simp [hlen]
  have hdrop_len : ((chainKeyBytes ck).drop 20).length = 16 := by simp [hlen]
  obtain ⟨w0, r1, hr1, hw0⟩ := split_bytes_4 (n := 16) htake_len
  obtain ⟨w1, r2, hr2, hw1⟩ := split_bytes_4 (n := 12) hr1
  obtain ⟨w2, r3, hr3, hw2⟩ := split_bytes_4 (n := 8) hr2
  obtain ⟨w3, r4, hr4, hw3⟩ := split_bytes_4 (n := 4) hr3
  obtain ⟨w4, hw4⟩ := split_bytes_4_end hr4
  obtain ⟨w5, d1, hd1, hw5⟩ := split_bytes_4 (n := 12) hdrop_len
  obtain ⟨w6, d2, hd2, hw6⟩ := split_bytes_4 (n := 8) hd1
  obtain ⟨w7, d3, hd3, hw7⟩ := split_bytes_4 (n := 4) hd2
  obtain ⟨w8, hw8⟩ := split_bytes_4_end hd3
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, ?_, ?_, ?_⟩
  · intro a
    rw [hw5, hw6, hw7, hw8, ← pointsTo32_merge64 a w5 w6, ← pointsTo32_merge64 (a + 8#64) w7 w8]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · intro a
    rw [hw0, hw1, hw2, hw3, hw4, ← pointsTo32_merge64 a w0 w1, ← pointsTo32_merge64 (a + 8#64) w2 w3]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · intro a
    have happ : chainKeyBytes ck = (chainKeyBytes ck).take 20 ++ (chainKeyBytes ck).drop 20 :=
      (List.take_append_drop 20 (chainKeyBytes ck)).symm
    conv_lhs => rw [happ]
    rw [pointsToBytes_append, htake_len,
      hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8,
      ← pointsTo32_merge64 a w0 w1,
      ← pointsTo32_merge64 (a + 8#64) w2 w3,
      ← pointsTo32_merge64 (a + 16#64) w4 w5,
      ← pointsTo32_merge64 (a + 24#64) w6 w7]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem realign_416_436 (sp : BitVec 64) (w4 w5 w6 w7 w8 : BitVec 32) :
    ((sp + 416#64) ↦₃₂ w4) ∗ ((sp + 420#64) ↦₆₄ (w6 ++ w5)) ∗ ((sp + 428#64) ↦₆₄ (w8 ++ w7)) ⊢
    ((sp + 416#64) ↦₆₄ (w5 ++ w4)) ∗ ((sp + 424#64) ↦₆₄ (w7 ++ w6)) ∗ ((sp + 432#64) ↦₃₂ w8) := by
  have h65 := (pointsTo32_merge64 (sp + 420#64) w5 w6).symm
  have h87 := (pointsTo32_merge64 (sp + 428#64) w7 w8).symm
  have h54 := (pointsTo32_merge64 (sp + 416#64) w4 w5).symm
  have h76 := (pointsTo32_merge64 (sp + 424#64) w6 w7).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h65 h87 h54 h76
  rw [h65, h87, h54, h76]
  have heq :
      ((sp + 416#64) ↦₃₂ w4) ∗ (((sp + 420#64) ↦₃₂ w5) ∗ ((sp + 424#64) ↦₃₂ w6)) ∗
        (((sp + 428#64) ↦₃₂ w7) ∗ ((sp + 432#64) ↦₃₂ w8)) =
      (((sp + 416#64) ↦₃₂ w4) ∗ ((sp + 420#64) ↦₃₂ w5)) ∗
        (((sp + 424#64) ↦₃₂ w6) ∗ ((sp + 428#64) ↦₃₂ w7)) ∗
        ((sp + 432#64) ↦₃₂ w8) := by ac_rfl
  rw [heq]
  exact Entails.refl _

private theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (k : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= k) s =
      match (Mut.exec m s).1 with
      | .ok a => Mut.exec (k a) (Mut.exec m s).2
      | .error e => (.error e, (Mut.exec m s).2) := by
  change (match m s with | (r, s') => ExceptT.bindCont k r s') =
    match (m s).1 with
    | .ok a => (k a).run (m s).2
    | .error e => (.error e, (m s).2)
  cases m s with
  | mk r s' =>
    cases r <;> rfl

private theorem mut_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem takeSkippedKey_senderChain (their : PublicKey) (counter : BitVec 32) (s : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) s).2.senderChain = s.senderChain := by
  unfold RatchetState.takeSkippedKey
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
  · rfl

private theorem storeSkippedKey_senderChain (their : PublicKey) (key : MessageKeyGenerator) (s : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) s).2.senderChain = s.senderChain := by
  unfold RatchetState.storeSkippedKey
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem setReceiverChainKey_senderChain (their : PublicKey) (ck : ChainKey) (s : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) s).2.senderChain = s.senderChain := by
  unfold RatchetState.setReceiverChainKey
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem advanceChain_senderChain (F : ShaCompress) (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : Nat) (ck : ChainKey) (s : RatchetState),
      (Mut.exec (RatchetState.advanceChain F their counter fuel ck) s).2.senderChain = s.senderChain
  | 0, ck, s => rfl
  | fuel + 1, ck, s => by
    unfold RatchetState.advanceChain
    split
    · rw [mut_exec_bind]
      have h1 := storeSkippedKey_senderChain their (ck.messageKeys F) s
      cases hst : (Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) s).1 with
      | error e => exact h1
      | ok u =>
        dsimp only
        rw [mut_exec_bind, mut_exec_liftE]
        cases hnk : ck.nextChainKey F with
        | error e => exact h1
        | ok ck' =>
          dsimp only
          exact (advanceChain_senderChain F their counter fuel ck' _).trans h1
    · rfl

private theorem consumeMessageKey_senderChain (F : ShaCompress) (their : PublicKey) (ck : ChainKey)
    (counter : BitVec 32) (msgType : MessageType) (s : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) s).2.senderChain = s.senderChain := by
  unfold RatchetState.consumeMessageKey
  dsimp only
  split
  · rw [mut_exec_bind]
    have h1 := takeSkippedKey_senderChain their counter s
    cases htk : (Mut.exec (RatchetState.takeSkippedKey their counter) s).1 with
    | error e => exact h1
    | ok o => cases o <;> exact h1
  · rw [mut_exec_bind, mut_exec_get]
    dsimp only
    split
    · rfl
    · rw [mut_exec_bind]
      have hadv := advanceChain_senderChain F their counter (counter - ck.index).toNat ck s
      cases hadv1 : (Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) s).1 with
      | error e => exact hadv
      | ok ck' =>
        dsimp only
        rw [mut_exec_bind, mut_exec_liftE]
        cases hnk : ck'.nextChainKey F with
        | error e => exact hadv
        | ok nextCk =>
          dsimp only
          rw [mut_exec_bind]
          have hset := setReceiverChainKey_senderChain their nextCk
            (Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) s).2
          cases (Mut.exec (RatchetState.setReceiverChainKey their nextCk)
            (Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) s).2).1 <;>
            exact hset.trans hadv

private def ErrWordsRel (A : RustAlloc) (e : SignalProtocolError)
    (w416 w424 w432 w440 : BitVec 64) (restHeap : SepProp) : Prop :=
  match e with
  | .duplicatedMessage i c =>
    w416 = c ++ i ∧ restHeap = emp
  | .invalidMessage t .tooFarInFuture =>
    ∃ hi : BitVec 56,
      w432 = BitVec.ofNat 64 tooFarInFutureStr.length ∧
      w440 = hi ++ msgTypeByte t ∧
      tooFarInFutureStr.length ≤ w416.toNat ∧ w416.toNat < 2 ^ 63 ∧ w424 ≠ 0 ∧
      restHeap = (if w416 = 0 then emp else A.live w424 w416.toNat 1 ∗
        (w424 ↦ₛ tooFarInFutureStr) ∗
        memRegion (w424 + BitVec.ofNat 64 tooFarInFutureStr.length)
          (w416.toNat - tooFarInFutureStr.length))
  | _ => False

private theorem resultAt_err_unpack (A : RustAlloc) (sp : BitVec 64) (e : SignalProtocolError) :
    consumeMessageKeyResultAt A (sp + 400#64) (.error e) ⊢
    ∃∗ w416 : BitVec 64, ∃∗ w424 : BitVec 64, ∃∗ w432 : BitVec 64,
    ∃∗ w440 : BitVec 64, ∃∗ w448 : BitVec 64, ∃∗ restHeap : SepProp,
      ⌜ErrWordsRel A e w416 w424 w432 w440 restHeap ∧ speTag e + 2#64 ≠ 0#64⌝ ∗
      ((sp + 400#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 404#64) 4 ∗
      ((sp + 408#64) ↦₆₄ speTag e) ∗
      ((sp + 416#64) ↦₆₄ w416) ∗
      ((sp + 424#64) ↦₆₄ w424) ∗
      ((sp + 432#64) ↦₆₄ w432) ∗
      ((sp + 440#64) ↦₆₄ w440) ∗
      ((sp + 448#64) ↦₆₄ w448) ∗
      memRegion (sp + 456#64) 32 ∗
      restHeap := by
  unfold consumeMessageKeyResultAt
  split
  · next r heq => cases heq
  · next i c heq =>
    injection heq with heq; subst heq
    dsimp only [speTag, ErrWordsRel]
    have htag : errDuplicatedMessage = speWord 23 := rfl
    have hne : speWord 23 + 2#64 ≠ 0#64 := by decide
    have hmerge : ((sp + 416#64) ↦₃₂ i) ∗ ((sp + 420#64) ↦₃₂ c) = ((sp + 416#64) ↦₆₄ (c ++ i)) := by
      have hm := pointsTo32_merge64 (sp + 416#64) i c
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
      exact hm
    have hmr64 : memRegion (sp + 424#64) 64 =
        memRegion (sp + 424#64) 8 ∗ (memRegion (sp + 432#64) 8 ∗
        (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ memRegion (sp + 456#64) 32))) := by
      rw [mr_cut_add sp 424 8 56 (by decide),
        mr_cut_add sp 432 8 48 (by decide),
        mr_cut_add sp 440 8 40 (by decide),
        mr_cut_add sp 448 8 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, htag, ← sepConj_assoc]
    rw [sepConj_assoc _ ((sp + 416#64) ↦₃₂ i), hmerge, hmr64,
      memRegion_eight (sp + 424#64), memRegion_eight (sp + 432#64),
      memRegion_eight (sp + 440#64), memRegion_eight (sp + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w448 =>
      Entails.sepExists_elim fun w440 =>
      Entails.sepExists_elim fun w432 =>
      Entails.sepExists_elim fun w424 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro (c ++ i))
    refine Entails.trans ?_ (Entails.sepExists_intro w424)
    refine Entails.trans ?_ (Entails.sepExists_intro w432)
    refine Entails.trans ?_ (Entails.sepExists_intro w440)
    refine Entails.trans ?_ (Entails.sepExists_intro w448)
    refine Entails.trans ?_ (Entails.sepExists_intro emp)
    rw [sepConj_emp]
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨⟨trivial, trivial⟩, hne⟩ (Entails.refl _)
  · next t heq =>
    injection heq with heq; subst heq
    dsimp only [speTag, ErrWordsRel, vecU8, vecU8At, vecHeader]
    rw [pointsToBytes_singleton]
    have htag : errInvalidMessage = speWord 24 := rfl
    have hne : speWord 24 + 2#64 ≠ 0#64 := by decide
    have hmr47 : memRegion (sp + 441#64) 47 =
        memRegion ((sp + 440#64) + 1#64) 7 ∗ (memRegion (sp + 448#64) 8 ∗ memRegion (sp + 456#64) 32) := by
      rw [mr_cut_add sp 441 7 40 (by decide), mr_cut_add sp 448 8 32 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr47 ⊢
    rw [htag, hmr47, memRegion_eight (sp + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w448 =>
      Entails.sepExists_elim fun cap =>
      Entails.sepExists_elim fun ptr => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Entails.pure_left fun ⟨h1, h2, h3⟩ => ?_
    have h440 := pointsTo8_memRegion7_to_64 (sp + 440#64) (msgTypeByte t)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h440
    have hstep :
        ((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗ ((sp + 408#64) ↦₆₄ speWord 24) ∗
        ((sp + 416#64) ↦₆₄ cap) ∗ ((sp + 424#64) ↦₆₄ ptr) ∗
        ((sp + 432#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ tooFarInFutureStr) ∗
          memRegion (ptr + BitVec.ofNat 64 tooFarInFutureStr.length)
            (cap.toNat - tooFarInFutureStr.length)) ∗
        ((sp + 440#64) ↦₈ msgTypeByte t) ∗ memRegion (sp + 441#64) 7 ∗
        ((sp + 448#64) ↦₆₄ w448) ∗ memRegion (sp + 456#64) 32 ⊢
        (∃∗ hi : BitVec 56, (sp + 440#64) ↦₆₄ (hi ++ msgTypeByte t)) ∗
        (((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗ ((sp + 408#64) ↦₆₄ speWord 24) ∗
         ((sp + 416#64) ↦₆₄ cap) ∗ ((sp + 424#64) ↦₆₄ ptr) ∗
         ((sp + 432#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
         ((sp + 448#64) ↦₆₄ w448) ∗ memRegion (sp + 456#64) 32 ∗
         (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ tooFarInFutureStr) ∗
           memRegion (ptr + BitVec.ofNat 64 tooFarInFutureStr.length)
             (cap.toNat - tooFarInFutureStr.length))) := by
      have heq :
          ((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗ ((sp + 408#64) ↦₆₄ speWord 24) ∗
          ((sp + 416#64) ↦₆₄ cap) ∗ ((sp + 424#64) ↦₆₄ ptr) ∗
          ((sp + 432#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
          (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ tooFarInFutureStr) ∗
            memRegion (ptr + BitVec.ofNat 64 tooFarInFutureStr.length)
              (cap.toNat - tooFarInFutureStr.length)) ∗
          ((sp + 440#64) ↦₈ msgTypeByte t) ∗ memRegion (sp + 441#64) 7 ∗
          ((sp + 448#64) ↦₆₄ w448) ∗ memRegion (sp + 456#64) 32 =
          (((sp + 440#64) ↦₈ msgTypeByte t) ∗ memRegion (sp + 441#64) 7) ∗
          (((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗ ((sp + 408#64) ↦₆₄ speWord 24) ∗
           ((sp + 416#64) ↦₆₄ cap) ∗ ((sp + 424#64) ↦₆₄ ptr) ∗
           ((sp + 432#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
           ((sp + 448#64) ↦₆₄ w448) ∗ memRegion (sp + 456#64) 32 ∗
           (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ tooFarInFutureStr) ∗
             memRegion (ptr + BitVec.ofNat 64 tooFarInFutureStr.length)
               (cap.toNat - tooFarInFutureStr.length))) := by ac_rfl
      rw [heq]
      exact sepConj_mono_left h440
    refine Entails.trans hstep ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun hi => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro cap)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 tooFarInFutureStr.length))
    refine Entails.trans ?_ (Entails.sepExists_intro (hi ++ msgTypeByte t))
    refine Entails.trans ?_ (Entails.sepExists_intro w448)
    refine Entails.trans ?_ (Entails.sepExists_intro
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ tooFarInFutureStr) ∗
        memRegion (ptr + BitVec.ofNat 64 tooFarInFutureStr.length)
          (cap.toNat - tooFarInFutureStr.length)))
    refine Entails.pure_right ⟨⟨hi, rfl, rfl, h1, h2, h3, rfl⟩, hne⟩ ?_
    have heq2 :
        ((sp + 440#64) ↦₆₄ (hi ++ msgTypeByte t)) ∗
        (((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗ ((sp + 408#64) ↦₆₄ speWord 24) ∗
         ((sp + 416#64) ↦₆₄ cap) ∗ ((sp + 424#64) ↦₆₄ ptr) ∗
         ((sp + 432#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
         ((sp + 448#64) ↦₆₄ w448) ∗ memRegion (sp + 456#64) 32 ∗
         (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ tooFarInFutureStr) ∗
           memRegion (ptr + BitVec.ofNat 64 tooFarInFutureStr.length)
             (cap.toNat - tooFarInFutureStr.length))) =
        ((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗ ((sp + 408#64) ↦₆₄ speWord 24) ∗
        ((sp + 416#64) ↦₆₄ cap) ∗ ((sp + 424#64) ↦₆₄ ptr) ∗
        ((sp + 432#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
        ((sp + 440#64) ↦₆₄ (hi ++ msgTypeByte t)) ∗
        ((sp + 448#64) ↦₆₄ w448) ∗ memRegion (sp + 456#64) 32 ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ tooFarInFutureStr) ∗
          memRegion (ptr + BitVec.ofNat 64 tooFarInFutureStr.length)
            (cap.toNat - tooFarInFutureStr.length)) := by ac_rfl
    rw [heq2]
    exact Entails.refl _
  · exact entails_of_false

private theorem speBodyAt_err_pack (A : RustAlloc) (sp : BitVec 64) (e : SignalProtocolError)
    (w416 w424 w432 w440 w448 : BitVec 64) (restHeap : SepProp)
    (hrel : ErrWordsRel A e w416 w424 w432 w440 restHeap) :
    ((sp + 360#64) ↦₆₄ w416) ∗
    ((sp + 368#64) ↦₆₄ w424) ∗
    ((sp + 376#64) ↦₆₄ w432) ∗
    ((sp + 384#64) ↦₆₄ w440) ∗
    ((sp + 392#64) ↦₆₄ w448) ∗
    restHeap ⊢
    speBodyAt A (utf8 "decrypt") (sp + 360#64) e := by
  unfold ErrWordsRel at hrel
  split at hrel
  · -- duplicatedMessage i c
    next i c =>
    rcases hrel with ⟨rfl, rfl⟩
    simp only [speBodyAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    have hsplit : ((sp + 360#64) ↦₆₄ (c ++ i)) =
        ((sp + 360#64) ↦₃₂ i) ∗ ((sp + 364#64) ↦₃₂ c) := by
      have hm := (pointsTo32_merge64 (sp + 360#64) i c).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
      exact hm
    have hmr32 : memRegion (sp + 368#64) 32 =
        memRegion (sp + 368#64) 8 ∗ (memRegion (sp + 376#64) 8 ∗
        (memRegion (sp + 384#64) 8 ∗ memRegion (sp + 392#64) 8)) := by
      rw [mr_cut_add sp 368 8 24 (by decide),
        mr_cut_add sp 376 8 16 (by decide),
        mr_cut_add sp 384 8 8 (by decide)]
    rw [hsplit, hmr32]
    simp only [sepConj_assoc]
    exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (pts64_to_mr _ _) (sepConj_mono (pts64_to_mr _ _)
        (sepConj_mono (pts64_to_mr _ _) (pts64_to_mr _ _)))))
  · -- invalidMessage t tooFarInFuture
    next t =>
    rcases hrel with ⟨hi, rfl, rfl, h1, h2, h3, rfl⟩
    dsimp only [speBodyAt, invalidMessageStrAt, vecU8, vecU8At, vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
    refine Entails.trans ?_ (Entails.sepExists_intro w416)
    refine Entails.trans ?_ (Entails.sepExists_intro w424)
    have h384 := pointsTo64_to_8_memRegion7 (sp + 384#64) hi (msgTypeByte t)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h384
    have hmr15 : memRegion (sp + 385#64) 15 =
        memRegion (sp + 385#64) 7 ∗ memRegion (sp + 392#64) 8 := by
      rw [mr_cut_add sp 385 7 8 (by decide)]
    rw [hmr15]
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Entails.pure_right ⟨h1, h2, h3⟩ ?_
    have heq :
        ((sp + 360#64) ↦₆₄ w416) ∗ ((sp + 368#64) ↦₆₄ w424) ∗
        ((sp + 376#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
        ((sp + 384#64) ↦₆₄ (hi ++ msgTypeByte t)) ∗
        ((sp + 392#64) ↦₆₄ w448) ∗
        (if w416 = 0 then emp else A.live w424 w416.toNat 1 ∗ (w424 ↦ₛ tooFarInFutureStr) ∗
          memRegion (w424 + BitVec.ofNat 64 tooFarInFutureStr.length)
            (w416.toNat - tooFarInFutureStr.length)) =
        ((sp + 360#64) ↦₆₄ w416) ∗ ((sp + 368#64) ↦₆₄ w424) ∗
        ((sp + 376#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
        (if w416 = 0 then emp else A.live w424 w416.toNat 1 ∗ (w424 ↦ₛ tooFarInFutureStr) ∗
          memRegion (w424 + BitVec.ofNat 64 tooFarInFutureStr.length)
            (w416.toNat - tooFarInFutureStr.length)) ∗
        ((sp + 384#64) ↦₆₄ (hi ++ msgTypeByte t)) ∗
        ((sp + 392#64) ↦₆₄ w448) := by ac_rfl
    rw [heq]
    exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (Entails.trans (sepConj_mono h384 (pts64_to_mr _ _))
          (by simp only [sepConj_assoc]; exact Entails.refl _)))))
  · exact hrel.elim

private theorem empty_vecU8_intro (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
    vecU8 A v [] := by
  dsimp only [vecU8, vecU8At, vecHeader]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : 0 ≤ (0#64).toNat ∧ (0#64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := by
    decide
  have heq :
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜0 ≤ (0#64).toNat ∧ (0#64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜0 ≤ (0#64).toNat ∧ (0#64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]
  exact Entails.pure_right hp (Entails.refl _)

private theorem steps_call_out {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {Out : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hfrozen : img.FrozenLoaded sm) (hsym : sm.symtab = img.symtab)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → Out sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ Out s')
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ Out s' := by
  obtain ⟨s', hsteps, hout | hout⟩ :=
    steps_call x hcall hpc hrun hsp hlr hfrozen hsym hL hpre hpanic
      (fun sf h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
        let ⟨s', hs, ho⟩ := hnext sf h1 h2 h3 h4 h5 h6 h7 h8 h9
        ⟨s', hs, Or.inl ho⟩) hexit hoom
  · exact ⟨s', hsteps, hout⟩
  · exact ⟨s', hsteps, hout⟩

private def trNonRatchetAt (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  vecU8At A (sp + 232#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
  ((sp + 256#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
  ((sp + 288#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

private theorem trAt_split_ratchet (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp + 56#64) trG tr =
      ⌜∀ sc, tr.ratchet.senderChain = some sc →
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
      ratchetAt A (sp + 56#64) trG.ratchet tr.ratchet ∗
      trNonRatchetAt A sp trG tr := by
  unfold trAt trNonRatchetAt
  rw [BitVec.add_assoc, show (56#64 : BitVec 64) + 0xb0#64 = 232#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xc8#64 = 256#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xe8#64 = 288#64 by rfl]

private def signalMessageNonTheirAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

private theorem signalMessageAt_split_their (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 56#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
      signalMessageNonTheirAt A g a m := by
  unfold signalMessageAt signalMessageNonTheirAt
  ac_rfl

namespace KeyDeriveCallees

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.cmk_ok_at_entry {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hcmk : CmkOkExt img C A ext)
    (heq : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (CryptoVerification.LibsignalSession.consumeMessageKeySpec C.F A img) := by
  rw [← heq, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq, ← fnAddr_callee_of_fnOff (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") (k := (num% ((2^64 + ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))) rfl]
  exact hcmk

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.consumeMsgKey_cmk_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (mkg : MessageKeyGenerator)
    (draws : Nat) (R : SepProp) (s0 : State)
    {entry sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = entry)
    (hentry_eq : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType)
    (sf2 : State)
    (hpcf2 : sf2.pc = entry + bv% (1144))
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (hx21_f2 : sf2.readReg64 .x21 = x.ss)
    (hx22_f2 : sf2.readReg64 .x22 = x.msgA)
    (hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hff2 : img.FrozenLoaded sf2)
    (hsymf2 : sf2.symtab = img.symtab)
    (hLf2 : (tripleRatchetProgAtExt img.base ext).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.ok mkg) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf2 s' ∧
      ((∃ trG'', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG'' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  decrypt_fetches_at_ext_cli hentry_eq 1144 12
  decrypt_fetches_at_ext_cli hentry_eq 1396 68
  clear hentry_eq
  examples_hide_fetches
  dsimp only [consumeMessageKeyResultAt, vecU8, vecU8At, vecHeader] at hm_post2
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post2
  rcases hm_post2 with ⟨seedCap, seedPtr, hm_post2⟩
  simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm_post2
  rcases hm_post2 with ⟨⟨hseed1, hseed2, hseed3⟩, hm_post2⟩
  simp only [← sepConj_assoc] at hm_post2
  refine steps_of_sepWP hm_post2 hLf2 hff2 hsymf2
    (mid := entry + bv% (1396))
    (RegMid := fun sm3 =>
      (sm3.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x21 = x.ss ∧
      sm3.readReg64 .x22 = x.msgA ∧
      sm3.readReg64 .x23 = sp + 1280#64 ∧
      sm3.readReg64 .x25 = sp + 400#64 ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
          (seedCap.toNat - mkg.seed.length)) ∗
      ((sp + 400#64) ↦₃₂ 1#32) ∗
      memRegion (sp + 404#64) 4 ∗
      ((sp + 408#64) ↦₆₄ seedCap) ∗
      ((sp + 416#64) ↦₆₄ seedPtr) ∗
      ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 432#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 436#64) 52 ∗
      memRegion x.ret 48 ∗
      memRegion sp 28 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 488#64) 920 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre => simp only [sepConj_assoc]
    wp_steps
    wp_done
  · intro sm3 hpc3 hrun3 hf_fr3 hsym3 hL3
      ⟨hx24_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3,
       hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    refine steps_of_sepWP hm3 hL3 hf_fr3 hsym3
      (mid := entry + bv% (1444))
      (RegMid := fun sm4 =>
        (sm4.readReg64 .x24).setWidth 32 = 1#32 ∧
        sm4.readReg64 .x19 = x.ret ∧
        sm4.readReg64 .x20 = sp + 320#64 ∧
        sm4.readReg64 .x21 = x.ss ∧
        sm4.readReg64 .x22 = x.msgA ∧
        sm4.readReg64 .x23 = sp + 1280#64 ∧
        sm4.readReg64 .x25 = sp + 400#64 ∧
        sm4.readReg64 .x27 = dispPtr ∧
        sm4.readReg64 .x28 = dispCap ∧
        sm4.readReg64 .fp = sp + 1408#64 ∧
        sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
        calleeSavedVRegs sm4 = calleeSavedVRegs s0)
      (P_mid :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
          (seedPtr ↦ₛ mkg.seed) ∗
          memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
            (seedCap.toNat - mkg.seed.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 16 ∗
        ((sp + 16#64) ↦₆₄ seedPtr) ∗
        memRegion (sp + 24#64) 4 ∗
        ((sp + 28#64) ↦₃₂ msgW) ∗
        ((sp + 32#64) ↦₆₄ x.locA) ∗
        ((sp + 40#64) ↦₆₄ seedCap) ∗
        ((sp + 48#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 320#64) 784 ∗
        ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
        memRegion (sp + 1116#64) 292 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        logOff img ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ?_ ?_
    · have hsp0 : memRegion sp 28 =
          memRegion sp 16 ∗ (memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4) := by
        have h1 := mr_cut_add sp 0 16 12 (by decide)
        simp only [BitVec.add_zero] at h1
        rw [h1, mr_cut_add sp 16 8 4 (by decide)]
      wp_conv_pre =>
        rw [mr_cut sp 436 4 48 52 440#64,
          memRegion_four (sp + 404#64),
          memRegion_four (sp + 436#64),
          memRegion_four (sp + 44#64)]
        simp only [sepConj_assoc]
      wp_pull_exists
      rename_i pad44 pad436 pad404
      have hmerge432 :
          ((sp + 432#64) ↦₃₂ mkg.counter) ∗ ((sp + 436#64) ↦₃₂ pad436) ⊢
          ((sp + 432#64) ↦₆₄ (pad436 ++ mkg.counter)) := by
        have hm := pointsTo32_merge64 (sp + 432#64) mkg.counter pad436
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
        rw [hm]; exact Entails.refl _
      have hmerge40 :
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ ((sp + 44#64) ↦₃₂ pad44) ⊢
          ((sp + 40#64) ↦₆₄ (pad44 ++ x.msg.counter)) := by
        have hm := pointsTo32_merge64 (sp + 40#64) x.msg.counter pad44
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
        rw [hm]; exact Entails.refl _
      refine SepWP.focus_weaken hmerge432 (by sep_focus) ?_
      refine SepWP.focus_weaken hmerge40 (by sep_focus) ?_
      wp_conv_pre =>
        rw [hsp0,
          mr_cut sp 440 8 40 48 448#64,
          mr_cut sp 448 8 32 40 456#64,
          mr_cut sp 456 8 24 32 464#64,
          mr_cut sp 464 8 16 24 472#64,
          mr_cut sp 472 8 8 16 480#64,
          mr_cut sp 488 616 304 920 1104#64,
          mr_cut sp 1104 8 296 304 1112#64,
          mr_cut sp 1112 8 288 296 1120#64,
          mr_cut sp 1120 8 280 288 1128#64,
          mr_cut sp 1128 8 272 280 1136#64,
          mr_cut sp 1136 8 264 272 1144#64,
          mr_cut sp 1144 8 256 264 1152#64,
          mr_cut sp 1152 8 248 256 1160#64,
          mr_cut sp 1160 8 240 248 1168#64,
          mr_cut sp 1168 112 128 240 1280#64,
          mr_cut sp 1280 8 120 128 1288#64,
          mr_cut sp 1288 8 112 120 1296#64,
          mr_cut sp 1296 8 104 112 1304#64,
          mr_cut sp 1304 8 96 104 1312#64]
        simp only [sepConj_assoc,
          memRegion_eight (sp + 16#64),
          memRegion_eight (sp + 440#64),
          memRegion_eight (sp + 448#64),
          memRegion_eight (sp + 456#64),
          memRegion_eight (sp + 464#64),
          memRegion_eight (sp + 472#64),
          memRegion_eight (sp + 480#64),
          memRegion_eight (sp + 1104#64),
          memRegion_eight (sp + 1112#64),
          memRegion_eight (sp + 1120#64),
          memRegion_eight (sp + 1128#64),
          memRegion_eight (sp + 1136#64),
          memRegion_eight (sp + 1144#64),
          memRegion_eight (sp + 1152#64),
          memRegion_eight (sp + 1160#64),
          memRegion_eight (sp + 1280#64),
          memRegion_eight (sp + 1288#64),
          memRegion_eight (sp + 1296#64),
          memRegion_eight (sp + 1304#64)]
      wp_pull_exists
      wp_steps
      have hsplit1112 :
          ((sp + 1112#64) ↦₆₄ (pad436 ++ mkg.counter)) ⊢
          ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 4 := by
        have hs := (pointsTo32_merge64 (sp + 1112#64) mkg.counter pad436).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
        rw [hs]
        exact sepConj_mono_right (pointsTo32_entails_memRegion (sp + 1116#64) pad436)
      refine SepWP.focus_weaken hsplit1112 (by sep_focus) ?_
      refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 400#64) 1#32) (by sep_focus) ?_
      refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 404#64) pad404) (by sep_focus) ?_
      have hm320 : memRegion (sp + 320#64) 784 =
          memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 4 ∗ (memRegion (sp + 404#64) 4 ∗
          (memRegion (sp + 408#64) 8 ∗ (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗
          (memRegion (sp + 432#64) 8 ∗ (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗
          (memRegion (sp + 456#64) 8 ∗ (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗
          (memRegion (sp + 480#64) 8 ∗ memRegion (sp + 488#64) 616)))))))))))) := by
        rw [mr_cut_add sp 320 80 704 (by decide),
          mr_cut_add sp 400 4 700 (by decide),
          mr_cut_add sp 404 4 696 (by decide),
          mr_cut_add sp 408 8 688 (by decide),
          mr_cut_add sp 416 8 680 (by decide),
          mr_cut_add sp 424 8 672 (by decide),
          mr_cut_add sp 432 8 664 (by decide),
          mr_cut_add sp 440 8 656 (by decide),
          mr_cut_add sp 448 8 648 (by decide),
          mr_cut_add sp 456 8 640 (by decide),
          mr_cut_add sp 464 8 632 (by decide),
          mr_cut_add sp 472 8 624 (by decide),
          mr_cut_add sp 480 8 616 (by decide)]
      have hm1116 : memRegion (sp + 1116#64) 292 =
          memRegion (sp + 1116#64) 4 ∗ (memRegion (sp + 1120#64) 8 ∗
          (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗
          (memRegion (sp + 1144#64) 8 ∗ (memRegion (sp + 1152#64) 8 ∗
          (memRegion (sp + 1160#64) 8 ∗ (memRegion (sp + 1168#64) 112 ∗
          (memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗
          (memRegion (sp + 1296#64) 8 ∗ (memRegion (sp + 1304#64) 8 ∗
           memRegion (sp + 1312#64) 96))))))))))) := by
        rw [mr_cut_add sp 1116 4 288 (by decide),
          mr_cut_add sp 1120 8 280 (by decide),
          mr_cut_add sp 1128 8 272 (by decide),
          mr_cut_add sp 1136 8 264 (by decide),
          mr_cut_add sp 1144 8 256 (by decide),
          mr_cut_add sp 1152 8 248 (by decide),
          mr_cut_add sp 1160 8 240 (by decide),
          mr_cut_add sp 1168 112 128 (by decide),
          mr_cut_add sp 1280 8 120 (by decide),
          mr_cut_add sp 1288 8 112 (by decide),
          mr_cut_add sp 1296 8 104 (by decide),
          mr_cut_add sp 1304 8 96 (by decide)]
      rw [hm320, hm1116]
      wp_done
    · intro sm4 hpc4 hrun4 hf_fr4 hsym4 hL4
        ⟨hx24_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx25_4, hx27_4, hx28_4,
         hfp4, hsp4, hsp_al4, htr4, hvregs4⟩
        hm4
      by_cases hcap : dispCap = 0
      · simp only [hcap, ↓reduceIte, emp_sepConj] at hm4
        subst hcap
        refine steps_of_sepWP hm4 hL4 hf_fr4 hsym4
          (mid := entry + bv% (1464))
          (RegMid := fun sf =>
            (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
            sf.readReg64 .x19 = x.ret ∧
            sf.readReg64 .x20 = sp + 320#64 ∧
            sf.readReg64 .x21 = x.ss ∧
            sf.readReg64 .x22 = x.msgA ∧
            sf.readReg64 .x23 = sp + 1280#64 ∧
            sf.readReg64 .x25 = sp + 400#64 ∧
            sf.readReg64 .fp = sp + 1408#64 ∧
            sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
            memRegion x.ret 48 ∗
            memRegion sp 16 ∗
            ((sp + 16#64) ↦₆₄ seedPtr) ∗
            memRegion (sp + 24#64) 4 ∗
            ((sp + 28#64) ↦₃₂ msgW) ∗
            ((sp + 32#64) ↦₆₄ x.locA) ∗
            ((sp + 40#64) ↦₆₄ seedCap) ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 320#64) 784 ∗
            ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
            ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
            logOff img ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_steps
          wp_done
        · intro sf hpcf hrunf hff hsymf _
            ⟨hx24_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩
            hmf
          subst hsp_def
          refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
          have hpc_s5 : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC img := by
            rw [hpcf]; unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC; rw [hentry]
          have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
            change sf.readReg64 .fp = s0.sp - 96#64
            rw [hfp_f]; exact (sp_fp_eq rfl).symm
          refine ⟨hpc_s5, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hff, hsymf, hvregs_f⟩,
            hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f,
            seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
          dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap]
          simp only [sepConj_assoc] at hmf ⊢
          arm64_sep_close
      · simp only [hcap, ↓reduceIte] at hm4
        have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
        refine steps_of_sepWP hm4 hL4 hf_fr4 hsym4
          (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
          (RegMid := fun sm5 =>
            sm5.readReg64 .x0 = dispPtr ∧
            sm5.readReg64 .x1 = dispCap ∧
            sm5.readReg64 .x2 = 1#64 ∧
            (sm5.readReg64 .x24).setWidth 32 = 1#32 ∧
            sm5.readReg64 .x19 = x.ret ∧
            sm5.readReg64 .x20 = sp + 320#64 ∧
            sm5.readReg64 .x21 = x.ss ∧
            sm5.readReg64 .x22 = x.msgA ∧
            sm5.readReg64 .x23 = sp + 1280#64 ∧
            sm5.readReg64 .x25 = sp + 400#64 ∧
            sm5.readReg64 .fp = sp + 1408#64 ∧
            sm5.readReg64 .lr = entry + bv% (1464) ∧
            sm5.sp = sp ∧ sm5.spAligned = true ∧ sm5.trace = s0.trace ∧
            calleeSavedVRegs sm5 = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            A.live dispPtr dispCap.toNat 1 ∗
            memRegion dispPtr dispCap.toNat ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
            memRegion x.ret 48 ∗
            memRegion sp 16 ∗
            ((sp + 16#64) ↦₆₄ seedPtr) ∗
            memRegion (sp + 24#64) 4 ∗
            ((sp + 28#64) ↦₃₂ msgW) ∗
            ((sp + 32#64) ↦₆₄ x.locA) ∗
            ((sp + 40#64) ↦₆₄ seedCap) ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 320#64) 784 ∗
            ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
            ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
            logOff img ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_conv_pre => simp only [sepConj_assoc]
          wp_steps
          refine SepWP.focus_weaken (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2)
            (by sep_focus) ?_
          wp_done
        · intro sm5 hpc5 hrun5 hf_fr5 hsym5 hL5
            ⟨hx0_5, hx1_5, hx2_5, hx24_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
             hx25_5, hfp5, hlr5, hsp5, hsp_al5, htr5, hvregs5⟩
            hm5
          have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
          have hpre_dealloc : sm5.mem ⊨
              (rustDeallocSpec A).pre (dispPtr, dispCap.toNat, 1) sm5 ∗
              ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
                trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
                (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                  (seedPtr ↦ₛ mkg.seed) ∗
                  memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                    (seedCap.toNat - mkg.seed.length)) ∗
                memRegion x.ret 48 ∗
                memRegion sp 16 ∗
                ((sp + 16#64) ↦₆₄ seedPtr) ∗
                memRegion (sp + 24#64) 4 ∗
                ((sp + 28#64) ↦₃₂ msgW) ∗
                ((sp + 32#64) ↦₆₄ x.locA) ∗
                ((sp + 40#64) ↦₆₄ seedCap) ∗
                ((sp + 48#64) ↦₆₄ x.remA) ∗
                memRegion (sp + 320#64) 784 ∗
                ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
                ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
                memRegion (sp + 1116#64) 292 ∗
                protocolAddressAt A x.rem x.remA ∗
                protocolAddressAt A x.loc x.locA ∗
                signalMessageAt A x.msgG x.msgA x.msg ∗
                CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
                logOff img ∗
                memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                  (tryDecryptSubStack - allocHookStack) ∗
                tryDecryptSavedRegs s0.sp s0) ∗ R) := by
            dsimp only [rustDeallocSpec]
            rw [hsp5, sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨hx0_5, by rw [hx1_5], by rw [hx2_5]; rfl⟩, ?_⟩
            rw [hstack_dealloc] at hm5
            simp only [sepConj_assoc] at hm5 ⊢
            arm64_sep_close
          refine steps_call_out (dispPtr, dispCap.toNat, 1) hdealloc
            hpc5 hrun5 hsp_al5 hlr5 hf_fr5 hsym5 hL5 hpre_dealloc ?_ ?_
          · intro sf _ hpost
            dsimp only [rustDeallocSpec] at hpost
            rw [sepConj_assoc] at hpost
            exact (not_satisfies_false_sepConj hpost).elim
          · intro sf hpcf hrunf hspf hsp_alf hcsf hff hsymf _ hpost
            have hx24_f : (sf.readReg64 .x24).setWidth 32 = 1#32 := by
              rw [show sf.readReg64 .x24 = sm5.readReg64 .x24 by reg_chain]; exact hx24_5
            have hfp_f_sp : sf.readReg64 .fp = sp + 1408#64 := by reg_chain
            dsimp only [rustDeallocSpec] at hpost
            rw [hsp5, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
            rcases hpost with ⟨htr_f, hpost⟩
            subst hsp_def
            refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
            have hpc_s5 : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC img := by
              rw [hpcf]; unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC; rw [hentry]
            have hfp_f : sf.readReg64 .x29 = s0.sp - 96#64 := by
              change sf.readReg64 .fp = s0.sp - 96#64
              rw [hfp_f_sp]; exact (sp_fp_eq rfl).symm
            refine ⟨hpc_s5, ⟨hrunf, by reg_chain, hsp0_al, hsp_alf, hfp_f, by reg_chain, hff, hsymf, by reg_chain⟩,
              by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx24_f,
              by reg_chain, seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
            dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap]
            rw [hstack_dealloc]
            simp only [sepConj_assoc] at hpost ⊢
            arm64_sep_close

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.consumeMsgKey_cmk_err (img : Obj.Image) (_C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (_parse : UuidParser) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (e : SignalProtocolError)
    (draws : Nat) (R : SepProp) (s0 : State)
    {entry sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hne_panic : e ≠ .panic)
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = entry)
    (hentry_eq : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (sf2 : State)
    (hpcf2 : sf2.pc = entry + bv% (1144))
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (_hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hff2 : img.FrozenLoaded sf2)
    (hsymf2 : sf2.symtab = img.symtab)
    (hLf2 : (tripleRatchetProgAtExt img.base ext).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.error e) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf2 s' ∧
      ((e ≠ .panic ∧ ∃ trG'',
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧
         ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
         (s'.mem ⊨ anyHeap ∗ R))) := by
  decrypt_fetches_at_ext_cli hentry_eq 1144 64
  clear hentry_eq
  examples_hide_fetches
  have hm_err : sf2.mem ⊨
      (∃∗ w416 : BitVec 64, ∃∗ w424 : BitVec 64, ∃∗ w432 : BitVec 64,
       ∃∗ w440 : BitVec 64, ∃∗ w448 : BitVec 64, ∃∗ restHeap : SepProp,
        ⌜ErrWordsRel A e w416 w424 w432 w440 restHeap ∧ speTag e + 2#64 ≠ 0#64⌝ ∗
        ((sp + 400#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 404#64) 4 ∗
        ((sp + 408#64) ↦₆₄ speTag e) ∗
        ((sp + 416#64) ↦₆₄ w416) ∗
        ((sp + 424#64) ↦₆₄ w424) ∗
        ((sp + 432#64) ↦₆₄ w432) ∗
        ((sp + 440#64) ↦₆₄ w440) ∗
        ((sp + 448#64) ↦₆₄ w448) ∗
        memRegion (sp + 456#64) 32 ∗
        restHeap) ∗
      ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 56 ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 488#64) 920 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        logOff img ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ∗ R) := by
    have hsp56 : memRegion sp 56 =
        memRegion sp 28 ∗ (memRegion (sp + 28#64) 4 ∗ (memRegion (sp + 32#64) 8 ∗
        (memRegion (sp + 40#64) 4 ∗ (memRegion (sp + 44#64) 4 ∗ memRegion (sp + 48#64) 8)))) := by
      have h1 := mr_cut_add sp 0 28 28 (by decide)
      simp only [BitVec.add_zero] at h1
      rw [h1,
        mr_cut_add sp 28 4 24 (by decide),
        mr_cut_add sp 32 8 16 (by decide),
        mr_cut_add sp 40 4 12 (by decide),
        mr_cut_add sp 44 4 8 (by decide)]
    rw [hsp56]
    refine Satisfies.mono (sepConj_mono_left (resultAt_err_unpack A sp e)) ?_
    have hm_post2' : sf2.mem ⊨
        (((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ ((sp + 48#64) ↦₆₄ x.remA)) ∗
        (consumeMessageKeyResultAt A (sp + 400#64) (.error e) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
         (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
           (dispPtr ↦ₛ dispBs) ∗
           memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
         memRegion x.ret 48 ∗
         memRegion sp 28 ∗
         memRegion (sp + 44#64) 4 ∗
         memRegion (sp + 320#64) 80 ∗
         memRegion (sp + 488#64) 920 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
         logOff img ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool ∗ R) := by
      simp only [sepConj_assoc] at hm_post2 ⊢
      arm64_sep_close
    have hm_post2'' := Satisfies.mono (sepConj_mono_left (sepConj_mono
      (pointsTo32_entails_memRegion (sp + 28#64) msgW)
      (sepConj_mono (pts64_to_mr (sp + 32#64) x.locA)
        (sepConj_mono (pointsTo32_entails_memRegion (sp + 40#64) x.msg.counter)
          (pts64_to_mr (sp + 48#64) x.remA))))) hm_post2'
    change sf2.mem ⊨ _ at hm_post2'' ⊢
    simp only [sepConj_assoc] at hm_post2'' ⊢
    arm64_sep_close
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm_err
  rcases hm_err with ⟨w416, w424, w432, w440, w448, restHeap, hm_err⟩
  rw [satisfies_pure_sepConj] at hm_err
  rcases hm_err with ⟨⟨hrel, htag_ne⟩, hm_err⟩
  simp only [← sepConj_assoc] at hm_err
  refine steps_of_sepWP hm_err hLf2 hff2 hsymf2
    (mid := entry + bv% (1180))
    (RegMid := fun sm3 =>
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x26 = speTag e ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 56 ∗
      memRegion (sp + 320#64) 40 ∗
      speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
      memRegion (sp + 400#64) 1008 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 40 40 80 360#64,
        mr_cut sp 360 8 32 40 368#64,
        mr_cut sp 368 8 24 32 376#64,
        mr_cut sp 376 8 16 24 384#64,
        mr_cut sp 384 8 8 16 392#64,
        mr_cut sp 488 792 128 920 1280#64,
        mr_cut sp 1280 8 120 128 1288#64,
        mr_cut sp 1288 8 112 120 1296#64,
        mr_cut sp 1296 8 104 112 1304#64,
        mr_cut sp 1304 8 96 104 1312#64]
      simp only [sepConj_assoc,
        memRegion_eight (sp + 360#64),
        memRegion_eight (sp + 368#64),
        memRegion_eight (sp + 376#64),
        memRegion_eight (sp + 384#64),
        memRegion_eight (sp + 392#64),
        memRegion_eight (sp + 1280#64),
        memRegion_eight (sp + 1288#64),
        memRegion_eight (sp + 1296#64),
        memRegion_eight (sp + 1304#64)]
    wp_pull_exists
    have htag_beq : (speTag e + 2#64 == 0#64) = false := beq_false_of_ne htag_ne
    have htag_beq0 : (speTag e + 2#64 + 0#64 == 0#64) = false := by
      rw [BitVec.add_zero]; exact htag_beq
    wp_steps
    refine SepWP.focus_weaken
      (speBodyAt_err_pack A sp e w416 w424 w432 w440 w448 restHeap hrel)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (pointsTo32_entails_memRegion (sp + 400#64) 2#32) (by sep_focus) ?_
    have hm400 : memRegion (sp + 400#64) 1008 =
        memRegion (sp + 400#64) 4 ∗ (memRegion (sp + 404#64) 4 ∗ (memRegion (sp + 408#64) 8 ∗
        (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗ (memRegion (sp + 432#64) 8 ∗
        (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 32 ∗
        (memRegion (sp + 488#64) 792 ∗ (memRegion (sp + 1280#64) 8 ∗
        (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
        (memRegion (sp + 1304#64) 8 ∗ memRegion (sp + 1312#64) 96))))))))))))) := by
      rw [mr_cut_add sp 400 4 1004 (by decide),
        mr_cut_add sp 404 4 1000 (by decide),
        mr_cut_add sp 408 8 992 (by decide),
        mr_cut_add sp 416 8 984 (by decide),
        mr_cut_add sp 424 8 976 (by decide),
        mr_cut_add sp 432 8 968 (by decide),
        mr_cut_add sp 440 8 960 (by decide),
        mr_cut_add sp 448 8 952 (by decide),
        mr_cut_add sp 456 32 920 (by decide),
        mr_cut_add sp 488 792 128 (by decide),
        mr_cut_add sp 1280 8 120 (by decide),
        mr_cut_add sp 1288 8 112 (by decide),
        mr_cut_add sp 1296 8 104 (by decide),
        mr_cut_add sp 1304 8 96 (by decide)]
    rw [hm400]
    wp_done
  · intro sm3 hpc3 hrun3 hf_fr3 hsym3 hL3
      ⟨hx19_3, hx20_3, hx26_3, hx27_3, hx28_3, hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    have herr_tail : ∀ st4 : State,
        st4.pc = entry + bv% (1200) → st4.status = .Running →
        st4.sp = sp → st4.spAligned = true →
        st4.readReg64 .fp = sp + 1408#64 → st4.trace = s0.trace →
        calleeSavedVRegs st4 = calleeSavedVRegs s0 →
        img.FrozenLoaded st4 → st4.symtab = img.symtab →
        (tripleRatchetProgAtExt img.base ext).CodeLoaded st4.mem →
        st4.readReg64 .x19 = x.ret →
        st4.readReg64 .x20 = sp + 320#64 →
        st4.readReg64 .x26 = speTag e →
        (st4.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
           memRegion x.ret 48 ∗
           memRegion sp 56 ∗
           memRegion (sp + 320#64) 40 ∗
           speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
           memRegion (sp + 400#64) 1008 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R) →
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) st4 s' ∧
          ((e ≠ .panic ∧ ∃ trG'',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
      intro st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hff4 hsym4 hL4 hx19_4 hx20_4 hx26_4 hm4
      refine steps_of_sepWP hm4 hL4 hff4 hsym4
        (mid := entry + bv% (780))
        (RegMid := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = sp + 320#64 ∧
          sf.readReg64 .x26 = speTag e ∧
          sf.readReg64 .fp = sp + 1408#64 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro sf hpcf hrunf hff hsymf _ ⟨hx19_f, hx20_f, hx26_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩ hmf
        subst hsp_def
        refine ⟨sf, .refl _, Or.inl ⟨hne_panic, trG', ?_⟩⟩
        have hpc_err : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img := by
          rw [hpcf]; unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC; rw [hentry]
        have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
          change sf.readReg64 .fp = s0.sp - 96#64
          rw [hfp_f]; exact (sp_fp_eq rfl).symm
        refine ⟨hpc_err, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hff, hsymf, hvregs_f⟩,
          hx19_f, hx20_f, hx26_f, ?_⟩
        dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap]
        simp only [sepConj_assoc] at hmf ⊢
        arm64_sep_close
    by_cases hcap : dispCap = 0
    · simp only [hcap, ↓reduceIte, emp_sepConj] at hm3
      subst hcap
      refine steps_of_sepWP hm3 hL3 hf_fr3 hsym3
        (mid := entry + bv% (1200))
        (RegMid := fun st4 =>
          st4.readReg64 .x19 = x.ret ∧
          st4.readReg64 .x20 = sp + 320#64 ∧
          st4.readReg64 .x26 = speTag e ∧
          st4.readReg64 .fp = sp + 1408#64 ∧
          st4.sp = sp ∧ st4.spAligned = true ∧ st4.trace = s0.trace ∧
          calleeSavedVRegs st4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro st4 hpc4 hrun4 hff4 hsym4 hL4 ⟨hx19_4, hx20_4, hx26_4, hfp4, hsp4, hsp_al4, htr4, hvregs4⟩ hm4
        exact herr_tail st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hff4 hsym4 hL4 hx19_4 hx20_4 hx26_4 hm4
    · simp only [hcap, ↓reduceIte] at hm3
      have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
      refine steps_of_sepWP hm3 hL3 hf_fr3 hsym3
        (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
        (RegMid := fun sm4 =>
          sm4.readReg64 .x0 = dispPtr ∧
          sm4.readReg64 .x1 = dispCap ∧
          sm4.readReg64 .x2 = 1#64 ∧
          sm4.readReg64 .x19 = x.ret ∧
          sm4.readReg64 .x20 = sp + 320#64 ∧
          sm4.readReg64 .x26 = speTag e ∧
          sm4.readReg64 .fp = sp + 1408#64 ∧
          sm4.readReg64 .lr = entry + bv% (1200) ∧
          sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
          calleeSavedVRegs sm4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          A.live dispPtr dispCap.toNat 1 ∗
          memRegion dispPtr dispCap.toNat ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps
        refine SepWP.focus_weaken (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2)
          (by sep_focus) ?_
        wp_done
      · intro sm4 hpc4 hrun4 hf_fr4 hsym4 hL4
          ⟨hx0_4, hx1_4, hx2_4, hx19_4, hx20_4, hx26_4, hfp4, hlr4, hsp4, hsp_al4, htr4, hvregs4⟩
          hm4
        have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
        have hpre_dealloc : sm4.mem ⊨
            (rustDeallocSpec A).pre (dispPtr, dispCap.toNat, 1) sm4 ∗
            ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
              memRegion x.ret 48 ∗
              memRegion sp 56 ∗
              memRegion (sp + 320#64) 40 ∗
              speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
              memRegion (sp + 400#64) 1008 ∗
              protocolAddressAt A x.rem x.remA ∗
              protocolAddressAt A x.loc x.locA ∗
              signalMessageAt A x.msgG x.msgA x.msg ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
              logOff img ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - allocHookStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [rustDeallocSpec]
          rw [hsp4, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_4, by rw [hx1_4], by rw [hx2_4]; rfl⟩, ?_⟩
          rw [hstack_dealloc] at hm4
          simp only [sepConj_assoc] at hm4 ⊢
          arm64_sep_close
        refine steps_call_out (dispPtr, dispCap.toNat, 1) hdealloc
          hpc4 hrun4 hsp_al4 hlr4 hf_fr4 hsym4 hL4 hpre_dealloc ?_ ?_
        · intro sf _ hpost
          dsimp only [rustDeallocSpec] at hpost
          rw [sepConj_assoc] at hpost
          exact (not_satisfies_false_sepConj hpost).elim
        · intro st5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hff5 hsym5 hL5 hpost5
          dsimp only [rustDeallocSpec] at hpost5
          rw [hsp4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost5
          rcases hpost5 with ⟨htr5, hpost5⟩
          refine herr_tail st5 hpc5 hrun5 (by reg_chain) hsp_al5 (by reg_chain) (by reg_chain) (by reg_chain)
            hff5 hsym5 hL5 (by reg_chain) (by reg_chain) (by reg_chain) ?_
          rw [hstack_dealloc]
          simp only [sepConj_assoc] at hpost5 ⊢
          arm64_sep_close

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.cmk_ok_at_entry_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hcmk : CmkOkX img C A ext)
    (heq : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (cmkSpecX C.F A img) := by
  rw [← heq, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq, ← fnAddr_callee_of_fnOff (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") (k := (num% ((2^64 + ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))) rfl]
  exact hcmk

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.consumeMsgKey_cmk_ok_x (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (mkg : MessageKeyGenerator)
    (draws : Nat) (R : SepProp) (s0 : State)
    {entry sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = entry)
    (hentry_eq : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType)
    (sf2 : State)
    (hpcf2 : sf2.pc = entry + bv% (1144))
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (hx21_f2 : sf2.readReg64 .x21 = x.ss)
    (hx22_f2 : sf2.readReg64 .x22 = x.msgA)
    (hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hff2 : img.FrozenLoaded sf2)
    (hsymf2 : sf2.symtab = img.symtab)
    (hLf2 : (tripleRatchetProgAtExt img.base ext).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.ok mkg) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf2 s' ∧
      ((∃ trG'', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG'' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  decrypt_fetches_at_ext_cli hentry_eq 1144 12
  decrypt_fetches_at_ext_cli hentry_eq 1396 68
  clear hentry_eq
  examples_hide_fetches
  dsimp only [consumeMessageKeyResultAt, vecU8, vecU8At, vecHeader] at hm_post2
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post2
  rcases hm_post2 with ⟨seedCap, seedPtr, hm_post2⟩
  simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm_post2
  rcases hm_post2 with ⟨⟨hseed1, hseed2, hseed3⟩, hm_post2⟩
  simp only [← sepConj_assoc] at hm_post2
  refine steps_of_sepWP hm_post2 hLf2 hff2 hsymf2
    (mid := entry + bv% (1396))
    (RegMid := fun sm3 =>
      (sm3.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x21 = x.ss ∧
      sm3.readReg64 .x22 = x.msgA ∧
      sm3.readReg64 .x23 = sp + 1280#64 ∧
      sm3.readReg64 .x25 = sp + 400#64 ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
          (seedCap.toNat - mkg.seed.length)) ∗
      ((sp + 400#64) ↦₃₂ 1#32) ∗
      memRegion (sp + 404#64) 4 ∗
      ((sp + 408#64) ↦₆₄ seedCap) ∗
      ((sp + 416#64) ↦₆₄ seedPtr) ∗
      ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 432#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 436#64) 52 ∗
      memRegion x.ret 48 ∗
      memRegion sp 28 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 488#64) 920 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre => simp only [sepConj_assoc]
    wp_steps
    wp_done
  · intro sm3 hpc3 hrun3 hf_fr3 hsym3 hL3
      ⟨hx24_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3,
       hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    refine steps_of_sepWP hm3 hL3 hf_fr3 hsym3
      (mid := entry + bv% (1444))
      (RegMid := fun sm4 =>
        (sm4.readReg64 .x24).setWidth 32 = 1#32 ∧
        sm4.readReg64 .x19 = x.ret ∧
        sm4.readReg64 .x20 = sp + 320#64 ∧
        sm4.readReg64 .x21 = x.ss ∧
        sm4.readReg64 .x22 = x.msgA ∧
        sm4.readReg64 .x23 = sp + 1280#64 ∧
        sm4.readReg64 .x25 = sp + 400#64 ∧
        sm4.readReg64 .x27 = dispPtr ∧
        sm4.readReg64 .x28 = dispCap ∧
        sm4.readReg64 .fp = sp + 1408#64 ∧
        sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
        calleeSavedVRegs sm4 = calleeSavedVRegs s0)
      (P_mid :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
          (seedPtr ↦ₛ mkg.seed) ∗
          memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
            (seedCap.toNat - mkg.seed.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 16 ∗
        ((sp + 16#64) ↦₆₄ seedPtr) ∗
        memRegion (sp + 24#64) 4 ∗
        ((sp + 28#64) ↦₃₂ msgW) ∗
        ((sp + 32#64) ↦₆₄ x.locA) ∗
        ((sp + 40#64) ↦₆₄ seedCap) ∗
        ((sp + 48#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 320#64) 784 ∗
        ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
        memRegion (sp + 1116#64) 292 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        logOff img ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ?_ ?_
    · have hsp0 : memRegion sp 28 =
          memRegion sp 16 ∗ (memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4) := by
        have h1 := mr_cut_add sp 0 16 12 (by decide)
        simp only [BitVec.add_zero] at h1
        rw [h1, mr_cut_add sp 16 8 4 (by decide)]
      wp_conv_pre =>
        rw [mr_cut sp 436 4 48 52 440#64,
          memRegion_four (sp + 404#64),
          memRegion_four (sp + 436#64),
          memRegion_four (sp + 44#64)]
        simp only [sepConj_assoc]
      wp_pull_exists
      rename_i pad44 pad436 pad404
      have hmerge432 :
          ((sp + 432#64) ↦₃₂ mkg.counter) ∗ ((sp + 436#64) ↦₃₂ pad436) ⊢
          ((sp + 432#64) ↦₆₄ (pad436 ++ mkg.counter)) := by
        have hm := pointsTo32_merge64 (sp + 432#64) mkg.counter pad436
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
        rw [hm]; exact Entails.refl _
      have hmerge40 :
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ ((sp + 44#64) ↦₃₂ pad44) ⊢
          ((sp + 40#64) ↦₆₄ (pad44 ++ x.msg.counter)) := by
        have hm := pointsTo32_merge64 (sp + 40#64) x.msg.counter pad44
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
        rw [hm]; exact Entails.refl _
      refine SepWP.focus_weaken hmerge432 (by sep_focus) ?_
      refine SepWP.focus_weaken hmerge40 (by sep_focus) ?_
      wp_conv_pre =>
        rw [hsp0,
          mr_cut sp 440 8 40 48 448#64,
          mr_cut sp 448 8 32 40 456#64,
          mr_cut sp 456 8 24 32 464#64,
          mr_cut sp 464 8 16 24 472#64,
          mr_cut sp 472 8 8 16 480#64,
          mr_cut sp 488 616 304 920 1104#64,
          mr_cut sp 1104 8 296 304 1112#64,
          mr_cut sp 1112 8 288 296 1120#64,
          mr_cut sp 1120 8 280 288 1128#64,
          mr_cut sp 1128 8 272 280 1136#64,
          mr_cut sp 1136 8 264 272 1144#64,
          mr_cut sp 1144 8 256 264 1152#64,
          mr_cut sp 1152 8 248 256 1160#64,
          mr_cut sp 1160 8 240 248 1168#64,
          mr_cut sp 1168 112 128 240 1280#64,
          mr_cut sp 1280 8 120 128 1288#64,
          mr_cut sp 1288 8 112 120 1296#64,
          mr_cut sp 1296 8 104 112 1304#64,
          mr_cut sp 1304 8 96 104 1312#64]
        simp only [sepConj_assoc,
          memRegion_eight (sp + 16#64),
          memRegion_eight (sp + 440#64),
          memRegion_eight (sp + 448#64),
          memRegion_eight (sp + 456#64),
          memRegion_eight (sp + 464#64),
          memRegion_eight (sp + 472#64),
          memRegion_eight (sp + 480#64),
          memRegion_eight (sp + 1104#64),
          memRegion_eight (sp + 1112#64),
          memRegion_eight (sp + 1120#64),
          memRegion_eight (sp + 1128#64),
          memRegion_eight (sp + 1136#64),
          memRegion_eight (sp + 1144#64),
          memRegion_eight (sp + 1152#64),
          memRegion_eight (sp + 1160#64),
          memRegion_eight (sp + 1280#64),
          memRegion_eight (sp + 1288#64),
          memRegion_eight (sp + 1296#64),
          memRegion_eight (sp + 1304#64)]
      wp_pull_exists
      wp_steps
      have hsplit1112 :
          ((sp + 1112#64) ↦₆₄ (pad436 ++ mkg.counter)) ⊢
          ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 4 := by
        have hs := (pointsTo32_merge64 (sp + 1112#64) mkg.counter pad436).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
        rw [hs]
        exact sepConj_mono_right (pointsTo32_entails_memRegion (sp + 1116#64) pad436)
      refine SepWP.focus_weaken hsplit1112 (by sep_focus) ?_
      refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 400#64) 1#32) (by sep_focus) ?_
      refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 404#64) pad404) (by sep_focus) ?_
      have hm320 : memRegion (sp + 320#64) 784 =
          memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 4 ∗ (memRegion (sp + 404#64) 4 ∗
          (memRegion (sp + 408#64) 8 ∗ (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗
          (memRegion (sp + 432#64) 8 ∗ (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗
          (memRegion (sp + 456#64) 8 ∗ (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗
          (memRegion (sp + 480#64) 8 ∗ memRegion (sp + 488#64) 616)))))))))))) := by
        rw [mr_cut_add sp 320 80 704 (by decide),
          mr_cut_add sp 400 4 700 (by decide),
          mr_cut_add sp 404 4 696 (by decide),
          mr_cut_add sp 408 8 688 (by decide),
          mr_cut_add sp 416 8 680 (by decide),
          mr_cut_add sp 424 8 672 (by decide),
          mr_cut_add sp 432 8 664 (by decide),
          mr_cut_add sp 440 8 656 (by decide),
          mr_cut_add sp 448 8 648 (by decide),
          mr_cut_add sp 456 8 640 (by decide),
          mr_cut_add sp 464 8 632 (by decide),
          mr_cut_add sp 472 8 624 (by decide),
          mr_cut_add sp 480 8 616 (by decide)]
      have hm1116 : memRegion (sp + 1116#64) 292 =
          memRegion (sp + 1116#64) 4 ∗ (memRegion (sp + 1120#64) 8 ∗
          (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗
          (memRegion (sp + 1144#64) 8 ∗ (memRegion (sp + 1152#64) 8 ∗
          (memRegion (sp + 1160#64) 8 ∗ (memRegion (sp + 1168#64) 112 ∗
          (memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗
          (memRegion (sp + 1296#64) 8 ∗ (memRegion (sp + 1304#64) 8 ∗
           memRegion (sp + 1312#64) 96))))))))))) := by
        rw [mr_cut_add sp 1116 4 288 (by decide),
          mr_cut_add sp 1120 8 280 (by decide),
          mr_cut_add sp 1128 8 272 (by decide),
          mr_cut_add sp 1136 8 264 (by decide),
          mr_cut_add sp 1144 8 256 (by decide),
          mr_cut_add sp 1152 8 248 (by decide),
          mr_cut_add sp 1160 8 240 (by decide),
          mr_cut_add sp 1168 112 128 (by decide),
          mr_cut_add sp 1280 8 120 (by decide),
          mr_cut_add sp 1288 8 112 (by decide),
          mr_cut_add sp 1296 8 104 (by decide),
          mr_cut_add sp 1304 8 96 (by decide)]
      rw [hm320, hm1116]
      wp_done
    · intro sm4 hpc4 hrun4 hf_fr4 hsym4 hL4
        ⟨hx24_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx25_4, hx27_4, hx28_4,
         hfp4, hsp4, hsp_al4, htr4, hvregs4⟩
        hm4
      by_cases hcap : dispCap = 0
      · simp only [hcap, ↓reduceIte, emp_sepConj] at hm4
        subst hcap
        refine steps_of_sepWP hm4 hL4 hf_fr4 hsym4
          (mid := entry + bv% (1464))
          (RegMid := fun sf =>
            (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
            sf.readReg64 .x19 = x.ret ∧
            sf.readReg64 .x20 = sp + 320#64 ∧
            sf.readReg64 .x21 = x.ss ∧
            sf.readReg64 .x22 = x.msgA ∧
            sf.readReg64 .x23 = sp + 1280#64 ∧
            sf.readReg64 .x25 = sp + 400#64 ∧
            sf.readReg64 .fp = sp + 1408#64 ∧
            sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
            memRegion x.ret 48 ∗
            memRegion sp 16 ∗
            ((sp + 16#64) ↦₆₄ seedPtr) ∗
            memRegion (sp + 24#64) 4 ∗
            ((sp + 28#64) ↦₃₂ msgW) ∗
            ((sp + 32#64) ↦₆₄ x.locA) ∗
            ((sp + 40#64) ↦₆₄ seedCap) ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 320#64) 784 ∗
            ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
            ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
            logOff img ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_steps
          wp_done
        · intro sf hpcf hrunf hff hsymf _
            ⟨hx24_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩
            hmf
          subst hsp_def
          refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
          have hpc_s5 : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC img := by
            rw [hpcf]; unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC; rw [hentry]
          have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
            change sf.readReg64 .fp = s0.sp - 96#64
            rw [hfp_f]; exact (sp_fp_eq rfl).symm
          refine ⟨hpc_s5, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hff, hsymf, hvregs_f⟩,
            hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f,
            seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
          dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap]
          simp only [sepConj_assoc] at hmf ⊢
          arm64_sep_close
      · simp only [hcap, ↓reduceIte] at hm4
        have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
        refine steps_of_sepWP hm4 hL4 hf_fr4 hsym4
          (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
          (RegMid := fun sm5 =>
            sm5.readReg64 .x0 = dispPtr ∧
            sm5.readReg64 .x1 = dispCap ∧
            sm5.readReg64 .x2 = 1#64 ∧
            (sm5.readReg64 .x24).setWidth 32 = 1#32 ∧
            sm5.readReg64 .x19 = x.ret ∧
            sm5.readReg64 .x20 = sp + 320#64 ∧
            sm5.readReg64 .x21 = x.ss ∧
            sm5.readReg64 .x22 = x.msgA ∧
            sm5.readReg64 .x23 = sp + 1280#64 ∧
            sm5.readReg64 .x25 = sp + 400#64 ∧
            sm5.readReg64 .fp = sp + 1408#64 ∧
            sm5.readReg64 .lr = entry + bv% (1464) ∧
            sm5.sp = sp ∧ sm5.spAligned = true ∧ sm5.trace = s0.trace ∧
            calleeSavedVRegs sm5 = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            A.live dispPtr dispCap.toNat 1 ∗
            memRegion dispPtr dispCap.toNat ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
            memRegion x.ret 48 ∗
            memRegion sp 16 ∗
            ((sp + 16#64) ↦₆₄ seedPtr) ∗
            memRegion (sp + 24#64) 4 ∗
            ((sp + 28#64) ↦₃₂ msgW) ∗
            ((sp + 32#64) ↦₆₄ x.locA) ∗
            ((sp + 40#64) ↦₆₄ seedCap) ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 320#64) 784 ∗
            ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
            ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
            logOff img ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_conv_pre => simp only [sepConj_assoc]
          wp_steps
          refine SepWP.focus_weaken (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2)
            (by sep_focus) ?_
          wp_done
        · intro sm5 hpc5 hrun5 hf_fr5 hsym5 hL5
            ⟨hx0_5, hx1_5, hx2_5, hx24_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
             hx25_5, hfp5, hlr5, hsp5, hsp_al5, htr5, hvregs5⟩
            hm5
          have hstack_dealloc := stackAt_sub sp tryDecryptSubStack extHookStack (by decide) (by decide)
          have hpre_dealloc : sm5.mem ⊨
              ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
                (dispPtr, dispCap.toNat, 1) sm5 ∗
              ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
                trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
                (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                  (seedPtr ↦ₛ mkg.seed) ∗
                  memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                    (seedCap.toNat - mkg.seed.length)) ∗
                memRegion x.ret 48 ∗
                memRegion sp 16 ∗
                ((sp + 16#64) ↦₆₄ seedPtr) ∗
                memRegion (sp + 24#64) 4 ∗
                ((sp + 28#64) ↦₃₂ msgW) ∗
                ((sp + 32#64) ↦₆₄ x.locA) ∗
                ((sp + 40#64) ↦₆₄ seedCap) ∗
                ((sp + 48#64) ↦₆₄ x.remA) ∗
                memRegion (sp + 320#64) 784 ∗
                ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
                ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
                memRegion (sp + 1116#64) 292 ∗
                protocolAddressAt A x.rem x.remA ∗
                protocolAddressAt A x.loc x.locA ∗
                signalMessageAt A x.msgG x.msgA x.msg ∗
                CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
                logOff img ∗
                memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                  (tryDecryptSubStack - extHookStack) ∗
                tryDecryptSavedRegs s0.sp s0) ∗ R) := by
            dsimp only [rustDeallocExternSpecWithStack, Spec.inImage]
            rw [hsp5, sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨hf_fr5, hsym5⟩, ?_⟩
            rw [sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨hx0_5, by rw [hx1_5], by rw [hx2_5]; rfl,
              ⟨BitVec.toNat_pos_of_ne_zero hcap, ⟨0, rfl⟩, by omega⟩⟩, ?_⟩
            rw [hstack_dealloc] at hm5
            simp only [sepConj_assoc] at hm5 ⊢
            arm64_sep_close
          refine steps_call_out (dispPtr, dispCap.toNat, 1) hdealloc
            hpc5 hrun5 hsp_al5 hlr5 hf_fr5 hsym5 hL5 hpre_dealloc ?_ ?_
          · intro sf _ hpost
            dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost
            rw [sepConj_assoc] at hpost
            exact (not_satisfies_false_sepConj hpost).elim
          · intro sf hpcf hrunf hspf hsp_alf hcsf hff hsymf _ hpost
            rcases hcsf with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, _, _, _, hfp_cs, hvregs_cs⟩
            have hx19_f : sf.readReg64 .x19 = x.ret := hx19_cs.trans hx19_5
            have hx20_f : sf.readReg64 .x20 = sp + 320#64 := hx20_cs.trans hx20_5
            have hx21_f : sf.readReg64 .x21 = x.ss := hx21_cs.trans hx21_5
            have hx22_f : sf.readReg64 .x22 = x.msgA := hx22_cs.trans hx22_5
            have hx23_f : sf.readReg64 .x23 = sp + 1280#64 := hx23_cs.trans hx23_5
            have hx24_f : (sf.readReg64 .x24).setWidth 32 = 1#32 := by
              rw [hx24_cs]; exact hx24_5
            have hx25_f : sf.readReg64 .x25 = sp + 400#64 := hx25_cs.trans hx25_5
            have hfp_f_sp : sf.readReg64 .fp = sp + 1408#64 := hfp_cs.trans hfp5
            have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregs_cs.trans hvregs5
            have hsp_f : sf.sp = sp := hspf.trans hsp5
            dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost
            rw [hsp5, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
            rcases hpost with ⟨htr_f, hpost⟩
            have htr_f' : sf.trace = s0.trace := htr_f.trans htr5
            subst hsp_def
            refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
            have hpc_s5 : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC img := by
              rw [hpcf]; unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC; rw [hentry]
            have hfp_f : sf.readReg64 .x29 = s0.sp - 96#64 := by
              change sf.readReg64 .fp = s0.sp - 96#64
              rw [hfp_f_sp]; exact (sp_fp_eq rfl).symm
            refine ⟨hpc_s5, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f, htr_f', hff, hsymf, hvregs_f⟩,
              hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f,
              seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
            dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap]
            rw [hstack_dealloc]
            simp only [sepConj_assoc] at hpost ⊢
            arm64_sep_close

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.consumeMsgKey_cmk_err_x (img : Obj.Image) (_C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (_parse : UuidParser) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (e : SignalProtocolError)
    (draws : Nat) (R : SepProp) (s0 : State)
    {entry sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hne_panic : e ≠ .panic)
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = entry)
    (hentry_eq : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (sf2 : State)
    (hpcf2 : sf2.pc = entry + bv% (1144))
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (_hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hff2 : img.FrozenLoaded sf2)
    (hsymf2 : sf2.symtab = img.symtab)
    (hLf2 : (tripleRatchetProgAtExt img.base ext).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.error e) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf2 s' ∧
      ((e ≠ .panic ∧ ∃ trG'',
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧
         ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
         (s'.mem ⊨ anyHeap ∗ R))) := by
  decrypt_fetches_at_ext_cli hentry_eq 1144 64
  clear hentry_eq
  examples_hide_fetches
  have hm_err : sf2.mem ⊨
      (∃∗ w416 : BitVec 64, ∃∗ w424 : BitVec 64, ∃∗ w432 : BitVec 64,
       ∃∗ w440 : BitVec 64, ∃∗ w448 : BitVec 64, ∃∗ restHeap : SepProp,
        ⌜ErrWordsRel A e w416 w424 w432 w440 restHeap ∧ speTag e + 2#64 ≠ 0#64⌝ ∗
        ((sp + 400#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 404#64) 4 ∗
        ((sp + 408#64) ↦₆₄ speTag e) ∗
        ((sp + 416#64) ↦₆₄ w416) ∗
        ((sp + 424#64) ↦₆₄ w424) ∗
        ((sp + 432#64) ↦₆₄ w432) ∗
        ((sp + 440#64) ↦₆₄ w440) ∗
        ((sp + 448#64) ↦₆₄ w448) ∗
        memRegion (sp + 456#64) 32 ∗
        restHeap) ∗
      ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 56 ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 488#64) 920 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        logOff img ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ∗ R) := by
    have hsp56 : memRegion sp 56 =
        memRegion sp 28 ∗ (memRegion (sp + 28#64) 4 ∗ (memRegion (sp + 32#64) 8 ∗
        (memRegion (sp + 40#64) 4 ∗ (memRegion (sp + 44#64) 4 ∗ memRegion (sp + 48#64) 8)))) := by
      have h1 := mr_cut_add sp 0 28 28 (by decide)
      simp only [BitVec.add_zero] at h1
      rw [h1,
        mr_cut_add sp 28 4 24 (by decide),
        mr_cut_add sp 32 8 16 (by decide),
        mr_cut_add sp 40 4 12 (by decide),
        mr_cut_add sp 44 4 8 (by decide)]
    rw [hsp56]
    refine Satisfies.mono (sepConj_mono_left (resultAt_err_unpack A sp e)) ?_
    have hm_post2' : sf2.mem ⊨
        (((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ ((sp + 48#64) ↦₆₄ x.remA)) ∗
        (consumeMessageKeyResultAt A (sp + 400#64) (.error e) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
         (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
           (dispPtr ↦ₛ dispBs) ∗
           memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
         memRegion x.ret 48 ∗
         memRegion sp 28 ∗
         memRegion (sp + 44#64) 4 ∗
         memRegion (sp + 320#64) 80 ∗
         memRegion (sp + 488#64) 920 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
         logOff img ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool ∗ R) := by
      simp only [sepConj_assoc] at hm_post2 ⊢
      arm64_sep_close
    have hm_post2'' := Satisfies.mono (sepConj_mono_left (sepConj_mono
      (pointsTo32_entails_memRegion (sp + 28#64) msgW)
      (sepConj_mono (pts64_to_mr (sp + 32#64) x.locA)
        (sepConj_mono (pointsTo32_entails_memRegion (sp + 40#64) x.msg.counter)
          (pts64_to_mr (sp + 48#64) x.remA))))) hm_post2'
    change sf2.mem ⊨ _ at hm_post2'' ⊢
    simp only [sepConj_assoc] at hm_post2'' ⊢
    arm64_sep_close
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm_err
  rcases hm_err with ⟨w416, w424, w432, w440, w448, restHeap, hm_err⟩
  rw [satisfies_pure_sepConj] at hm_err
  rcases hm_err with ⟨⟨hrel, htag_ne⟩, hm_err⟩
  simp only [← sepConj_assoc] at hm_err
  refine steps_of_sepWP hm_err hLf2 hff2 hsymf2
    (mid := entry + bv% (1180))
    (RegMid := fun sm3 =>
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x26 = speTag e ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 56 ∗
      memRegion (sp + 320#64) 40 ∗
      speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
      memRegion (sp + 400#64) 1008 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 40 40 80 360#64,
        mr_cut sp 360 8 32 40 368#64,
        mr_cut sp 368 8 24 32 376#64,
        mr_cut sp 376 8 16 24 384#64,
        mr_cut sp 384 8 8 16 392#64,
        mr_cut sp 488 792 128 920 1280#64,
        mr_cut sp 1280 8 120 128 1288#64,
        mr_cut sp 1288 8 112 120 1296#64,
        mr_cut sp 1296 8 104 112 1304#64,
        mr_cut sp 1304 8 96 104 1312#64]
      simp only [sepConj_assoc,
        memRegion_eight (sp + 360#64),
        memRegion_eight (sp + 368#64),
        memRegion_eight (sp + 376#64),
        memRegion_eight (sp + 384#64),
        memRegion_eight (sp + 392#64),
        memRegion_eight (sp + 1280#64),
        memRegion_eight (sp + 1288#64),
        memRegion_eight (sp + 1296#64),
        memRegion_eight (sp + 1304#64)]
    wp_pull_exists
    have htag_beq : (speTag e + 2#64 == 0#64) = false := beq_false_of_ne htag_ne
    have htag_beq0 : (speTag e + 2#64 + 0#64 == 0#64) = false := by
      rw [BitVec.add_zero]; exact htag_beq
    wp_steps
    refine SepWP.focus_weaken
      (speBodyAt_err_pack A sp e w416 w424 w432 w440 w448 restHeap hrel)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (pointsTo32_entails_memRegion (sp + 400#64) 2#32) (by sep_focus) ?_
    have hm400 : memRegion (sp + 400#64) 1008 =
        memRegion (sp + 400#64) 4 ∗ (memRegion (sp + 404#64) 4 ∗ (memRegion (sp + 408#64) 8 ∗
        (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗ (memRegion (sp + 432#64) 8 ∗
        (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 32 ∗
        (memRegion (sp + 488#64) 792 ∗ (memRegion (sp + 1280#64) 8 ∗
        (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
        (memRegion (sp + 1304#64) 8 ∗ memRegion (sp + 1312#64) 96))))))))))))) := by
      rw [mr_cut_add sp 400 4 1004 (by decide),
        mr_cut_add sp 404 4 1000 (by decide),
        mr_cut_add sp 408 8 992 (by decide),
        mr_cut_add sp 416 8 984 (by decide),
        mr_cut_add sp 424 8 976 (by decide),
        mr_cut_add sp 432 8 968 (by decide),
        mr_cut_add sp 440 8 960 (by decide),
        mr_cut_add sp 448 8 952 (by decide),
        mr_cut_add sp 456 32 920 (by decide),
        mr_cut_add sp 488 792 128 (by decide),
        mr_cut_add sp 1280 8 120 (by decide),
        mr_cut_add sp 1288 8 112 (by decide),
        mr_cut_add sp 1296 8 104 (by decide),
        mr_cut_add sp 1304 8 96 (by decide)]
    rw [hm400]
    wp_done
  · intro sm3 hpc3 hrun3 hf_fr3 hsym3 hL3
      ⟨hx19_3, hx20_3, hx26_3, hx27_3, hx28_3, hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    have herr_tail : ∀ st4 : State,
        st4.pc = entry + bv% (1200) → st4.status = .Running →
        st4.sp = sp → st4.spAligned = true →
        st4.readReg64 .fp = sp + 1408#64 → st4.trace = s0.trace →
        calleeSavedVRegs st4 = calleeSavedVRegs s0 →
        img.FrozenLoaded st4 → st4.symtab = img.symtab →
        (tripleRatchetProgAtExt img.base ext).CodeLoaded st4.mem →
        st4.readReg64 .x19 = x.ret →
        st4.readReg64 .x20 = sp + 320#64 →
        st4.readReg64 .x26 = speTag e →
        (st4.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
           memRegion x.ret 48 ∗
           memRegion sp 56 ∗
           memRegion (sp + 320#64) 40 ∗
           speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
           memRegion (sp + 400#64) 1008 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R) →
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) st4 s' ∧
          ((e ≠ .panic ∧ ∃ trG'',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
      intro st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hff4 hsym4 hL4 hx19_4 hx20_4 hx26_4 hm4
      refine steps_of_sepWP hm4 hL4 hff4 hsym4
        (mid := entry + bv% (780))
        (RegMid := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = sp + 320#64 ∧
          sf.readReg64 .x26 = speTag e ∧
          sf.readReg64 .fp = sp + 1408#64 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro sf hpcf hrunf hff hsymf _ ⟨hx19_f, hx20_f, hx26_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩ hmf
        subst hsp_def
        refine ⟨sf, .refl _, Or.inl ⟨hne_panic, trG', ?_⟩⟩
        have hpc_err : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img := by
          rw [hpcf]; unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC; rw [hentry]
        have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
          change sf.readReg64 .fp = s0.sp - 96#64
          rw [hfp_f]; exact (sp_fp_eq rfl).symm
        refine ⟨hpc_err, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hff, hsymf, hvregs_f⟩,
          hx19_f, hx20_f, hx26_f, ?_⟩
        dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap]
        simp only [sepConj_assoc] at hmf ⊢
        arm64_sep_close
    by_cases hcap : dispCap = 0
    · simp only [hcap, ↓reduceIte, emp_sepConj] at hm3
      subst hcap
      refine steps_of_sepWP hm3 hL3 hf_fr3 hsym3
        (mid := entry + bv% (1200))
        (RegMid := fun st4 =>
          st4.readReg64 .x19 = x.ret ∧
          st4.readReg64 .x20 = sp + 320#64 ∧
          st4.readReg64 .x26 = speTag e ∧
          st4.readReg64 .fp = sp + 1408#64 ∧
          st4.sp = sp ∧ st4.spAligned = true ∧ st4.trace = s0.trace ∧
          calleeSavedVRegs st4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro st4 hpc4 hrun4 hff4 hsym4 hL4 ⟨hx19_4, hx20_4, hx26_4, hfp4, hsp4, hsp_al4, htr4, hvregs4⟩ hm4
        exact herr_tail st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hff4 hsym4 hL4 hx19_4 hx20_4 hx26_4 hm4
    · simp only [hcap, ↓reduceIte] at hm3
      have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
      refine steps_of_sepWP hm3 hL3 hf_fr3 hsym3
        (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
        (RegMid := fun sm4 =>
          sm4.readReg64 .x0 = dispPtr ∧
          sm4.readReg64 .x1 = dispCap ∧
          sm4.readReg64 .x2 = 1#64 ∧
          sm4.readReg64 .x19 = x.ret ∧
          sm4.readReg64 .x20 = sp + 320#64 ∧
          sm4.readReg64 .x26 = speTag e ∧
          sm4.readReg64 .fp = sp + 1408#64 ∧
          sm4.readReg64 .lr = entry + bv% (1200) ∧
          sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
          calleeSavedVRegs sm4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          A.live dispPtr dispCap.toNat 1 ∗
          memRegion dispPtr dispCap.toNat ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps
        refine SepWP.focus_weaken (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2)
          (by sep_focus) ?_
        wp_done
      · intro sm4 hpc4 hrun4 hf_fr4 hsym4 hL4
          ⟨hx0_4, hx1_4, hx2_4, hx19_4, hx20_4, hx26_4, hfp4, hlr4, hsp4, hsp_al4, htr4, hvregs4⟩
          hm4
        have hstack_dealloc := stackAt_sub sp tryDecryptSubStack extHookStack (by decide) (by decide)
        have hpre_dealloc : sm4.mem ⊨
            ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
              (dispPtr, dispCap.toNat, 1) sm4 ∗
            ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
              memRegion x.ret 48 ∗
              memRegion sp 56 ∗
              memRegion (sp + 320#64) 40 ∗
              speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
              memRegion (sp + 400#64) 1008 ∗
              protocolAddressAt A x.rem x.remA ∗
              protocolAddressAt A x.loc x.locA ∗
              signalMessageAt A x.msgG x.msgA x.msg ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
              logOff img ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - extHookStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [rustDeallocExternSpecWithStack, Spec.inImage]
          rw [hsp4, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hf_fr4, hsym4⟩, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_4, by rw [hx1_4], by rw [hx2_4]; rfl,
            ⟨BitVec.toNat_pos_of_ne_zero hcap, ⟨0, rfl⟩, by omega⟩⟩, ?_⟩
          rw [hstack_dealloc] at hm4
          simp only [sepConj_assoc] at hm4 ⊢
          arm64_sep_close
        refine steps_call_out (dispPtr, dispCap.toNat, 1) hdealloc
          hpc4 hrun4 hsp_al4 hlr4 hf_fr4 hsym4 hL4 hpre_dealloc ?_ ?_
        · intro sf _ hpost
          dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost
          rw [sepConj_assoc] at hpost
          exact (not_satisfies_false_sepConj hpost).elim
        · intro st5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hff5 hsym5 hL5 hpost5
          rcases hcs5 with ⟨hx19_cs5, hx20_cs5, _, _, _, _, _, hx26_cs5, _, _, hfp_cs5, hvregs_cs5⟩
          have hx19_5 : st5.readReg64 .x19 = x.ret := hx19_cs5.trans hx19_4
          have hx20_5 : st5.readReg64 .x20 = sp + 320#64 := hx20_cs5.trans hx20_4
          have hx26_5 : st5.readReg64 .x26 = speTag e := hx26_cs5.trans hx26_4
          have hfp5 : st5.readReg64 .fp = sp + 1408#64 := hfp_cs5.trans hfp4
          have hvregs5 : calleeSavedVRegs st5 = calleeSavedVRegs s0 := hvregs_cs5.trans hvregs4
          have hsp5' : st5.sp = sp := hsp5.trans hsp4
          dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost5
          rw [hsp4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost5
          rcases hpost5 with ⟨htr5, hpost5⟩
          have htr5' : st5.trace = s0.trace := htr5.trans htr4
          refine herr_tail st5 hpc5 hrun5 hsp5' hsp_al5 hfp5 htr5' hvregs5 hff5 hsym5 hL5
            hx19_5 hx20_5 hx26_5 ?_
          rw [hstack_dealloc]
          simp only [sepConj_assoc] at hpost5 ⊢
          arm64_sep_close

end KeyDeriveCallees

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_ext_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S4SpecExt_trap img C A ctl uuidTryParse S ext := by
  intro hloads hS hcmk x trG tr st1 ck draws R s0 s hS4 hL
  rcases hS4 with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hfp, htrace, hfrozen, hsym, hvregs⟩,
    hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hmem⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
  change CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName at hentry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC at hpc
  rw [show (0x3e4#64 : BitVec 64) = 996#64 by rfl] at hpc
  rw [hentry] at hpc
  have hentry_eq := (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq img.base ext).symm
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  have haddrDisplay := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_ext_trap hS hentry_eq
  have hdealloc := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_ext hS.toAllocContracts hentry_eq
  have hcmk_call := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.cmk_ok_at_entry hcmk hentry_eq
  clear hcmk
  decrypt_fetches_at_ext_cli hentry_eq 996 96
  decrypt_fetches_at_ext_cli hentry_eq 1092 52
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hfp
  rw [hsp29_eq] at hfp
  clear hsp29_eq
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx12 hx20 hx23 hx25 hfp hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hdrop, htake, hfull⟩ := split_chainKeyBytes ck
  let Out : State → Prop := fun s' =>
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      (∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
      (s'.status = .Panicked ∧
        (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))
    | (.error e, r2) =>
      (e ≠ .panic ∧ ∃ trG',
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
      (s'.status = .Panicked ∧
        ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
        (s'.mem ⊨ anyHeap ∗ R))
  have hOut_split : ∀ (prog : Program) (sm : State),
      (∃ s', Steps prog sm s' ∧ Out s') →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps prog sm s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps prog sm s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
    intro prog sm ⟨s', hst, hout⟩
    dsimp only [Out] at hout
    split at hout <;> exact ⟨s', hst, hout⟩
  apply hOut_split
  have hmem0 : s.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 32 ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 368 ∗
       ((sp + 688#64) ↦₆₄ (w6 ++ w5)) ∗
       ((sp + 696#64) ↦₆₄ (w8 ++ w7)) ∗
       ((sp + 704#64) ↦₆₄ (w1 ++ w0)) ∗
       ((sp + 712#64) ↦₆₄ (w3 ++ w2)) ∗
       ((sp + 720#64) ↦₃₂ w4) ∗
       memRegion (sp + 724#64) 684 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R := by
    have hd := hdrop (sp + 688#64)
    have ht := htake (sp + 704#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hd ht
    rw [hd, ht] at hmem
    simp only [sepConj_assoc] at hmem
    simp only [sepConj_assoc]
    exact hmem
  refine steps_of_sepWP hmem0 hL hfrozen hsym
    (mid := entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
    (RegMid := fun sm1 =>
      sm1.readReg64 .x1 = sp + 1024#64 ∧
      sm1.readReg64 .x19 = x.ret ∧
      sm1.readReg64 .x20 = sp + 320#64 ∧
      sm1.readReg64 .x21 = x.ss ∧
      sm1.readReg64 .x22 = x.msgA ∧
      sm1.readReg64 .x23 = sp + 1280#64 ∧
      (sm1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
      sm1.readReg64 .x25 = sp + 400#64 ∧
      sm1.readReg64 .fp = sp + 1408#64 ∧
      sm1.readReg64 .lr = entry + bv% (1092) ∧
      sm1.sp = sp ∧ sm1.spAligned = true ∧ sm1.trace = s0.trace ∧
      calleeSavedVRegs sm1 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      memRegion x.ret 48 ∗
      memRegion sp 32 ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 416 ∗
      ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
      memRegion (sp + 772#64) 204 ∗
      vecU8 A (sp + 976#64) [] ∗
      memRegion (sp + 1000#64) 24 ∗
      ((sp + 1024#64) ↦₆₄ (sp + 976#64)) ∗
      memRegion (sp + 1032#64) 40 ∗
      memRegion (sp + 1072#64) 336 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 96 272 368 416#64,
        mr_cut sp 416 4 268 272 420#64,
        mr_cut sp 420 8 260 268 428#64,
        mr_cut sp 428 8 252 260 436#64,
        mr_cut sp 724 12 672 684 736#64,
        mr_cut sp 736 8 664 672 744#64,
        mr_cut sp 744 8 656 664 752#64,
        mr_cut sp 752 8 648 656 760#64,
        mr_cut sp 760 8 640 648 768#64,
        mr_cut sp 768 4 636 640 772#64,
        mr_cut sp 772 204 432 636 976#64,
        mr_cut sp 976 8 424 432 984#64,
        mr_cut sp 984 8 416 424 992#64,
        mr_cut sp 992 8 408 416 1000#64,
        mr_cut sp 1000 8 400 408 1008#64,
        mr_cut sp 1008 8 392 400 1016#64,
        mr_cut sp 1016 8 384 392 1024#64,
        mr_cut sp 1024 8 376 384 1032#64,
        mr_cut sp 1032 8 368 376 1040#64,
        mr_cut sp 1040 8 360 368 1048#64,
        mr_cut sp 1048 8 352 360 1056#64,
        mr_cut sp 1056 8 344 352 1064#64,
        mr_cut sp 1064 8 336 344 1072#64]
      simp only [sepConj_assoc,
        memRegion_four (sp + 416#64),
        memRegion_eight (sp + 420#64),
        memRegion_eight (sp + 428#64),
        memRegion_eight (sp + 736#64),
        memRegion_eight (sp + 744#64),
        memRegion_eight (sp + 752#64),
        memRegion_eight (sp + 760#64),
        memRegion_four (sp + 768#64),
        memRegion_eight (sp + 976#64),
        memRegion_eight (sp + 984#64),
        memRegion_eight (sp + 992#64),
        memRegion_eight (sp + 1000#64),
        memRegion_eight (sp + 1008#64),
        memRegion_eight (sp + 1016#64),
        memRegion_eight (sp + 1024#64),
        memRegion_eight (sp + 1032#64),
        memRegion_eight (sp + 1040#64),
        memRegion_eight (sp + 1048#64),
        memRegion_eight (sp + 1056#64),
        memRegion_eight (sp + 1064#64)]
    wp_pull_exists
    wp_steps
    refine SepWP.focus_weaken (realign_416_436 sp w4 w5 w6 w7 w8) (by sep_focus) ?_
    wp_steps
    have hck_fold :
        ((sp + 736#64) ↦₆₄ (w1 ++ w0)) ∗ ((sp + 744#64) ↦₆₄ (w3 ++ w2)) ∗
        ((sp + 752#64) ↦₆₄ (w5 ++ w4)) ∗ ((sp + 760#64) ↦₆₄ (w7 ++ w6)) ∗
        ((sp + 768#64) ↦₃₂ w8) ⊢
        ((sp + 736#64) ↦ₛ chainKeyBytes ck) := by
      have hf := (hfull (sp + 736#64)).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hf ⊢
      rw [hf]
      exact Entails.refl _
    refine SepWP.focus_weaken hck_fold (by sep_focus) ?_
    have hv_empty := empty_vecU8_intro A (sp + 976#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv_empty
    refine SepWP.focus_weaken hv_empty (by sep_focus) ?_
    refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 432#64) w8) (by sep_focus) ?_
    refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 720#64) w4) (by sep_focus) ?_
    have hm320 : memRegion (sp + 320#64) 416 =
        memRegion (sp + 320#64) 96 ∗ (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗
        (memRegion (sp + 432#64) 4 ∗ (memRegion (sp + 436#64) 252 ∗ (memRegion (sp + 688#64) 8 ∗
        (memRegion (sp + 696#64) 8 ∗ (memRegion (sp + 704#64) 8 ∗ (memRegion (sp + 712#64) 8 ∗
        (memRegion (sp + 720#64) 4 ∗ memRegion (sp + 724#64) 12))))))))) := by
      rw [mr_cut_add sp 320 96 320 (by decide),
        mr_cut_add sp 416 8 312 (by decide),
        mr_cut_add sp 424 8 304 (by decide),
        mr_cut_add sp 432 4 300 (by decide),
        mr_cut_add sp 436 252 48 (by decide),
        mr_cut_add sp 688 8 40 (by decide),
        mr_cut_add sp 696 8 32 (by decide),
        mr_cut_add sp 704 8 24 (by decide),
        mr_cut_add sp 712 8 16 (by decide),
        mr_cut_add sp 720 4 12 (by decide)]
    have hm1000 : memRegion (sp + 1000#64) 24 =
        memRegion (sp + 1000#64) 8 ∗ (memRegion (sp + 1008#64) 8 ∗ memRegion (sp + 1016#64) 8) := by
      rw [mr_cut_add sp 1000 8 16 (by decide), mr_cut_add sp 1008 8 8 (by decide)]
    have hm1032 : memRegion (sp + 1032#64) 40 =
        memRegion (sp + 1032#64) 8 ∗ (memRegion (sp + 1040#64) 8 ∗ (memRegion (sp + 1048#64) 8 ∗
        (memRegion (sp + 1056#64) 8 ∗ memRegion (sp + 1064#64) 8))) := by
      rw [mr_cut_add sp 1032 8 32 (by decide),
        mr_cut_add sp 1040 8 24 (by decide),
        mr_cut_add sp 1048 8 16 (by decide),
        mr_cut_add sp 1056 8 8 (by decide)]
    rw [hm320, hm1000, hm1032]
    wp_done
  · intro sm1 hpc1 hrun1 hf_fr1 hsym1 hL1
      ⟨hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hfp1, hlr1, hsp1, hsp_al1, htr1, hvregs1⟩
      hm1
    have hm1032_split : memRegion (sp + 1032#64) 40 =
        (∃∗ vt : BitVec 64, (sp + 1032#64) ↦₆₄ vt) ∗ memRegion (sp + 1040#64) 32 := by
      rw [mr_cut_add sp 1032 8 32 (by decide), memRegion_eight (sp + 1032#64)]
    rw [hm1032_split] at hm1
    simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hm1
    rcases hm1 with ⟨vt, hm1⟩
    have hpre_disp : sm1.mem ⊨
        (addrDisplaySpec A).pre (sp + 1024#64, sp + 976#64, vt, []) sm1 ∗
        ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion sp 32 ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 416 ∗
          ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
          memRegion (sp + 772#64) 204 ∗
          memRegion (sp + 1000#64) 24 ∗
          memRegion (sp + 1040#64) 32 ∗
          memRegion (sp + 1072#64) 336 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - addrDisplayStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [addrDisplaySpec]
      rw [hsp1]
      rw [stackAt_sub sp tryDecryptSubStack addrDisplayStack] at hm1
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hx1_1, ?_⟩
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm1 ⊢
      arm64_sep_close
    refine steps_call_out (sp + 1024#64, sp + 976#64, vt, []) haddrDisplay
      hpc1 hrun1 hsp_al1 hlr1 hf_fr1 hsym1 hL1 hpre_disp ?_ ?_
    ·
      intro sf hpan hpost
      dsimp only [addrDisplaySpec] at hpost
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨⟨halloc, htr_sub⟩, hpost⟩
      have halloc0 : allocFailedIn s0 sf := by
        unfold allocFailedIn at halloc ⊢; rw [← htr1]; exact halloc
      have htr0 : s0.trace <+: sf.trace := by rw [← htr1]; exact htr_sub
      rw [← sepConj_assoc] at hpost
      have hany : sf.mem ⊨ anyHeap ∗ R :=
        Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpost
      dsimp only [Out]
      split
      · refine Or.inr ⟨hpan, ?_⟩
        dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨Or.inr (Or.inr halloc0), htr0⟩, hany⟩
      · exact Or.inr ⟨hpan, ⟨Or.inr halloc0, htr0⟩, hany⟩
    ·
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      rcases hcsf1 with ⟨hx19_cs1, hx20_cs1, hx21_cs1, hx22_cs1, hx23_cs1, hx24_cs1, hx25_cs1, _, _, _, hfp_cs1, hvregs_cs1⟩
      have hx19_f1 : sf1.readReg64 .x19 = x.ret := hx19_cs1.trans hx19_1
      have hx20_f1 : sf1.readReg64 .x20 = sp + 320#64 := hx20_cs1.trans hx20_1
      have hx21_f1 : sf1.readReg64 .x21 = x.ss := hx21_cs1.trans hx21_1
      have hx22_f1 : sf1.readReg64 .x22 = x.msgA := hx22_cs1.trans hx22_1
      have hx23_f1 : sf1.readReg64 .x23 = sp + 1280#64 := hx23_cs1.trans hx23_1
      have hx24_f1 : (sf1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
        rw [hx24_cs1]; exact hx24_1
      have hx25_f1 : sf1.readReg64 .x25 = sp + 400#64 := hx25_cs1.trans hx25_1
      have hfp_f1 : sf1.readReg64 .fp = sp + 1408#64 := hfp_cs1.trans hfp1
      have hvregs_f1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := hvregs_cs1.trans hvregs1
      have hsp_f1 : sf1.sp = sp := hspf1.trans hsp1
      dsimp only [addrDisplaySpec] at hpost1
      rw [hsp1] at hpost1
      simp only [vecU8, vecU8At, vecHeader, sepConj_assoc, sepExists_sepConj_left,
        sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨dispBs, dispCap, dispPtr, hpost1⟩
      rw [satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨hw0_f1, htr_f1⟩, hpost1⟩
      have htr_f1' : sf1.trace = s0.trace := htr_f1.trans htr1
      simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨hdisp1, hdisp2, _hdisp3⟩, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG tr ∗
           (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
             (dispPtr ↦ₛ dispBs) ∗
             memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
           ((sp + 976#64) ↦₆₄ dispCap) ∗
           ((sp + 984#64) ↦₆₄ dispPtr) ∗
           ((sp + 992#64) ↦₆₄ BitVec.ofNat 64 dispBs.length) ∗
           ((sp + 1024#64) ↦₆₄ (sp + 976#64)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 32 ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 44#64) 4 ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 416 ∗
           ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
           memRegion (sp + 772#64) 204 ∗
           memRegion (sp + 1000#64) 24 ∗
           memRegion (sp + 1032#64) 40 ∗
           memRegion (sp + 1072#64) 336 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [hm1032_split, stackAt_sub sp tryDecryptSubStack addrDisplayStack]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
          sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1 ⊢
        refine ⟨vt, ?_⟩
        arm64_sep_close
      let msgW : BitVec 32 := (sf1.readReg64 .x24).setWidth 32
      have hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType := by
        have h8 : msgW.setWidth 8 = (sf1.readReg64 .x24).setWidth 8 :=
          BitVec.setWidth_setWidth_of_le (sf1.readReg64 .x24) (by decide)
        exact h8.trans hx24_f1
      refine steps_of_sepWP hpost1' hLf1 hff1 hsymf1
        (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
        (RegMid := fun sm2 =>
          sm2.readReg64 .x0 = sp + 56#64 ∧
          sm2.readReg64 .x1 = x.msgA + 56#64 ∧
          sm2.readReg64 .x2 = sp + 736#64 ∧
          (sm2.readReg64 .x3).setWidth 32 = x.msg.counter ∧
          (sm2.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧
          sm2.readReg64 .x8 = sp + 400#64 ∧
          sm2.readReg64 .x19 = x.ret ∧
          sm2.readReg64 .x20 = sp + 320#64 ∧
          sm2.readReg64 .x21 = x.ss ∧
          sm2.readReg64 .x22 = x.msgA ∧
          sm2.readReg64 .x23 = sp + 1280#64 ∧
          sm2.readReg64 .x25 = sp + 400#64 ∧
          sm2.readReg64 .x27 = dispPtr ∧
          sm2.readReg64 .x28 = dispCap ∧
          sm2.readReg64 .fp = sp + 1408#64 ∧
          sm2.readReg64 .lr = entry + bv% (1144) ∧
          sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.trace = s0.trace ∧
          calleeSavedVRegs sm2 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
          (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
            (dispPtr ↦ₛ dispBs) ∗
            memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
          memRegion x.ret 48 ∗
          memRegion sp 28 ∗
          ((sp + 28#64) ↦₃₂ msgW) ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 80 ∗
          memRegion (sp + 400#64) 88 ∗
          memRegion (sp + 488#64) 248 ∗
          ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
          memRegion (sp + 772#64) 636 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · have hsp0 : memRegion sp 32 = memRegion sp 28 ∗ memRegion (sp + 28#64) 4 := by
          have hm := mr_cut_add sp 0 28 4 (by decide)
          simp only [BitVec.add_zero] at hm
          exact hm
        wp_conv_pre =>
          rw [hsp0, memRegion_four (sp + 28#64),
            mr_cut sp 320 80 336 416 400#64,
            mr_cut sp 400 88 248 336 488#64]
          simp only [sepConj_assoc]
        wp_pull_exists
        wp_steps
        have hm772 : memRegion (sp + 772#64) 636 =
            memRegion (sp + 772#64) 204 ∗ (memRegion (sp + 976#64) 8 ∗ (memRegion (sp + 984#64) 8 ∗
            (memRegion (sp + 992#64) 8 ∗ (memRegion (sp + 1000#64) 24 ∗
            (memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 40 ∗
             memRegion (sp + 1072#64) 336)))))) := by
          rw [mr_cut_add sp 772 204 432 (by decide),
            mr_cut_add sp 976 8 424 (by decide),
            mr_cut_add sp 984 8 416 (by decide),
            mr_cut_add sp 992 8 408 (by decide),
            mr_cut_add sp 1000 24 384 (by decide),
            mr_cut_add sp 1024 8 376 (by decide),
            mr_cut_add sp 1032 40 336 (by decide)]
        rw [hm772]
        dsimp only [msgW]
        wp_done
      · intro sm2 hpc2 hrun2 hf_fr2 hsym2 hL2
          ⟨hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2,
           hx23_2, hx25_2, hx27_2, hx28_2, hfp2, hlr2, hsp2, hsp_al2, htr2, hvregs2⟩
          hm2
        let cmkX : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost :=
          { self := sp + 56#64
            G := trG.ratchet
            st := tr.ratchet
            their := x.msg.senderRatchetKey
            theirA := x.msgA + 56#64
            ck := ck
            ckA := sp + 736#64
            counter := x.msg.counter
            msgType := x.msgType
            ret := sp + 400#64 }
        have hcmk_model : cmkX.model C.F =
            Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
              x.msgType) tr.ratchet := rfl
        have hstack_cmk := stackAt_sub sp tryDecryptSubStack CryptoVerification.LibsignalSession.cmkStack
          (by decide) (by decide)
        rw [trAt_split_ratchet, signalMessageAt_split_their] at hm2
        dsimp only [logOff] at hm2
        simp only [sepConj_assoc] at hm2
        rw [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm2
        rcases hm2 with ⟨hclamp, hm2⟩
        have hpre_cmk : sm2.mem ⊨
            (CryptoVerification.LibsignalSession.consumeMessageKeySpec C.F A img).pre cmkX sm2 ∗
            ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trNonRatchetAt A sp trG tr ∗
              (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
                (dispPtr ↦ₛ dispBs) ∗
                memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
              memRegion x.ret 48 ∗
              memRegion sp 28 ∗
              ((sp + 28#64) ↦₃₂ msgW) ∗
              ((sp + 32#64) ↦₆₄ x.locA) ∗
              ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
              memRegion (sp + 44#64) 4 ∗
              ((sp + 48#64) ↦₆₄ x.remA) ∗
              memRegion (sp + 320#64) 80 ∗
              memRegion (sp + 488#64) 248 ∗
              memRegion (sp + 772#64) 636 ∗
              protocolAddressAt A x.rem x.remA ∗
              protocolAddressAt A x.loc x.locA ∗
              signalMessageNonTheirAt A x.msgG x.msgA x.msg ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - CryptoVerification.LibsignalSession.cmkStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [CryptoVerification.LibsignalSession.consumeMessageKeySpec, Spec.inImage, cmkX]
          rw [hsp2, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hf_fr2, hsym2⟩, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx8_2⟩, ?_⟩
          rw [hstack_cmk] at hm2
          simp only [sepConj_assoc] at hm2 ⊢
          arm64_sep_close
        refine steps_call_out cmkX hcmk_call
          hpc2 hrun2 hsp_al2 hlr2 hf_fr2 hsym2 hL2 hpre_cmk ?_ ?_
        ·
          intro sf hpan hpost
          dsimp only [CryptoVerification.LibsignalSession.consumeMessageKeySpec, Spec.inImage] at hpost
          rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
          rcases hpost with ⟨⟨hpan_or, htr_sub⟩, hpost⟩
          have htr0 : s0.trace <+: sf.trace := by rw [← htr2]; exact htr_sub
          rw [← sepConj_assoc] at hpost
          have hany : sf.mem ⊨ anyHeap ∗ R :=
            Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpost
          rw [hcmk_model] at hpan_or
          dsimp only [Out]
          split
          · next mkg r2 hmod =>
            rw [hmod] at hpan_or
            rcases hpan_or with hbad | halloc
            · cases hbad
            · have halloc0 : allocFailedIn s0 sf := by
                unfold allocFailedIn at halloc ⊢; rw [← htr2]; exact halloc
              refine Or.inr ⟨hpan, ?_⟩
              dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
              rw [sepConj_assoc, satisfies_pure_sepConj]
              exact ⟨⟨Or.inr (Or.inr halloc0), htr0⟩, hany⟩
          · next e r2 hmod =>
            rw [hmod] at hpan_or
            refine Or.inr ⟨hpan, ⟨?_, htr0⟩, hany⟩
            rcases hpan_or with hbad | halloc
            · exact Or.inl (Except.error.inj hbad)
            · unfold allocFailedIn at halloc ⊢; rw [← htr2]; exact Or.inr halloc
        ·
          intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hff2 hsymf2 hLf2 hpost2
          dsimp only [CryptoVerification.LibsignalSession.consumeMessageKeySpec, Spec.inImage] at hpost2
          rw [hsp2, hcmk_model] at hpost2
          simp only [cmkX, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
            satisfies_sepExists] at hpost2
          rcases hpost2 with ⟨rG', hpost2⟩
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨⟨hnot_panic, htr_f2⟩, hpost2⟩
          have htr_f2' : sf2.trace = s0.trace := htr_f2.trans htr2
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨_, hpost2⟩
          let r2 := (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
            x.msg.counter x.msgType) tr.ratchet).2
          let trG' : TrGhost := { trG with ratchet := rG' }
          have hclamp2 : ∀ sc, r2.senderChain = some sc →
              Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
            intro sc hsc
            rw [consumeMessageKey_senderChain] at hsc
            exact hclamp sc hsc
          have hm_post2 : sf2.mem ⊨
              (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
               trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
               (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
                 (dispPtr ↦ₛ dispBs) ∗
                 memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
               consumeMessageKeyResultAt A (sp + 400#64) (Mut.exec (RatchetState.consumeMessageKey C.F
                 x.msg.senderRatchetKey ck x.msg.counter x.msgType) tr.ratchet).1 ∗
               memRegion x.ret 48 ∗
               memRegion sp 28 ∗
               ((sp + 28#64) ↦₃₂ msgW) ∗
               ((sp + 32#64) ↦₆₄ x.locA) ∗
               ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
               memRegion (sp + 44#64) 4 ∗
               ((sp + 48#64) ↦₆₄ x.remA) ∗
               memRegion (sp + 320#64) 80 ∗
               memRegion (sp + 488#64) 920 ∗
               protocolAddressAt A x.rem x.remA ∗
               protocolAddressAt A x.loc x.locA ∗
               signalMessageAt A x.msgG x.msgA x.msg ∗
               CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
               logOff img ∗
               stackAt sp tryDecryptSubStack ∗
               tryDecryptSavedRegs s0.sp s0 ∗
               A.pool) ∗ R := by
            have hm488 : memRegion (sp + 488#64) 920 =
                memRegion (sp + 488#64) 248 ∗ (memRegion (sp + 736#64) 36 ∗ memRegion (sp + 772#64) 636) := by
              rw [mr_cut_add sp 488 248 672 (by decide), mr_cut_add sp 736 36 636 (by decide)]
            rw [trAt_split_ratchet, signalMessageAt_split_their, hm488, hstack_cmk]
            dsimp only [logOff, trG', r2, trNonRatchetAt] at hpost2 ⊢
            simp only [sepConj_assoc] at hpost2 ⊢
            rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
            refine ⟨hclamp2, ?_⟩
            arm64_sep_close
          clear hpost2
          dsimp only [Out]
          split
          · next mkg r2' hmod =>
            have hr2_eq : r2 = r2' := congrArg Prod.snd hmod
            subst hr2_eq
            have hres_eq : (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
                x.msg.counter x.msgType) tr.ratchet).1 = .ok mkg := congrArg Prod.fst hmod
            rw [hres_eq] at hm_post2
            exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.consumeMsgKey_cmk_ok img C A ctl S ext x trG' tr st1 r2 mkg draws R s0
              hsp0_al hsp_al' hentry hentry_eq hdealloc hsp_def hdisp1 hdisp2 hmsgW_byte
              sf2 hpcf2 hrunf2 (by reg_chain) hsp_alf2 (by reg_chain) (by reg_chain) (by reg_chain)
              (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
              htr_f2' (by reg_chain) hff2 hsymf2 hLf2 hm_post2
          · next e r2' hmod =>
            have hr2_eq : r2 = r2' := congrArg Prod.snd hmod
            subst hr2_eq
            have hres_eq : (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
                x.msg.counter x.msgType) tr.ratchet).1 = .error e := congrArg Prod.fst hmod
            have hne_panic : e ≠ .panic := by
              intro hp; subst hp; exact hnot_panic hres_eq
            rw [hres_eq] at hm_post2
            exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.consumeMsgKey_cmk_err img C A ctl uuidTryParse ext x trG' tr st1 r2 e
              draws R s0 hne_panic hsp0_al hsp_al' hentry hentry_eq hdealloc hsp_def hdisp1 hdisp2
              sf2 hpcf2 hrunf2 (by reg_chain) hsp_alf2 (by reg_chain) (by reg_chain) (by reg_chain)
              (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) htr_f2' (by reg_chain) hff2 hsymf2 hLf2
              hm_post2

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S4SpecExt img C A ctl uuidTryParse S ext :=
  fun hloads hS => CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_ext_trap img C A ctl S ext hloads hS.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeySpec img C A ctl uuidTryParse S abs :=
  fun hloads hS => CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_ext img C A ctl S (tripleRatchetExterns C ctl abs) hloads (.of_tripleRatchetProgAt' hS)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeySpec_trap img C A ctl uuidTryParse S abs :=
  fun hloads hS => CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_ext_trap img C A ctl S (trTrapExterns C abs) hloads (.of_tripleRatchetProgAt'_trap hS)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok_x (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S4SpecX img C encFn decFn A ctl uuidTryParse S ext := by
  intro hloads hS hcmk x trG tr st1 ck draws R s0 s hS4 hL
  rcases hS4 with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hfp, htrace, hfrozen, hsym, hvregs⟩,
    hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hmem⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
  change CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName at hentry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC at hpc
  rw [show (0x3e4#64 : BitVec 64) = 996#64 by rfl] at hpc
  rw [hentry] at hpc
  have hentry_eq := (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq img.base ext).symm
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  have haddrDisplay := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_ext_x hS hentry_eq
  have hdealloc := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_ext_x hS.toAllocContractsX hentry_eq
  have hcmk_call := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.cmk_ok_at_entry_x hcmk hentry_eq
  clear hcmk
  decrypt_fetches_at_ext_cli hentry_eq 996 96
  decrypt_fetches_at_ext_cli hentry_eq 1092 52
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hfp
  rw [hsp29_eq] at hfp
  clear hsp29_eq
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx12 hx20 hx23 hx25 hfp hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hdrop, htake, hfull⟩ := split_chainKeyBytes ck
  let Out : State → Prop := fun s' =>
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      (∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
      (s'.status = .Panicked ∧
        (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))
    | (.error e, r2) =>
      (e ≠ .panic ∧ ∃ trG',
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
      (s'.status = .Panicked ∧
        ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
        (s'.mem ⊨ anyHeap ∗ R))
  have hOut_split : ∀ (prog : Program) (sm : State),
      (∃ s', Steps prog sm s' ∧ Out s') →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps prog sm s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps prog sm s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
    intro prog sm ⟨s', hst, hout⟩
    dsimp only [Out] at hout
    split at hout <;> exact ⟨s', hst, hout⟩
  apply hOut_split
  have hmem0 : s.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 32 ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 368 ∗
       ((sp + 688#64) ↦₆₄ (w6 ++ w5)) ∗
       ((sp + 696#64) ↦₆₄ (w8 ++ w7)) ∗
       ((sp + 704#64) ↦₆₄ (w1 ++ w0)) ∗
       ((sp + 712#64) ↦₆₄ (w3 ++ w2)) ∗
       ((sp + 720#64) ↦₃₂ w4) ∗
       memRegion (sp + 724#64) 684 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R := by
    have hd := hdrop (sp + 688#64)
    have ht := htake (sp + 704#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hd ht
    rw [hd, ht] at hmem
    simp only [sepConj_assoc] at hmem
    simp only [sepConj_assoc]
    exact hmem
  refine steps_of_sepWP hmem0 hL hfrozen hsym
    (mid := entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
    (RegMid := fun sm1 =>
      sm1.readReg64 .x1 = sp + 1024#64 ∧
      sm1.readReg64 .x19 = x.ret ∧
      sm1.readReg64 .x20 = sp + 320#64 ∧
      sm1.readReg64 .x21 = x.ss ∧
      sm1.readReg64 .x22 = x.msgA ∧
      sm1.readReg64 .x23 = sp + 1280#64 ∧
      (sm1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
      sm1.readReg64 .x25 = sp + 400#64 ∧
      sm1.readReg64 .fp = sp + 1408#64 ∧
      sm1.readReg64 .lr = entry + bv% (1092) ∧
      sm1.sp = sp ∧ sm1.spAligned = true ∧ sm1.trace = s0.trace ∧
      calleeSavedVRegs sm1 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      memRegion x.ret 48 ∗
      memRegion sp 32 ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 416 ∗
      ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
      memRegion (sp + 772#64) 204 ∗
      vecU8 A (sp + 976#64) [] ∗
      memRegion (sp + 1000#64) 24 ∗
      ((sp + 1024#64) ↦₆₄ (sp + 976#64)) ∗
      memRegion (sp + 1032#64) 40 ∗
      memRegion (sp + 1072#64) 336 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 96 272 368 416#64,
        mr_cut sp 416 4 268 272 420#64,
        mr_cut sp 420 8 260 268 428#64,
        mr_cut sp 428 8 252 260 436#64,
        mr_cut sp 724 12 672 684 736#64,
        mr_cut sp 736 8 664 672 744#64,
        mr_cut sp 744 8 656 664 752#64,
        mr_cut sp 752 8 648 656 760#64,
        mr_cut sp 760 8 640 648 768#64,
        mr_cut sp 768 4 636 640 772#64,
        mr_cut sp 772 204 432 636 976#64,
        mr_cut sp 976 8 424 432 984#64,
        mr_cut sp 984 8 416 424 992#64,
        mr_cut sp 992 8 408 416 1000#64,
        mr_cut sp 1000 8 400 408 1008#64,
        mr_cut sp 1008 8 392 400 1016#64,
        mr_cut sp 1016 8 384 392 1024#64,
        mr_cut sp 1024 8 376 384 1032#64,
        mr_cut sp 1032 8 368 376 1040#64,
        mr_cut sp 1040 8 360 368 1048#64,
        mr_cut sp 1048 8 352 360 1056#64,
        mr_cut sp 1056 8 344 352 1064#64,
        mr_cut sp 1064 8 336 344 1072#64]
      simp only [sepConj_assoc,
        memRegion_four (sp + 416#64),
        memRegion_eight (sp + 420#64),
        memRegion_eight (sp + 428#64),
        memRegion_eight (sp + 736#64),
        memRegion_eight (sp + 744#64),
        memRegion_eight (sp + 752#64),
        memRegion_eight (sp + 760#64),
        memRegion_four (sp + 768#64),
        memRegion_eight (sp + 976#64),
        memRegion_eight (sp + 984#64),
        memRegion_eight (sp + 992#64),
        memRegion_eight (sp + 1000#64),
        memRegion_eight (sp + 1008#64),
        memRegion_eight (sp + 1016#64),
        memRegion_eight (sp + 1024#64),
        memRegion_eight (sp + 1032#64),
        memRegion_eight (sp + 1040#64),
        memRegion_eight (sp + 1048#64),
        memRegion_eight (sp + 1056#64),
        memRegion_eight (sp + 1064#64)]
    wp_pull_exists
    wp_steps
    refine SepWP.focus_weaken (realign_416_436 sp w4 w5 w6 w7 w8) (by sep_focus) ?_
    wp_steps
    have hck_fold :
        ((sp + 736#64) ↦₆₄ (w1 ++ w0)) ∗ ((sp + 744#64) ↦₆₄ (w3 ++ w2)) ∗
        ((sp + 752#64) ↦₆₄ (w5 ++ w4)) ∗ ((sp + 760#64) ↦₆₄ (w7 ++ w6)) ∗
        ((sp + 768#64) ↦₃₂ w8) ⊢
        ((sp + 736#64) ↦ₛ chainKeyBytes ck) := by
      have hf := (hfull (sp + 736#64)).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hf ⊢
      rw [hf]
      exact Entails.refl _
    refine SepWP.focus_weaken hck_fold (by sep_focus) ?_
    have hv_empty := empty_vecU8_intro A (sp + 976#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv_empty
    refine SepWP.focus_weaken hv_empty (by sep_focus) ?_
    refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 432#64) w8) (by sep_focus) ?_
    refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 720#64) w4) (by sep_focus) ?_
    have hm320 : memRegion (sp + 320#64) 416 =
        memRegion (sp + 320#64) 96 ∗ (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗
        (memRegion (sp + 432#64) 4 ∗ (memRegion (sp + 436#64) 252 ∗ (memRegion (sp + 688#64) 8 ∗
        (memRegion (sp + 696#64) 8 ∗ (memRegion (sp + 704#64) 8 ∗ (memRegion (sp + 712#64) 8 ∗
        (memRegion (sp + 720#64) 4 ∗ memRegion (sp + 724#64) 12))))))))) := by
      rw [mr_cut_add sp 320 96 320 (by decide),
        mr_cut_add sp 416 8 312 (by decide),
        mr_cut_add sp 424 8 304 (by decide),
        mr_cut_add sp 432 4 300 (by decide),
        mr_cut_add sp 436 252 48 (by decide),
        mr_cut_add sp 688 8 40 (by decide),
        mr_cut_add sp 696 8 32 (by decide),
        mr_cut_add sp 704 8 24 (by decide),
        mr_cut_add sp 712 8 16 (by decide),
        mr_cut_add sp 720 4 12 (by decide)]
    have hm1000 : memRegion (sp + 1000#64) 24 =
        memRegion (sp + 1000#64) 8 ∗ (memRegion (sp + 1008#64) 8 ∗ memRegion (sp + 1016#64) 8) := by
      rw [mr_cut_add sp 1000 8 16 (by decide), mr_cut_add sp 1008 8 8 (by decide)]
    have hm1032 : memRegion (sp + 1032#64) 40 =
        memRegion (sp + 1032#64) 8 ∗ (memRegion (sp + 1040#64) 8 ∗ (memRegion (sp + 1048#64) 8 ∗
        (memRegion (sp + 1056#64) 8 ∗ memRegion (sp + 1064#64) 8))) := by
      rw [mr_cut_add sp 1032 8 32 (by decide),
        mr_cut_add sp 1040 8 24 (by decide),
        mr_cut_add sp 1048 8 16 (by decide),
        mr_cut_add sp 1056 8 8 (by decide)]
    rw [hm320, hm1000, hm1032]
    wp_done
  · intro sm1 hpc1 hrun1 hf_fr1 hsym1 hL1
      ⟨hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hfp1, hlr1, hsp1, hsp_al1, htr1, hvregs1⟩
      hm1
    have hm1032_split : memRegion (sp + 1032#64) 40 =
        (∃∗ vt : BitVec 64, (sp + 1032#64) ↦₆₄ vt) ∗ memRegion (sp + 1040#64) 32 := by
      rw [mr_cut_add sp 1032 8 32 (by decide), memRegion_eight (sp + 1032#64)]
    rw [hm1032_split] at hm1
    simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hm1
    rcases hm1 with ⟨vt, hm1⟩
    have hpre_disp : sm1.mem ⊨
        ((addrDisplaySpec A).inImage img).pre (sp + 1024#64, sp + 976#64, vt, []) sm1 ∗
        ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion sp 32 ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 416 ∗
          ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
          memRegion (sp + 772#64) 204 ∗
          memRegion (sp + 1000#64) 24 ∗
          memRegion (sp + 1040#64) 32 ∗
          memRegion (sp + 1072#64) 336 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - addrDisplayStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [addrDisplaySpec, Spec.inImage]
      rw [hsp1]
      rw [stackAt_sub sp tryDecryptSubStack addrDisplayStack] at hm1
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hf_fr1, hsym1⟩, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hx1_1, ?_⟩
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm1 ⊢
      arm64_sep_close
    refine steps_call_out (sp + 1024#64, sp + 976#64, vt, []) haddrDisplay
      hpc1 hrun1 hsp_al1 hlr1 hf_fr1 hsym1 hL1 hpre_disp ?_ ?_
    · intro sf hpan hpost
      dsimp only [addrDisplaySpec, Spec.inImage] at hpost
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨⟨halloc, htr_sub⟩, hpost⟩
      have halloc0 : allocFailedIn s0 sf := by
        unfold allocFailedIn at halloc ⊢; rw [← htr1]; exact halloc
      have htr0 : s0.trace <+: sf.trace := by rw [← htr1]; exact htr_sub
      rw [← sepConj_assoc] at hpost
      have hany : sf.mem ⊨ anyHeap ∗ R :=
        Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpost
      dsimp only [Out]
      split
      · refine Or.inr ⟨hpan, ?_⟩
        dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec, Spec.inImage]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨Or.inr (Or.inr halloc0), htr0⟩, hany⟩
      · exact Or.inr ⟨hpan, ⟨Or.inr halloc0, htr0⟩, hany⟩
    · intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      rcases hcsf1 with ⟨hx19_cs1, hx20_cs1, hx21_cs1, hx22_cs1, hx23_cs1, hx24_cs1, hx25_cs1, _, _, _, hfp_cs1, hvregs_cs1⟩
      have hx19_f1 : sf1.readReg64 .x19 = x.ret := hx19_cs1.trans hx19_1
      have hx20_f1 : sf1.readReg64 .x20 = sp + 320#64 := hx20_cs1.trans hx20_1
      have hx21_f1 : sf1.readReg64 .x21 = x.ss := hx21_cs1.trans hx21_1
      have hx22_f1 : sf1.readReg64 .x22 = x.msgA := hx22_cs1.trans hx22_1
      have hx23_f1 : sf1.readReg64 .x23 = sp + 1280#64 := hx23_cs1.trans hx23_1
      have hx24_f1 : (sf1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
        rw [hx24_cs1]; exact hx24_1
      have hx25_f1 : sf1.readReg64 .x25 = sp + 400#64 := hx25_cs1.trans hx25_1
      have hfp_f1 : sf1.readReg64 .fp = sp + 1408#64 := hfp_cs1.trans hfp1
      have hvregs_f1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := hvregs_cs1.trans hvregs1
      have hsp_f1 : sf1.sp = sp := hspf1.trans hsp1
      dsimp only [addrDisplaySpec, Spec.inImage] at hpost1
      rw [hsp1] at hpost1
      simp only [vecU8, vecU8At, vecHeader, sepConj_assoc, sepExists_sepConj_left,
        sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨dispBs, dispCap, dispPtr, hpost1⟩
      rw [satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨hw0_f1, htr_f1⟩, hpost1⟩
      have htr_f1' : sf1.trace = s0.trace := htr_f1.trans htr1
      simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨hdisp1, hdisp2, _hdisp3⟩, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG tr ∗
           (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
             (dispPtr ↦ₛ dispBs) ∗
             memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
           ((sp + 976#64) ↦₆₄ dispCap) ∗
           ((sp + 984#64) ↦₆₄ dispPtr) ∗
           ((sp + 992#64) ↦₆₄ BitVec.ofNat 64 dispBs.length) ∗
           ((sp + 1024#64) ↦₆₄ (sp + 976#64)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 32 ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 44#64) 4 ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 416 ∗
           ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
           memRegion (sp + 772#64) 204 ∗
           memRegion (sp + 1000#64) 24 ∗
           memRegion (sp + 1032#64) 40 ∗
           memRegion (sp + 1072#64) 336 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [hm1032_split, stackAt_sub sp tryDecryptSubStack addrDisplayStack]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
          sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1 ⊢
        refine ⟨vt, ?_⟩
        arm64_sep_close
      let msgW : BitVec 32 := (sf1.readReg64 .x24).setWidth 32
      have hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType := by
        have h8 : msgW.setWidth 8 = (sf1.readReg64 .x24).setWidth 8 :=
          BitVec.setWidth_setWidth_of_le (sf1.readReg64 .x24) (by decide)
        exact h8.trans hx24_f1
      refine steps_of_sepWP hpost1' hLf1 hff1 hsymf1
        (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
        (RegMid := fun sm2 =>
          sm2.readReg64 .x0 = sp + 56#64 ∧
          sm2.readReg64 .x1 = x.msgA + 56#64 ∧
          sm2.readReg64 .x2 = sp + 736#64 ∧
          (sm2.readReg64 .x3).setWidth 32 = x.msg.counter ∧
          (sm2.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧
          sm2.readReg64 .x8 = sp + 400#64 ∧
          sm2.readReg64 .x19 = x.ret ∧
          sm2.readReg64 .x20 = sp + 320#64 ∧
          sm2.readReg64 .x21 = x.ss ∧
          sm2.readReg64 .x22 = x.msgA ∧
          sm2.readReg64 .x23 = sp + 1280#64 ∧
          sm2.readReg64 .x25 = sp + 400#64 ∧
          sm2.readReg64 .x27 = dispPtr ∧
          sm2.readReg64 .x28 = dispCap ∧
          sm2.readReg64 .fp = sp + 1408#64 ∧
          sm2.readReg64 .lr = entry + bv% (1144) ∧
          sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.trace = s0.trace ∧
          calleeSavedVRegs sm2 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
          (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
            (dispPtr ↦ₛ dispBs) ∗
            memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
          memRegion x.ret 48 ∗
          memRegion sp 28 ∗
          ((sp + 28#64) ↦₃₂ msgW) ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 80 ∗
          memRegion (sp + 400#64) 88 ∗
          memRegion (sp + 488#64) 248 ∗
          ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
          memRegion (sp + 772#64) 636 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · have hsp0 : memRegion sp 32 = memRegion sp 28 ∗ memRegion (sp + 28#64) 4 := by
          have hm := mr_cut_add sp 0 28 4 (by decide)
          simp only [BitVec.add_zero] at hm
          exact hm
        wp_conv_pre =>
          rw [hsp0, memRegion_four (sp + 28#64),
            mr_cut sp 320 80 336 416 400#64,
            mr_cut sp 400 88 248 336 488#64]
          simp only [sepConj_assoc]
        wp_pull_exists
        wp_steps
        have hm772 : memRegion (sp + 772#64) 636 =
            memRegion (sp + 772#64) 204 ∗ (memRegion (sp + 976#64) 8 ∗ (memRegion (sp + 984#64) 8 ∗
            (memRegion (sp + 992#64) 8 ∗ (memRegion (sp + 1000#64) 24 ∗
            (memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 40 ∗
             memRegion (sp + 1072#64) 336)))))) := by
          rw [mr_cut_add sp 772 204 432 (by decide),
            mr_cut_add sp 976 8 424 (by decide),
            mr_cut_add sp 984 8 416 (by decide),
            mr_cut_add sp 992 8 408 (by decide),
            mr_cut_add sp 1000 24 384 (by decide),
            mr_cut_add sp 1024 8 376 (by decide),
            mr_cut_add sp 1032 40 336 (by decide)]
        rw [hm772]
        dsimp only [msgW]
        wp_done
      · intro sm2 hpc2 hrun2 hf_fr2 hsym2 hL2
          ⟨hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2,
           hx23_2, hx25_2, hx27_2, hx28_2, hfp2, hlr2, hsp2, hsp_al2, htr2, hvregs2⟩
          hm2
        let cmkX : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost :=
          { self := sp + 56#64
            G := trG.ratchet
            st := tr.ratchet
            their := x.msg.senderRatchetKey
            theirA := x.msgA + 56#64
            ck := ck
            ckA := sp + 736#64
            counter := x.msg.counter
            msgType := x.msgType
            ret := sp + 400#64 }
        have hcmk_model : cmkX.model C.F =
            Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
              x.msgType) tr.ratchet := rfl
        have hstack_cmk := stackAt_sub sp tryDecryptSubStack cmkStackX
          (by decide) (by decide)
        rw [trAt_split_ratchet, signalMessageAt_split_their] at hm2
        dsimp only [logOff] at hm2
        simp only [sepConj_assoc] at hm2
        rw [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm2
        rcases hm2 with ⟨hclamp, hm2⟩
        have hpre_cmk : sm2.mem ⊨
            (cmkSpecX C.F A img).pre cmkX sm2 ∗
            ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trNonRatchetAt A sp trG tr ∗
              (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
                (dispPtr ↦ₛ dispBs) ∗
                memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
              memRegion x.ret 48 ∗
              memRegion sp 28 ∗
              ((sp + 28#64) ↦₃₂ msgW) ∗
              ((sp + 32#64) ↦₆₄ x.locA) ∗
              ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
              memRegion (sp + 44#64) 4 ∗
              ((sp + 48#64) ↦₆₄ x.remA) ∗
              memRegion (sp + 320#64) 80 ∗
              memRegion (sp + 488#64) 248 ∗
              memRegion (sp + 772#64) 636 ∗
              protocolAddressAt A x.rem x.remA ∗
              protocolAddressAt A x.loc x.locA ∗
              signalMessageNonTheirAt A x.msgG x.msgA x.msg ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - cmkStackX) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [cmkSpecX, Spec.inImage, cmkX]
          rw [hsp2, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hf_fr2, hsym2⟩, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx8_2⟩, ?_⟩
          rw [hstack_cmk] at hm2
          simp only [sepConj_assoc] at hm2 ⊢
          arm64_sep_close
        refine steps_call_out cmkX hcmk_call
          hpc2 hrun2 hsp_al2 hlr2 hf_fr2 hsym2 hL2 hpre_cmk ?_ ?_
        · intro sf hpan hpost
          dsimp only [cmkSpecX, Spec.inImage] at hpost
          rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
          rcases hpost with ⟨⟨hpan_or, htr_sub⟩, hpost⟩
          have htr0 : s0.trace <+: sf.trace := by rw [← htr2]; exact htr_sub
          rw [← sepConj_assoc] at hpost
          have hany : sf.mem ⊨ anyHeap ∗ R :=
            Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpost
          rw [hcmk_model] at hpan_or
          dsimp only [Out]
          split
          · next mkg r2 hmod =>
            rw [hmod] at hpan_or
            rcases hpan_or with hbad | halloc
            · cases hbad
            · have halloc0 : allocFailedIn s0 sf := by
                unfold allocFailedIn at halloc ⊢; rw [← htr2]; exact halloc
              refine Or.inr ⟨hpan, ?_⟩
              dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec, Spec.inImage]
              rw [sepConj_assoc, satisfies_pure_sepConj]
              exact ⟨⟨Or.inr (Or.inr halloc0), htr0⟩, hany⟩
          · next e r2 hmod =>
            rw [hmod] at hpan_or
            refine Or.inr ⟨hpan, ⟨?_, htr0⟩, hany⟩
            rcases hpan_or with hbad | halloc
            · exact Or.inl (Except.error.inj hbad)
            · unfold allocFailedIn at halloc ⊢; rw [← htr2]; exact Or.inr halloc
        · intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hff2 hsymf2 hLf2 hpost2
          rcases hcsf2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, _, hx25_cs2, _, hx27_cs2, hx28_cs2, hfp_cs2, hvregs_cs2⟩
          have hx19_f2 : sf2.readReg64 .x19 = x.ret := hx19_cs2.trans hx19_2
          have hx20_f2 : sf2.readReg64 .x20 = sp + 320#64 := hx20_cs2.trans hx20_2
          have hx21_f2 : sf2.readReg64 .x21 = x.ss := hx21_cs2.trans hx21_2
          have hx22_f2 : sf2.readReg64 .x22 = x.msgA := hx22_cs2.trans hx22_2
          have hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64 := hx23_cs2.trans hx23_2
          have hx25_f2 : sf2.readReg64 .x25 = sp + 400#64 := hx25_cs2.trans hx25_2
          have hx27_f2 : sf2.readReg64 .x27 = dispPtr := hx27_cs2.trans hx27_2
          have hx28_f2 : sf2.readReg64 .x28 = dispCap := hx28_cs2.trans hx28_2
          have hfp_f2 : sf2.readReg64 .fp = sp + 1408#64 := hfp_cs2.trans hfp2
          have hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := hvregs_cs2.trans hvregs2
          have hsp_f2 : sf2.sp = sp := hspf2.trans hsp2
          dsimp only [cmkSpecX, Spec.inImage] at hpost2
          rw [hsp2, hcmk_model] at hpost2
          simp only [cmkX, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
            satisfies_sepExists] at hpost2
          rcases hpost2 with ⟨rG', hpost2⟩
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨⟨hnot_panic, htr_f2⟩, hpost2⟩
          have htr_f2' : sf2.trace = s0.trace := htr_f2.trans htr2
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨_, hpost2⟩
          let r2 := (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
            x.msg.counter x.msgType) tr.ratchet).2
          let trG' : TrGhost := { trG with ratchet := rG' }
          have hclamp2 : ∀ sc, r2.senderChain = some sc →
              Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
            intro sc hsc
            rw [consumeMessageKey_senderChain] at hsc
            exact hclamp sc hsc
          have hm_post2 : sf2.mem ⊨
              (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
               trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
               (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
                 (dispPtr ↦ₛ dispBs) ∗
                 memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
               consumeMessageKeyResultAt A (sp + 400#64) (Mut.exec (RatchetState.consumeMessageKey C.F
                 x.msg.senderRatchetKey ck x.msg.counter x.msgType) tr.ratchet).1 ∗
               memRegion x.ret 48 ∗
               memRegion sp 28 ∗
               ((sp + 28#64) ↦₃₂ msgW) ∗
               ((sp + 32#64) ↦₆₄ x.locA) ∗
               ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
               memRegion (sp + 44#64) 4 ∗
               ((sp + 48#64) ↦₆₄ x.remA) ∗
               memRegion (sp + 320#64) 80 ∗
               memRegion (sp + 488#64) 920 ∗
               protocolAddressAt A x.rem x.remA ∗
               protocolAddressAt A x.loc x.locA ∗
               signalMessageAt A x.msgG x.msgA x.msg ∗
               CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
               logOff img ∗
               stackAt sp tryDecryptSubStack ∗
               tryDecryptSavedRegs s0.sp s0 ∗
               A.pool) ∗ R := by
            have hm488 : memRegion (sp + 488#64) 920 =
                memRegion (sp + 488#64) 248 ∗ (memRegion (sp + 736#64) 36 ∗ memRegion (sp + 772#64) 636) := by
              rw [mr_cut_add sp 488 248 672 (by decide), mr_cut_add sp 736 36 636 (by decide)]
            rw [trAt_split_ratchet, signalMessageAt_split_their, hm488, hstack_cmk]
            dsimp only [logOff, trG', r2, trNonRatchetAt] at hpost2 ⊢
            simp only [sepConj_assoc] at hpost2 ⊢
            rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
            refine ⟨hclamp2, ?_⟩
            arm64_sep_close
          clear hpost2
          dsimp only [Out]
          split
          · next mkg r2' hmod =>
            have hr2_eq : r2 = r2' := congrArg Prod.snd hmod
            subst hr2_eq
            have hres_eq : (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
                x.msg.counter x.msgType) tr.ratchet).1 = .ok mkg := congrArg Prod.fst hmod
            rw [hres_eq] at hm_post2
            exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.consumeMsgKey_cmk_ok_x img C decFn A ctl S ext x trG' tr st1 r2 mkg draws R s0
              hsp0_al hsp_al' hentry hentry_eq hdealloc hsp_def hdisp1 hdisp2 hmsgW_byte
              sf2 hpcf2 hrunf2 hsp_f2 hsp_alf2 hx19_f2 hx20_f2 hx21_f2 hx22_f2 hx23_f2
              hx25_f2 hx27_f2 hx28_f2 hfp_f2 htr_f2' hvregs_f2 hff2 hsymf2 hLf2 hm_post2
          · next e r2' hmod =>
            have hr2_eq : r2 = r2' := congrArg Prod.snd hmod
            subst hr2_eq
            have hres_eq : (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
                x.msg.counter x.msgType) tr.ratchet).1 = .error e := congrArg Prod.fst hmod
            have hne_panic : e ≠ .panic := by
              intro hp; subst hp; exact hnot_panic hres_eq
            rw [hres_eq] at hm_post2
            exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.consumeMsgKey_cmk_err_x img C A ctl uuidTryParse ext x trG' tr st1 r2 e
              draws R s0
              hne_panic hsp0_al hsp_al' hentry hentry_eq hdealloc hsp_def hdisp1 hdisp2
              sf2 hpcf2 hrunf2 (by reg_chain) hsp_alf2 (by reg_chain) (by reg_chain) (by reg_chain)
              (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) htr_f2' hvregs_f2 hff2 hsymf2 hLf2
              hm_post2

end CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
