/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegMidBase
import ProofLib.SepLogic.WPp

/-!
# `consume_message_key` Segment Helpers (`S4Spec`)

Framing and postcondition-staging helpers around `RatchetState::consume_message_key` and
`clear_unacknowledged_pre_key_message` (`+0x3e4 → +0x5b8 / +0x30c`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

/-! ## Segment S4 (`+0x3e4 → +0x5b8 / +0x30c`) -/

@[local simp, local wp_norm, local arm64_norm]
private theorem extractLsb32_32_append32 (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 32 32 = hi := by bv_bits

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
    have hlo : ∀ {w : Nat} (hi : BitVec w) (lo : BitVec 8), (hi ++ lo).extractLsb' 0 8 = lo := by
      intro _ hi lo; ext i hlt; simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hlt]
    have hhi : ∀ {w : Nat} (hi : BitVec w) (lo : BitVec 8) (s : Nat),
        (hi ++ lo).extractLsb' (s + 8) 8 = hi.extractLsb' s 8 := by
      intro _ hi lo s; ext i hlt
      have hge : ¬ (s + 8 + i < 8) := by omega
      have hsub : s + 8 + i - 8 = s + i := by omega
      simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hge, hsub]
    have e0 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 0 8 = u0 :=
      fun u3 u2 u1 u0 => hlo (u3 ++ u2 ++ u1) u0
    have e1 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 8 8 = u1 :=
      fun u3 u2 u1 u0 => (hhi (u3 ++ u2 ++ u1) u0 0).trans (hlo (u3 ++ u2) u1)
    have e2 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 16 8 = u2 :=
      fun u3 u2 u1 u0 =>
        (hhi (u3 ++ u2 ++ u1) u0 8).trans ((hhi (u3 ++ u2) u1 0).trans (hlo u3 u2))
    have e3 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 24 8 = u3 := by
      intro u3 u2 u1 u0
      rw [hhi (u3 ++ u2 ++ u1) u0 16, hhi (u3 ++ u2) u1 8, hhi u3 u2 0]
      ext i hi; simp
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
    rw [hw0, hw1, hw2, hw3, hw4, ← pointsTo32_merge64 a w0 w1,
      ← pointsTo32_merge64 (a + 8#64) w2 w3]
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

private theorem takeSkippedKey_senderChain (their : PublicKey) (counter : BitVec 32) (s :
  RatchetState) :
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

private theorem storeSkippedKey_senderChain (their : PublicKey) (key : MessageKeyGenerator) (s :
  RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) s).2.senderChain = s.senderChain := by
  unfold RatchetState.storeSkippedKey
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem setReceiverChainKey_senderChain (their : PublicKey) (ck : ChainKey) (s :
  RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) s).2.senderChain = s.senderChain := by
  unfold RatchetState.setReceiverChainKey
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem advanceChain_senderChain (F : ShaCompress) (their : PublicKey) (counter : BitVec
  32) :
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
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) s).2.senderChain
      = s.senderChain := by
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
      cases hadv1 : (Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat
        ck) s).1 with
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
            (Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck)
              s).2).1 <;>
            exact hset.trans hadv

private def ErrWordsRel (A : RustAlloc) (e : SignalProtocolError)
    (w416 w424 w432 w440 : BitVec 64) (restHeap : SepProp) : Prop :=
  match e with
  | .duplicatedMessage i c =>
    w416 = c ++ i ∧ restHeap = emp
  | .invalidMessage t .tooFarInFuture =>
    ∃ hi : BitVec 56,
      w432 = BitVec.ofNat 64 tooFarInFutureStr.length ∧ w440 = hi ++ msgTypeByte t ∧
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
      ((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗ ((sp + 408#64) ↦₆₄ speTag e) ∗
      ((sp + 416#64) ↦₆₄ w416) ∗ ((sp + 424#64) ↦₆₄ w424) ∗ ((sp + 432#64) ↦₆₄ w432) ∗
      ((sp + 440#64) ↦₆₄ w440) ∗ ((sp + 448#64) ↦₆₄ w448) ∗ memRegion (sp + 456#64) 32 ∗
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
        (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗
          memRegion (sp + 456#64) 32))) := by
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
        memRegion ((sp + 440#64) + 1#64) 7 ∗ (memRegion (sp + 448#64) 8 ∗
          memRegion (sp + 456#64) 32) := by
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
        ((sp + 384#64) ↦₆₄ (hi ++ msgTypeByte t)) ∗ ((sp + 392#64) ↦₆₄ w448) ∗
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
      intro _ _ h; first | exact not_satisfies_false_sepConj h | (dsimp only [Spec.inImage] at h; exact not_satisfies_false_sepConj h)) :
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

namespace BS8

end BS8

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC
