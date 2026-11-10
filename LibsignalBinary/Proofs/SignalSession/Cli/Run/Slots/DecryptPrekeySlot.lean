/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SpecState

/-!
# State-Coupled `decrypt_prekey` Slot Adapter

Adapts `RunProofs.cliDecryptPrekeySpecState` on `cliDecryptPrekeyName` to `decPkSlotSpec` on
`wrapDecryptPrekeyName` (`signal_session_handshake::decrypt_prekey`), closing the `decryptPrekey`
slot of `RunCallees`.

Factors the 6 stack words `[w₀..w₅]` of the sret slot out of every variant of `RunDrop.speOwnedAt`
and `decResAt` (`dpErrHeap`, `dpResHeap`) with bidirectional separation-logic entailments, and
instantiates `RunProofs.DpPollKState` over `(fs, trace)` (`dpSlotPollKState`, `K₀_state`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose
open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalSessionRepr

/-! ## 1. Stack budgets -/
/-- Hardware stack frame of `cliDpPollName` (96 bytes saved registers + 3184 bytes locals). -/
abbrev dpPollFrame : Nat := 3280
/-- Stack budget of one poll of `message_decrypt_prekey`: `2 ^ 20` (`1048576` bytes) for the
closure, which includes the closure's `3280`-byte frame (`dpPollFrame`), plus `B.dirGetNeed`
below it. -/
abbrev dpPollNeed (B : RunBudgets) : Nat := 1048576 + B.dirGetNeed
/-- Total stack budget of `signal_session_handshake::decrypt_prekey` (`RunNeeds.decryptPrekey`). -/
abbrev decPkNeed (B : RunBudgets) : Nat := dpWrapFrame + 1048576 + B.dirGetNeed
theorem dpPollNeed_crypto (B : RunBudgets) : 524288 ≤ dpPollNeed B := by
  unfold dpPollNeed; omega
theorem dpPollNeed_store (B : RunBudgets) : dpPollFrame + 848 + B.dirGetNeed ≤ dpPollNeed B := by
  unfold dpPollFrame dpPollNeed; omega
theorem decPkNeed_eq (B : RunBudgets) : decPkNeed B = 2144 + 1048576 + B.dirGetNeed := rfl

/-! ## 2. `SepProp` combinators and byte/word bijections -/
section CellHelpers
private theorem bv8_8 : (8#64 : BitVec 64) + 8#64 = 16#64 := rfl
private theorem bv8_16 : (8#64 : BitVec 64) + 16#64 = 24#64 := rfl
private theorem bv8_24 : (8#64 : BitVec 64) + 24#64 = 32#64 := rfl
private theorem bv8_25 : (8#64 : BitVec 64) + 25#64 = 33#64 := rfl
private theorem bv24_1 : (24#64 : BitVec 64) + 1#64 = 25#64 := rfl
private theorem bv24_8 : (24#64 : BitVec 64) + 8#64 = 32#64 := rfl
private theorem bv24_16 : (24#64 : BitVec 64) + 16#64 = 40#64 := rfl
private theorem bv32_1 : (32#64 : BitVec 64) + 1#64 = 33#64 := rfl
private theorem bv32_8 : (32#64 : BitVec 64) + 8#64 = 40#64 := rfl
private theorem sepConj_pure_of_true {φ : Prop} (P : SepProp) (hφ : φ) : P ∗ ⌜φ⌝ = P := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩; rw [hEq, pure_true, sepConj_emp]
private theorem pure_sepConj_eq_of_true {φ : Prop} (P : SepProp) (hφ : φ) : ⌜φ⌝ ∗ P = P := by
  rw [sepConj_comm, sepConj_pure_of_true P hφ]
private theorem emp_entails_pure {φ : Prop} (hφ : φ) : emp ⊢ ⌜φ⌝ := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true]; exact Entails.refl _
private theorem false_entails (Q : SepProp) : (⌜False⌝ : SepProp) ⊢ Q :=
  Entails.pure_left_only False.elim
private theorem ent_pure_left {φ : Prop} {P Q : SepProp} (h : φ → (P ⊢ Q)) : ⌜φ⌝ ∗ P ⊢ Q :=
  Entails.pure_left h
private theorem ent_pure_peek {φ : Prop} {P Q : SepProp} (h : φ → (⌜φ⌝ ∗ P ⊢ Q)) : ⌜φ⌝ ∗ P ⊢ Q :=
  ent_pure_left fun hφ => by rw [← pure_sepConj_eq_of_true P hφ]; exact h hφ
private theorem ent_pure_right {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) : P ⊢ ⌜φ⌝ ∗ Q := by
  rw [pure_sepConj_eq_of_true Q hφ]; exact h
private theorem ent_bind {α : Type} {A R Q : SepProp} {P : α → SepProp}
    (hA : A ⊢ ∃∗ x, P x) (hk : ∀ x, P x ∗ R ⊢ Q) : A ∗ R ⊢ Q := by
  refine Entails.trans (sepConj_mono_left hA) ?_
  rw [sepExists_sepConj_left]; exact Entails.sepExists_elim hk
private theorem extractLsb'_zero_append8 {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 0 8 = b := by
  ext i hi; simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hi]
private theorem extractLsb'_shift_append8 {n : Nat} (x : BitVec n) (b : BitVec 8) (k : Nat) :
    (x ++ b).extractLsb' (k + 8) 8 = x.extractLsb' k 8 := by
  ext i hi
  have hlt : ¬(k + 8 + i < 8) := by omega
  have hsub : k + 8 + i - 8 = k + i := by omega
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hlt, hsub]
private def pack64Bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0
private theorem pack64Bytes_extract (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 0 8 = b0 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 8 8 = b1 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 16 8 = b2 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 24 8 = b3 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 32 8 = b4 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 40 8 = b5 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 48 8 = b6 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 56 8 = b7 := by
  unfold pack64Bytes; refine ⟨extractLsb'_zero_append8 _ b0,
    (extractLsb'_shift_append8 _ b0 0).trans (extractLsb'_zero_append8 _ b1),
    (extractLsb'_shift_append8 _ b0 8).trans ((extractLsb'_shift_append8 _ b1 0).trans (extractLsb'_zero_append8 _ b2)),
    (extractLsb'_shift_append8 _ b0 16).trans ((extractLsb'_shift_append8 _ b1 8).trans
      ((extractLsb'_shift_append8 _ b2 0).trans (extractLsb'_zero_append8 _ b3))),
    (extractLsb'_shift_append8 _ b0 24).trans ((extractLsb'_shift_append8 _ b1 16).trans
      ((extractLsb'_shift_append8 _ b2 8).trans ((extractLsb'_shift_append8 _ b3 0).trans (extractLsb'_zero_append8 _ b4)))),
    (extractLsb'_shift_append8 _ b0 32).trans ((extractLsb'_shift_append8 _ b1 24).trans
      ((extractLsb'_shift_append8 _ b2 16).trans ((extractLsb'_shift_append8 _ b3 8).trans
        ((extractLsb'_shift_append8 _ b4 0).trans (extractLsb'_zero_append8 _ b5))))),
    (extractLsb'_shift_append8 _ b0 40).trans ((extractLsb'_shift_append8 _ b1 32).trans
      ((extractLsb'_shift_append8 _ b2 24).trans ((extractLsb'_shift_append8 _ b3 16).trans
        ((extractLsb'_shift_append8 _ b4 8).trans ((extractLsb'_shift_append8 _ b5 0).trans (extractLsb'_zero_append8 _ b6)))))),
    (extractLsb'_shift_append8 _ b0 48).trans ((extractLsb'_shift_append8 _ b1 40).trans
      ((extractLsb'_shift_append8 _ b2 32).trans ((extractLsb'_shift_append8 _ b3 24).trans
        ((extractLsb'_shift_append8 _ b4 16).trans ((extractLsb'_shift_append8 _ b5 8).trans
          ((extractLsb'_shift_append8 _ b6 0).trans (by ext i hi; simp)))))))⟩
private theorem extractLsb'_lo32 (hi lo : BitVec 32) (k : Nat) (hk : k + 8 ≤ 32) :
    (hi ++ lo).extractLsb' k 8 = lo.extractLsb' k 8 := by
  ext i hi'
  have hlt : k + i < 32 := by omega
  simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [hlt]
private theorem extractLsb'_hi32 (hi lo : BitVec 32) (k : Nat) :
    (hi ++ lo).extractLsb' (k + 32) 8 = hi.extractLsb' k 8 := by
  ext i hi'
  have hlt : ¬(k + 32 + i < 32) := by omega
  have hsub : k + 32 + i - 32 = k + i := by omega
  simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [hlt, hsub]
private theorem pointsTo32_pair (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  simp only [pointsTo64, pointsTo32, sepConj_assoc, BitVec.add_zero, BitVec.add_assoc,
    extractLsb'_lo32 hi lo 0 (by decide), extractLsb'_lo32 hi lo 8 (by decide),
    extractLsb'_lo32 hi lo 16 (by decide), extractLsb'_lo32 hi lo 24 (by decide),
    extractLsb'_hi32 hi lo 0, extractLsb'_hi32 hi lo 8,
    extractLsb'_hi32 hi lo 16, extractLsb'_hi32 hi lo 24]
  rfl
private theorem pointsTo64_eq_bytes8 (a w : BitVec 64) : (a ↦₆₄ w) =
      (a ↦ₛ [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
              w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8]) := by
  simp only [pointsTo64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero, BitVec.add_assoc]; rfl
private theorem pointsTo64_entails_memRegion8 (a w : BitVec 64) : (a ↦₆₄ w) ⊢ memRegion a 8 := by
  rw [pointsTo64_eq_bytes8]; exact ProofLib.pointsToBytes_entails_memRegion a _
private theorem memRegion8_words (a : BitVec 64) : memRegion a 8 ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes a 8 (by decide)]
  refine Entails.sepExists_elim fun bs => ent_pure_left fun hlen => ?_
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen)
  refine Entails.sepExists_right (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7) ?_
  have hex := pack64Bytes_extract b0 b1 b2 b3 b4 b5 b6 b7
  rw [pointsTo64_eq_bytes8, hex.1, hex.2.1, hex.2.2.1, hex.2.2.2.1, hex.2.2.2.2.1,
      hex.2.2.2.2.2.1, hex.2.2.2.2.2.2.1, hex.2.2.2.2.2.2.2]
  exact Entails.refl _
private theorem pointsTo64_byte_entails (a w : BitVec 64) (b : BitVec 8) (hb : w.extractLsb' 0 8 = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_bytes8, hb, pointsToBytes_cons]
  exact sepConj_mono (Entails.refl _) (ProofLib.pointsToBytes_entails_memRegion (a + 1#64) _)
private theorem byte_memRegion7_words (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢ ∃∗ w : BitVec 64, ⌜w.extractLsb' 0 8 = b⌝ ∗ (a ↦₆₄ w) := by
  rw [sepConj_comm]
  refine ent_bind (Entails.of_eq (ProofLib.memRegion_eq_exists_bytes (a + 1#64) 7 (by decide))) fun bs => ?_
  rw [sepConj_assoc]; refine ent_pure_left fun hlen => ?_; rw [sepConj_comm]
  rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen)
  rw [← pointsToBytes_cons]
  have hex := pack64Bytes_extract b b1 b2 b3 b4 b5 b6 b7
  refine Entails.sepExists_right (pack64Bytes b b1 b2 b3 b4 b5 b6 b7) (ent_pure_right hex.1 ?_)
  rw [pointsTo64_eq_bytes8, hex.1, hex.2.1, hex.2.2.1, hex.2.2.2.1, hex.2.2.2.2.1,
      hex.2.2.2.2.2.1, hex.2.2.2.2.2.2.1, hex.2.2.2.2.2.2.2]
  exact Entails.refl _
private theorem dpWords2_entails_memRegion16 (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ⊢ memRegion a 16 := by
  rw [memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion8 a w0) (pointsTo64_entails_memRegion8 (a + 8#64) w1)
private theorem memRegion16_words (a : BitVec 64) :
    memRegion a 16 ⊢ ∃∗ t : BitVec 64 × BitVec 64, (a ↦₆₄ t.1) ∗ ((a + 8#64) ↦₆₄ t.2) := by
  rw [memRegion_split a 8 8 (by decide)]
  refine ent_bind (memRegion8_words a) fun w0 => ?_; rw [sepConj_comm]
  refine ent_bind (memRegion8_words (a + 8#64)) fun w1 => ?_; rw [sepConj_comm]
  exact Entails.sepExists_right (w0, w1) (Entails.refl _)
private theorem dpWords3_entails_memRegion24 (a w0 w1 w2 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ⊢ memRegion a 24 := by
  rw [memRegion_split a 8 16 (by decide)]
  have e16 := dpWords2_entails_memRegion16 (a + 8#64) w1 w2
  simp only [BitVec.add_assoc, bv8_8] at e16
  exact sepConj_mono (pointsTo64_entails_memRegion8 a w0) e16
private theorem memRegion24_words (a : BitVec 64) :
    memRegion a 24 ⊢ ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64,
      (a ↦₆₄ t.1) ∗ ((a + 8#64) ↦₆₄ t.2.1) ∗ ((a + 16#64) ↦₆₄ t.2.2) := by
  rw [memRegion_split a 8 16 (by decide)]
  refine ent_bind (memRegion8_words a) fun w0 => ?_; rw [sepConj_comm]
  refine ent_bind (memRegion16_words (a + 8#64)) fun ⟨w1, w2⟩ => ?_
  simp only [BitVec.add_assoc, bv8_8]; rw [sepConj_comm]
  exact Entails.sepExists_right (w0, w1, w2) (Entails.refl _)
private theorem dpWords4_entails_memRegion32 (v w₀ w₁ w₂ w₃ : BitVec 64) :
    ((v ↦₆₄ w₀) ∗ ((v + 8#64) ↦₆₄ w₁) ∗ ((v + 16#64) ↦₆₄ w₂) ∗ ((v + 24#64) ↦₆₄ w₃)) ⊢
      memRegion v 32 := by
  have h24 : (v + 16#64) + 8#64 = v + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [memRegion_split v 16 16 (by decide), ← sepConj_assoc]
  have e2 := dpWords2_entails_memRegion16 (v + 16#64) w₂ w₃
  rw [h24] at e2; exact sepConj_mono (dpWords2_entails_memRegion16 v w₀ w₁) e2
private theorem memRegion32_words (v : BitVec 64) : memRegion v 32 ⊢
      ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64, (v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2.1) ∗
          ((v + 16#64) ↦₆₄ t.2.2.1) ∗ ((v + 24#64) ↦₆₄ t.2.2.2) := by
  have h24 : (v + 16#64) + 8#64 = v + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [memRegion_split v 16 16 (by decide)]
  refine ent_bind (memRegion16_words v) fun ⟨w₀, w₁⟩ => ?_; rw [sepConj_comm]
  refine ent_bind (memRegion16_words (v + 16#64)) fun ⟨w₂, w₃⟩ => ?_
  rw [h24, sepConj_comm, sepConj_assoc]
  exact Entails.sepExists_right (w₀, w₁, w₂, w₃) (Entails.refl _)
private theorem dpWords5_entails_memRegion40 (v w₁ w₂ w₃ w₄ w₅ : BitVec 64) :
    ((v ↦₆₄ w₁) ∗ ((v + 8#64) ↦₆₄ w₂) ∗ ((v + 16#64) ↦₆₄ w₃) ∗
      ((v + 24#64) ↦₆₄ w₄) ∗ ((v + 32#64) ↦₆₄ w₅)) ⊢ memRegion v 40 := by
  rw [memRegion_split v 8 32 (by decide)]
  have e2 := dpWords4_entails_memRegion32 (v + 8#64) w₂ w₃ w₄ w₅
  simp only [BitVec.add_assoc, bv8_8, bv8_16, bv8_24] at e2
  exact sepConj_mono (pointsTo64_entails_memRegion8 v w₁) e2
private theorem memRegion40_words (v : BitVec 64) : memRegion v 40 ⊢
      ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64,
        (v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2.1) ∗ ((v + 16#64) ↦₆₄ t.2.2.1) ∗
          ((v + 24#64) ↦₆₄ t.2.2.2.1) ∗ ((v + 32#64) ↦₆₄ t.2.2.2.2) := by
  rw [memRegion_split v 8 32 (by decide)]
  refine ent_bind (memRegion8_words v) fun w₁ => ?_; rw [sepConj_comm]
  refine ent_bind (memRegion32_words (v + 8#64)) fun ⟨w₂, w₃, w₄, w₅⟩ => ?_
  simp only [BitVec.add_assoc, bv8_8, bv8_16, bv8_24]; rw [sepConj_comm]
  exact Entails.sepExists_right (w₁, w₂, w₃, w₄, w₅) (Entails.refl _)
end CellHelpers

/-! ## 3. Address-independent 6-word sret decomposition of `speOwnedAt` and `decResAt` -/
/-- Off-stack heap ownership of a `Vec<u8>` whose 3 header words are `(cap, ptr, len)`. -/
def vecU8Heap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))
/-- Off-stack rodata ownership of a `&'static str` fat pointer `(ptr, len)`. -/
def strRefHeap (ptr len : BitVec 64) (lit : List (BitVec 8)) : SepProp :=
  ⌜len = BitVec.ofNat 64 lit.length⌝ ∗ (ptr ↦ᵣ lit)
/-- Off-stack ownership of `invalidMessageStrAt` whose 3 `Vec<u8>` header words are `(w₁, w₂, w₃)`. -/
def invalidMsgStrHeap (A : RustAlloc) (w₁ w₂ w₃ : BitVec 64) : InvalidMessageReason → SepProp
  | .tooFarInFuture => ⌜w₃ = BitVec.ofNat 64 tooFarInFutureStr.length⌝ ∗ vecU8Heap A w₁ w₂ tooFarInFutureStr
  | .macFailed => ⌜w₃ = BitVec.ofNat 64 macFailedStr.length⌝ ∗ vecU8Heap A w₁ w₂ macFailedStr
  | .pqRatchet => ∃∗ bs : List (BitVec 8), ⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs
  | .badCiphertext => ∃∗ bs : List (BitVec 8), ⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs
  | .decryptionFailed => ⌜False⌝
/-- Off-stack ownership of `speAt A fnName a e` given the 6 stack words `[w₀..w₅]`. -/
def dpProtoHeap (A : RustAlloc) (fnName : List (BitVec 8))
    (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) : SignalProtocolError → SepProp
  | .invalidState => ⌜w₀ = speWord 1⌝ ∗
      (∃∗ bs : List (BitVec 8), ⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs) ∗
      strRefHeap w₄ w₅ fnName
  | .ciphertextMessageTooShort n => ⌜w₀ = speWord 3 ∧ w₁ = BitVec.ofNat 64 n⌝
  | .legacyCiphertextVersion v => ⌜w₀ = speWord 4 ∧ w₁.extractLsb' 0 8 = v⌝
  | .unrecognizedCiphertextVersion v => ⌜w₀ = speWord 5 ∧ w₁.extractLsb' 0 8 = v⌝
  | .invalidProtobufEncoding => ⌜w₀ = speWord 2⌝
  | .noKeyTypeIdentifier => ⌜w₀ = speWord 7⌝
  | .badKeyType t => ⌜w₀ = speWord 8 ∧ w₁.extractLsb' 0 8 = t⌝
  | .badKeyLength n => ⌜w₀ = speWord 9 ∧ w₁ = BitVec.ofNat 64 n⌝
  | .invalidKeyAgreement => ⌜w₀ = speWord 10⌝
  | .invalidSessionStructure r => ⌜w₀ = speWord 20⌝ ∗ strRefHeap w₁ w₂ (invalidSessionStructureStr r)
  | .duplicatedMessage i c => ⌜w₀ = speWord 23 ∧ w₁ = c ++ i⌝
  | .invalidMessage t r =>
    ⌜w₀ = speWord 24 ∧ w₄.extractLsb' 0 8 = msgTypeByte t⌝ ∗ invalidMsgStrHeap A w₁ w₂ w₃ r
  | .panic => ⌜False⌝
/-- Off-stack heap / rodata ownership of any `RunDrop.SpeOwned` given its 6 stack words `ws`. -/
def dpErrHeap (A : RustAlloc) (ws : List (BitVec 64)) (k : RunDrop.SpeOwned) : SepProp :=
  match ws with
  | [w₀, w₁, w₂, w₃, w₄, w₅] =>
    match k with
    | .proto fnName e => dpProtoHeap A fnName w₀ w₁ w₂ w₃ w₄ w₅ e
    | .sessionNotFound addr op =>
      ⌜w₂ = BitVec.ofNat 64 addr.name.length ∧ w₃.extractLsb' 0 8 = addr.device⌝ ∗
        vecU8Heap A w₀ w₁ addr.name ∗ strRefHeap w₄ w₅ (LibsignalTripleRatchetRepr.utf8 op)
    | .untrustedIdentity addr =>
      ⌜w₀ = speWord speUntrustedIdentity ∧ w₃ = BitVec.ofNat 64 addr.name.length ∧
        w₄.extractLsb' 0 8 = addr.device⌝ ∗ vecU8Heap A w₁ w₂ addr.name
    | .badKemKeyType => ⌜w₀ = speWord 31⌝
    | .badKemKeyLength => ⌜w₀ = speWord 33⌝
    | .plain i _ => ⌜w₀ = speWord i⌝
    | .withString i _ => ⌜w₀ = speWord i⌝ ∗
        (∃∗ bs : List (BitVec 8), ⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs)
  | _ => ⌜False⌝
/-- Off-stack heap / rodata ownership of `decResAt A a e` given its 6 stack words `ws`. -/
def dpResHeap (A : RustAlloc) (ws : List (BitVec 64))
    (e : Except (ApiError AddrVal Unit) Bytes) : SepProp :=
  match e with
  | .ok pt =>
    match ws with
    | [w₀, w₁, w₂, w₃, _, _] => ⌜w₀ = okTagVec ∧ w₃ = BitVec.ofNat 64 pt.length⌝ ∗ vecU8Heap A w₁ w₂ pt
    | _ => ⌜False⌝
  | .error _ => ∃∗ k : RunDrop.SpeOwned, dpErrHeap A ws k
section SpeBijectionProofs
private theorem dpWords6_eq (a w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) : dpWordsAt a [w₀, w₁, w₂, w₃, w₄, w₅] =
      (a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
        ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅) := by
  simp only [dpWordsAt, sepConj_emp, BitVec.add_assoc]; rfl
private theorem dpWords5_eq (a w₀ w₁ w₂ w₃ w₄ : BitVec 64) : dpWordsAt a [w₀, w₁, w₂, w₃, w₄] =
      (a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
        ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) := by
  simp only [dpWordsAt, sepConj_emp, BitVec.add_assoc]; rfl
private theorem vecU8_of_words (A : RustAlloc) (v w₀ w₁ w₂ : BitVec 64) (bs : List (BitVec 8)) :
    ((v ↦₆₄ w₀) ∗ ((v + 8#64) ↦₆₄ w₁) ∗ ((v + 16#64) ↦₆₄ w₂)) ∗
      (⌜w₂ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₀ w₁ bs) ⊢ vecU8 A v bs := by
  rw [sepConj_comm, sepConj_assoc]; refine ent_pure_left fun hw₂ => ?_
  subst hw₂; rw [sepConj_comm]
  exact Entails.sepExists_right w₀ (Entails.sepExists_right w₁ (Entails.refl _))
private theorem vecU8_words (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) : vecU8 A v bs ⊢
      ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64,
        ((v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2.1) ∗ ((v + 16#64) ↦₆₄ t.2.2)) ∗
          (⌜t.2.2 = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A t.1 t.2.1 bs) := by
  unfold vecU8; refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right (cap, ptr, BitVec.ofNat 64 bs.length) ?_
  rw [pure_sepConj_eq_of_true _ rfl]; exact Entails.refl _
private theorem strRef_of_words (v w₀ w₁ : BitVec 64) (lit : List (BitVec 8)) :
    ((v ↦₆₄ w₀) ∗ ((v + 8#64) ↦₆₄ w₁)) ∗ strRefHeap w₀ w₁ lit ⊢ strRefAt v lit := by
  unfold strRefHeap; rw [sepConj_comm, sepConj_assoc]
  refine ent_pure_left fun hw₁ => ?_; subst hw₁; rw [sepConj_comm, sepConj_assoc]
  exact Entails.sepExists_right w₀ (Entails.refl _)
private theorem strRef_words (v : BitVec 64) (lit : List (BitVec 8)) : strRefAt v lit ⊢
      ∃∗ t : BitVec 64 × BitVec 64, ((v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2)) ∗ strRefHeap t.1 t.2 lit := by
  unfold strRefAt; refine Entails.sepExists_elim fun p => ?_
  refine Entails.sepExists_right (p, BitVec.ofNat 64 lit.length) ?_
  unfold strRefHeap; rw [pure_sepConj_eq_of_true _ rfl, sepConj_assoc]; exact Entails.refl _
private theorem plainSpeTag_ne_pending {i : Nat} (hi : RunDrop.PlainSpeTag i) :
    speWord i ≠ pendingTag := by
  unfold RunDrop.PlainSpeTag RunDrop.plainSpeTags at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem strSpeTag_ne_pending {i : Nat} (hi : RunDrop.StrSpeTag i) : speWord i ≠ pendingTag := by
  unfold RunDrop.StrSpeTag RunDrop.strSpeTags at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem cap_lt_half_ne_pending {cap : BitVec 64} (hcap : cap.toNat < 2 ^ 63) :
    cap ≠ pendingTag := by
  intro heq; subst heq
  have hp : pendingTag.toNat = 2 ^ 64 - 3 := by decide
  omega
private theorem invalidMsg_of_words (A : RustAlloc) (v w₁ w₂ w₃ : BitVec 64)
    (r : InvalidMessageReason) : (((v ↦₆₄ w₁) ∗ ((v + 8#64) ↦₆₄ w₂) ∗ ((v + 16#64) ↦₆₄ w₃)) ∗
      invalidMsgStrHeap A w₁ w₂ w₃ r) ⊢ invalidMessageStrAt A v r := by
  cases r with
  | tooFarInFuture => exact vecU8_of_words A v w₁ w₂ w₃ tooFarInFutureStr
  | macFailed => exact vecU8_of_words A v w₁ w₂ w₃ macFailedStr
  | pqRatchet =>
    dsimp only [invalidMsgStrHeap, invalidMessageStrAt]; rw [sepConj_comm]
    refine ent_bind (Entails.refl _) fun bs => ?_
    rw [sepConj_comm]; exact Entails.sepExists_right bs (vecU8_of_words A v w₁ w₂ w₃ bs)
  | badCiphertext =>
    dsimp only [invalidMsgStrHeap, invalidMessageStrAt]; rw [sepConj_comm]
    refine ent_bind (Entails.refl _) fun bs => ?_
    rw [sepConj_comm]; exact Entails.sepExists_right bs (vecU8_of_words A v w₁ w₂ w₃ bs)
  | decryptionFailed =>
    dsimp only [invalidMsgStrHeap]; rw [sepConj_comm]; exact ent_pure_left False.elim
private theorem invalidMsg_words (A : RustAlloc) (v : BitVec 64) (r : InvalidMessageReason) :
    invalidMessageStrAt A v r ⊢ ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64,
        ((v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2.1) ∗ ((v + 16#64) ↦₆₄ t.2.2)) ∗
          invalidMsgStrHeap A t.1 t.2.1 t.2.2 r := by
  cases r with
  | tooFarInFuture => exact vecU8_words A v tooFarInFutureStr
  | macFailed => exact vecU8_words A v macFailedStr
  | pqRatchet =>
    dsimp only [invalidMessageStrAt, invalidMsgStrHeap]; refine Entails.sepExists_elim fun bs =>
      Entails.trans (vecU8_words A v bs) (Entails.sepExists_elim fun ⟨w₁, w₂, w₃⟩ => ?_)
    exact Entails.sepExists_right (w₁, w₂, w₃)
      (sepConj_mono (Entails.refl _) (Entails.sepExists_right bs (Entails.refl _)))
  | badCiphertext =>
    dsimp only [invalidMessageStrAt, invalidMsgStrHeap]; refine Entails.sepExists_elim fun bs =>
      Entails.trans (vecU8_words A v bs) (Entails.sepExists_elim fun ⟨w₁, w₂, w₃⟩ => ?_)
    exact Entails.sepExists_right (w₁, w₂, w₃)
      (sepConj_mono (Entails.refl _) (Entails.sepExists_right bs (Entails.refl _)))
  | decryptionFailed => exact false_entails _
private theorem fwd_tag_mem40 (a w₀ w₁ w₂ w₃ w₄ w₅ tag : BitVec 64) :
    ((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
      ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) ∗ ⌜w₀ = tag⌝ ⊢
      (a ↦₆₄ tag) ∗ memRegion (a + 8#64) 40 := by
  rw [sepConj_comm]; refine ent_pure_left fun hw₀ => ?_; subst hw₀
  have e40 := dpWords5_entails_memRegion40 (a + 8#64) w₁ w₂ w₃ w₄ w₅
  simp only [BitVec.add_assoc, bv8_8, bv8_16, bv8_24] at e40
  exact sepConj_mono (Entails.refl _) e40
private theorem fwd_tag_byte_mem39 (a w₀ w₁ w₂ w₃ w₄ w₅ tag : BitVec 64) (b : BitVec 8) :
    ((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
      ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) ∗
      ⌜w₀ = tag ∧ w₁.extractLsb' 0 8 = b⌝ ⊢
      (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₈ b) ∗ memRegion (a + 9#64) 39 := by
  rw [sepConj_comm]; refine ent_pure_left fun ⟨hw₀, hb⟩ => ?_; subst hw₀
  have hbyte := pointsTo64_byte_entails (a + 8#64) w₁ b hb
  have e32 := dpWords4_entails_memRegion32 (a + 16#64) w₂ w₃ w₄ w₅
  have hsplit : memRegion (a + 9#64) 39 = memRegion (a + 9#64) 7 ∗ memRegion (a + 16#64) 32 := by
    have ha : (a + 9#64) + 7#64 = a + 16#64 := by rw [BitVec.add_assoc]; rfl
    rw [memRegion_split (a + 9#64) 7 32 (by decide), ha]
  simp only [BitVec.add_assoc] at hbyte e32; rw [hsplit, ← sepConj_assoc ((a + 8#64) ↦₈ b)]
  exact sepConj_mono (Entails.refl _) (sepConj_mono hbyte e32)
private theorem fwd_tag_word_mem32 (a w₀ w₁ w₂ w₃ w₄ w₅ tag pay : BitVec 64) :
    ((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
      ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) ∗ ⌜w₀ = tag ∧ w₁ = pay⌝ ⊢
      (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ pay) ∗ memRegion (a + 16#64) 32 := by
  rw [sepConj_comm]; refine ent_pure_left fun ⟨hw₀, hw₁⟩ => ?_; subst hw₀; subst hw₁
  have e32 := dpWords4_entails_memRegion32 (a + 16#64) w₂ w₃ w₄ w₅
  simp only [BitVec.add_assoc] at e32
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) e32)
private theorem fwd_vec_at8_tail16 (A : RustAlloc) (a tag w₁ w₂ w₃ w₄ w₅ : BitVec 64)
    (bs : List (BitVec 8)) (TH T : SepProp)
    (hT : (((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) ∗ TH ⊢ T) :
    (⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs) ∗
      (TH ∗ ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
        ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅))) ⊢
      (a ↦₆₄ tag) ∗ vecU8 A (a + 8#64) bs ∗ T := by
  have hv := vecU8_of_words A (a + 8#64) w₁ w₂ w₃ bs
  simp only [BitVec.add_assoc, bv8_8, bv8_16] at hv
  have rearrange : (⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs) ∗
        (TH ∗ ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
          ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅))) =
      (a ↦₆₄ tag) ∗ ((((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗
          (⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs)) ∗
        ((((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) ∗ TH) := by ac_rfl
  rw [rearrange]; exact sepConj_mono (Entails.refl _) (sepConj_mono hv hT)
/-- Forward sret factorization: the 6 stack words `ws` plus off-stack heap `dpErrHeap A ws k` entail
`RunDrop.speOwnedAt A a k` at any address `a`. -/
theorem dpWords_errHeap_entails_speOwnedAt (A : RustAlloc) (a : BitVec 64)
    (ws : List (BitVec 64)) (k : RunDrop.SpeOwned) :
    dpWordsAt a ws ∗ dpErrHeap A ws k ⊢ RunDrop.speOwnedAt A a k := by
  rcases ws with _ | ⟨w₀, _ | ⟨w₁, _ | ⟨w₂, _ | ⟨w₃, _ | ⟨w₄, _ | ⟨w₅, _ | _⟩⟩⟩⟩⟩⟩
  all_goals try (dsimp only [dpErrHeap]; rw [sepConj_comm]; exact ent_pure_left False.elim)
  rw [dpWords6_eq]
  cases k with
  | badKemKeyType => exact fwd_tag_mem40 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 31)
  | badKemKeyLength => exact fwd_tag_mem40 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 33)
  | plain i _ => exact fwd_tag_mem40 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord i)
  | withString i _ =>
    dsimp only [dpErrHeap, RunDrop.speOwnedAt]
    rw [sepConj_comm, sepConj_assoc]; refine ent_pure_left fun hw₀ => ?_; subst hw₀
    refine ent_bind (Entails.refl _) fun bs => ?_
    have hm16 := dpWords2_entails_memRegion16 (a + 32#64) w₄ w₅
    simp only [BitVec.add_assoc, bv32_8] at hm16
    have he := fwd_vec_at8_tail16 A a (speWord i) w₁ w₂ w₃ w₄ w₅ bs emp
      (memRegion (a + 32#64) 16) (by rw [sepConj_emp]; exact hm16)
    rw [emp_sepConj] at he; exact Entails.trans he (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.sepExists_right bs (Entails.refl _)) (Entails.refl _)))
  | sessionNotFound addr op =>
    dsimp only [dpErrHeap, RunDrop.speOwnedAt, apiErrAt, addrCloneAt]
    rw [sepConj_comm, sepConj_assoc]; refine ent_pure_left fun ⟨hw₂, hw₃⟩ => ?_
    have hv := vecU8_of_words A a w₀ w₁ w₂ addr.name
    have hb := pointsTo64_byte_entails (a + 24#64) w₃ addr.device hw₃
    have hs := strRef_of_words (a + 32#64) w₄ w₅ (LibsignalTripleRatchetRepr.utf8 op)
    simp only [BitVec.add_assoc, bv24_1, bv32_8] at hb hs
    refine Entails.trans (ent_pure_right hw₂ (Entails.refl _)) ?_
    have rearrange : ⌜w₂ = BitVec.ofNat 64 addr.name.length⌝ ∗ ((vecU8Heap A w₀ w₁ addr.name ∗
              strRefHeap w₄ w₅ (LibsignalTripleRatchetRepr.utf8 op)) ∗
            ((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
              ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅))) =
        ((((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂)) ∗
            (⌜w₂ = BitVec.ofNat 64 addr.name.length⌝ ∗ vecU8Heap A w₀ w₁ addr.name)) ∗
          ((a + 24#64) ↦₆₄ w₃)) ∗ ((((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) ∗
            strRefHeap w₄ w₅ (LibsignalTripleRatchetRepr.utf8 op)) := by ac_rfl
    rw [rearrange]
    exact Entails.trans (sepConj_mono (sepConj_mono hv hb) hs) (Entails.of_eq (by ac_rfl))
  | untrustedIdentity addr =>
    dsimp only [dpErrHeap, RunDrop.speOwnedAt, apiErrAt, addrCloneAt]
    rw [sepConj_comm, sepConj_assoc]; refine ent_pure_left fun ⟨hw₀, hw₃, hw₄⟩ => ?_; subst hw₀
    have hv := vecU8_of_words A (a + 8#64) w₁ w₂ w₃ addr.name
    have hb := pointsTo64_byte_entails (a + 32#64) w₄ addr.device hw₄
    have hm8 := pointsTo64_entails_memRegion8 (a + 40#64) w₅
    simp only [BitVec.add_assoc, bv8_8, bv8_16, bv8_24, bv8_25, bv32_1] at hv hb ⊢
    refine Entails.trans (ent_pure_right hw₃ (Entails.refl _)) ?_
    have rearrange : ⌜w₃ = BitVec.ofNat 64 addr.name.length⌝ ∗ (vecU8Heap A w₁ w₂ addr.name ∗
            ((a ↦₆₄ speWord speUntrustedIdentity) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
              ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅))) =
        (a ↦₆₄ speWord speUntrustedIdentity) ∗
          ((((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗
            (⌜w₃ = BitVec.ofNat 64 addr.name.length⌝ ∗ vecU8Heap A w₁ w₂ addr.name)) ∗
          ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅) := by ac_rfl
    rw [rearrange]
    exact Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono hv (sepConj_mono hb hm8)))
      (Entails.of_eq (by ac_rfl))
  | proto fnName e =>
    cases e with
    | panic =>
      dsimp only [dpErrHeap, dpProtoHeap, RunDrop.speOwnedAt, speAt]
      rw [sepConj_comm]; exact ent_pure_left False.elim
    | invalidProtobufEncoding => exact fwd_tag_mem40 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 2)
    | noKeyTypeIdentifier => exact fwd_tag_mem40 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 7)
    | invalidKeyAgreement => exact fwd_tag_mem40 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 10)
    | legacyCiphertextVersion v => exact fwd_tag_byte_mem39 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 4) v
    | unrecognizedCiphertextVersion v => exact fwd_tag_byte_mem39 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 5) v
    | badKeyType t => exact fwd_tag_byte_mem39 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 8) t
    | ciphertextMessageTooShort n =>
      exact fwd_tag_word_mem32 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 3) (BitVec.ofNat 64 n)
    | badKeyLength n =>
      exact fwd_tag_word_mem32 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 9) (BitVec.ofNat 64 n)
    | duplicatedMessage i c =>
      dsimp only [dpErrHeap, dpProtoHeap, RunDrop.speOwnedAt, speAt]
      have hp : ((a + 8#64) ↦₆₄ (c ++ i)) = ((a + 8#64) ↦₃₂ i) ∗ ((a + 12#64) ↦₃₂ c) := by
        have h12 : (a + 8#64) + 4#64 = a + 12#64 := by rw [BitVec.add_assoc]; rfl
        rw [← h12, pointsTo32_pair]
      rw [← sepConj_assoc ((a + 8#64) ↦₃₂ i), ← hp]
      exact fwd_tag_word_mem32 a w₀ w₁ w₂ w₃ w₄ w₅ (speWord 23) (c ++ i)
    | invalidState =>
      dsimp only [dpErrHeap, dpProtoHeap, RunDrop.speOwnedAt, speAt]
      rw [sepConj_comm, sepConj_assoc]; refine ent_pure_left fun hw₀ => ?_; subst hw₀
      rw [sepConj_assoc]; refine ent_bind (Entails.refl _) fun bs => ?_
      have hs := strRef_of_words (a + 32#64) w₄ w₅ fnName; simp only [BitVec.add_assoc, bv32_8] at hs
      exact Entails.trans
        (fwd_vec_at8_tail16 A a (speWord 1) w₁ w₂ w₃ w₄ w₅ bs (strRefHeap w₄ w₅ fnName)
          (strRefAt (a + 32#64) fnName) hs)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.sepExists_right bs (Entails.refl _)) (Entails.refl _)))
    | invalidSessionStructure r =>
      dsimp only [dpErrHeap, dpProtoHeap, RunDrop.speOwnedAt, speAt]
      rw [sepConj_comm, sepConj_assoc]; refine ent_pure_left fun hw₀ => ?_; subst hw₀
      have hs := strRef_of_words (a + 8#64) w₁ w₂ (invalidSessionStructureStr r)
      have hm24 := dpWords3_entails_memRegion24 (a + 24#64) w₃ w₄ w₅
      simp only [BitVec.add_assoc, bv8_8, bv24_8, bv24_16] at hs hm24
      have rearrange : strRefHeap w₁ w₂ (invalidSessionStructureStr r) ∗
            ((a ↦₆₄ speWord 20) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
              ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) =
          (a ↦₆₄ speWord 20) ∗
            ((((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂)) ∗ strRefHeap w₁ w₂ (invalidSessionStructureStr r)) ∗
            (((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) := by ac_rfl
      rw [rearrange]; exact sepConj_mono (Entails.refl _) (sepConj_mono hs hm24)
    | invalidMessage t r =>
      dsimp only [dpErrHeap, dpProtoHeap, RunDrop.speOwnedAt, speAt]
      rw [sepConj_comm, sepConj_assoc]; refine ent_pure_left fun ⟨hw₀, hw₄⟩ => ?_; subst hw₀
      have him := invalidMsg_of_words A (a + 8#64) w₁ w₂ w₃ r
      have hb := pointsTo64_byte_entails (a + 32#64) w₄ (msgTypeByte t) hw₄
      have hm8 := pointsTo64_entails_memRegion8 (a + 40#64) w₅
      have hsplit : memRegion (a + 33#64) 15 = memRegion (a + 33#64) 7 ∗ memRegion (a + 40#64) 8 := by
        have ha : (a + 33#64) + 7#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
        rw [memRegion_split (a + 33#64) 7 8 (by decide), ha]
      simp only [BitVec.add_assoc, bv8_8, bv8_16, bv32_1] at him hb
      have rearrange : invalidMsgStrHeap A w₁ w₂ w₃ r ∗
            ((a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
              ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) =
          (a ↦₆₄ speWord 24) ∗ ((((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗
              invalidMsgStrHeap A w₁ w₂ w₃ r) ∗
            ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅) := by ac_rfl
      rw [rearrange, hsplit]
      exact Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono him (sepConj_mono hb hm8)))
        (Entails.of_eq (by ac_rfl))
private theorem mk_dpWords6 {P Q : SepProp} {F : List (BitVec 64) → SepProp}
    (a w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) (hne : w₀ ≠ pendingTag)
    (hQ : Q ⊢ ((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
      ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) ∗ P)
    (hF : P ⊢ F [w₀, w₁, w₂, w₃, w₄, w₅]) : Q ⊢ ∃∗ ws : List (BitVec 64),
      ⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt a ws ∗ F ws := by
  refine Entails.trans hQ (Entails.sepExists_right [w₀, w₁, w₂, w₃, w₄, w₅] ?_)
  rw [dpWords6_eq]
  exact ent_pure_right ⟨rfl, fun h => hne (Option.some.inj h)⟩ (sepConj_mono (Entails.refl _) hF)
private theorem conv_tag_mem40 {F : List (BitVec 64) → SepProp} (a tag : BitVec 64)
    (hne : tag ≠ pendingTag) (hF : ∀ w₁ w₂ w₃ w₄ w₅, F [tag, w₁, w₂, w₃, w₄, w₅] = ⌜tag = tag⌝) :
    (a ↦₆₄ tag) ∗ memRegion (a + 8#64) 40 ⊢ ∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt a ws ∗ F ws := by
  rw [sepConj_comm]; refine ent_bind (memRegion40_words (a + 8#64)) fun ⟨w₁, w₂, w₃, w₄, w₅⟩ => ?_
  simp only [BitVec.add_assoc, bv8_8, bv8_16, bv8_24]
  exact mk_dpWords6 a tag w₁ w₂ w₃ w₄ w₅ hne (P := emp) (Entails.of_eq (by ac_rfl))
    (by rw [hF]; exact emp_entails_pure rfl)
private theorem conv_tag_byte_mem39 {F : List (BitVec 64) → SepProp} (a tag : BitVec 64)
    (b : BitVec 8) (hne : tag ≠ pendingTag) (hF : ∀ w₁ w₂ w₃ w₄ w₅, F [tag, w₁, w₂, w₃, w₄, w₅] =
      ⌜tag = tag ∧ w₁.extractLsb' 0 8 = b⌝) :
    (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₈ b) ∗ memRegion (a + 9#64) 39 ⊢ ∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt a ws ∗ F ws := by
  have h16 : (a + 9#64) + 7#64 = a + 16#64 := by rw [BitVec.add_assoc]; rfl
  have h9 : (a + 8#64) + 1#64 = a + 9#64 := by rw [BitVec.add_assoc]; rfl
  rw [memRegion_split (a + 9#64) 7 32 (by decide), h16]
  have rearrange :
      (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₈ b) ∗ (memRegion (a + 9#64) 7 ∗ memRegion (a + 16#64) 32) =
      (((a + 8#64) ↦₈ b) ∗ memRegion ((a + 8#64) + 1#64) 7) ∗
        (memRegion (a + 16#64) 32 ∗ (a ↦₆₄ tag)) := by rw [h9]; ac_rfl
  rw [rearrange]; refine ent_bind (byte_memRegion7_words (a + 8#64) b) fun w₁ => ?_
  rw [sepConj_assoc]; refine ent_pure_left fun hw₁ => ?_
  have rearrange2 : ((a + 8#64) ↦₆₄ w₁) ∗ (memRegion (a + 16#64) 32 ∗ (a ↦₆₄ tag)) =
      memRegion (a + 16#64) 32 ∗ ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w₁)) := by ac_rfl
  rw [rearrange2]; refine ent_bind (memRegion32_words (a + 16#64)) fun ⟨w₂, w₃, w₄, w₅⟩ => ?_
  simp only [BitVec.add_assoc]
  exact mk_dpWords6 a tag w₁ w₂ w₃ w₄ w₅ hne (P := emp) (Entails.of_eq (by ac_rfl))
    (by rw [hF]; exact emp_entails_pure ⟨rfl, hw₁⟩)
private theorem conv_tag_word_mem32 {F : List (BitVec 64) → SepProp} (a tag pay : BitVec 64)
    (hne : tag ≠ pendingTag)
    (hF : ∀ w₂ w₃ w₄ w₅, F [tag, pay, w₂, w₃, w₄, w₅] = ⌜tag = tag ∧ pay = pay⌝) :
    (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ pay) ∗ memRegion (a + 16#64) 32 ⊢ ∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt a ws ∗ F ws := by
  have rearrange : (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ pay) ∗ memRegion (a + 16#64) 32 =
      memRegion (a + 16#64) 32 ∗ ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ pay)) := by ac_rfl
  rw [rearrange]; refine ent_bind (memRegion32_words (a + 16#64)) fun ⟨w₂, w₃, w₄, w₅⟩ => ?_
  simp only [BitVec.add_assoc]
  exact mk_dpWords6 a tag pay w₂ w₃ w₄ w₅ hne (P := emp) (Entails.of_eq (by ac_rfl))
    (by rw [hF]; exact emp_entails_pure ⟨rfl, rfl⟩)
private theorem conv_vec_at8_tail16 (A : RustAlloc) {TH : BitVec 64 → BitVec 64 → SepProp}
    {F : List (BitVec 64) → SepProp}
    (a tag : BitVec 64) (bs : List (BitVec 8)) (T : SepProp) (hne : tag ≠ pendingTag)
    (hT : T ⊢ ∃∗ p : BitVec 64 × BitVec 64,
      (((a + 32#64) ↦₆₄ p.1) ∗ ((a + 40#64) ↦₆₄ p.2)) ∗ TH p.1 p.2)
    (hF : ∀ w₁ w₂ w₃ w₄ w₅, (⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs) ∗ TH w₄ w₅ ⊢
        F [tag, w₁, w₂, w₃, w₄, w₅]) :
    vecU8 A (a + 8#64) bs ∗ (T ∗ (a ↦₆₄ tag)) ⊢ ∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt a ws ∗ F ws := by
  refine ent_bind (vecU8_words A (a + 8#64) bs) fun ⟨w₁, w₂, w₃⟩ => ?_
  simp only [BitVec.add_assoc, bv8_8, bv8_16]
  have r2 : ((((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗
        (⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs)) ∗ (T ∗ (a ↦₆₄ tag)) =
      T ∗ ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃) ∗
        (⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs)) := by ac_rfl
  rw [r2]; refine ent_bind hT fun ⟨w₄, w₅⟩ => ?_
  exact mk_dpWords6 a tag w₁ w₂ w₃ w₄ w₅ hne
    (P := (⌜w₃ = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Heap A w₁ w₂ bs) ∗ TH w₄ w₅)
    (Entails.of_eq (by ac_rfl)) (hF w₁ w₂ w₃ w₄ w₅)
private theorem conv_mid24_byte32_mem8 {MH : BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {F : List (BitVec 64) → SepProp}
    (a tag : BitVec 64) (b : BitVec 8) (M : SepProp) (hne : tag ≠ pendingTag)
    (hM : M ⊢ ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64,
      (((a + 8#64) ↦₆₄ t.1) ∗ ((a + 16#64) ↦₆₄ t.2.1) ∗ ((a + 24#64) ↦₆₄ t.2.2)) ∗ MH t.1 t.2.1 t.2.2)
    (hF : ∀ w₁ w₂ w₃ w₄ w₅, w₄.extractLsb' 0 8 = b → MH w₁ w₂ w₃ ⊢ F [tag, w₁, w₂, w₃, w₄, w₅]) :
    M ∗ ((((a + 32#64) ↦₈ b) ∗ memRegion ((a + 32#64) + 1#64) 7) ∗
      memRegion (a + 40#64) 8 ∗ (a ↦₆₄ tag)) ⊢ ∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt a ws ∗ F ws := by
  refine ent_bind hM fun ⟨w₁, w₂, w₃⟩ => ?_
  have r2 : ((((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗ MH w₁ w₂ w₃) ∗
        ((((a + 32#64) ↦₈ b) ∗ memRegion ((a + 32#64) + 1#64) 7) ∗
          memRegion (a + 40#64) 8 ∗ (a ↦₆₄ tag)) =
      (((a + 32#64) ↦₈ b) ∗ memRegion ((a + 32#64) + 1#64) 7) ∗ (memRegion (a + 40#64) 8 ∗
          ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗
          MH w₁ w₂ w₃) := by ac_rfl
  rw [r2]; refine ent_bind (byte_memRegion7_words (a + 32#64) b) fun w₄ => ?_
  rw [sepConj_assoc]; refine ent_pure_left fun hw₄ => ?_
  have r3 : ((a + 32#64) ↦₆₄ w₄) ∗ (memRegion (a + 40#64) 8 ∗
          ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗
          MH w₁ w₂ w₃) =
      memRegion (a + 40#64) 8 ∗ (((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
          ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄)) ∗ MH w₁ w₂ w₃) := by ac_rfl
  rw [r3]; refine ent_bind (memRegion8_words (a + 40#64)) fun w₅ => ?_
  exact mk_dpWords6 a tag w₁ w₂ w₃ w₄ w₅ hne (P := MH w₁ w₂ w₃)
    (Entails.of_eq (by ac_rfl)) (hF w₁ w₂ w₃ w₄ w₅ hw₄)
/-- Converse sret factorization: `RunDrop.speOwnedAt A a k` entails 6 non-pending stack words `ws`
(`ws.head? ≠ some pendingTag`) together with `dpWordsAt a ws ∗ dpErrHeap A ws k`. -/
theorem speOwnedAt_entails_dpWords_errHeap (A : RustAlloc) (a : BitVec 64) (k : RunDrop.SpeOwned) :
    RunDrop.speOwnedAt A a k ⊢ ∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt a ws ∗ dpErrHeap A ws k := by
  cases k with
  | badKemKeyType => exact conv_tag_mem40 a (speWord 31) (by decide) (fun _ _ _ _ _ => rfl)
  | badKemKeyLength => exact conv_tag_mem40 a (speWord 33) (by decide) (fun _ _ _ _ _ => rfl)
  | plain i hi =>
    exact conv_tag_mem40 a (speWord i) (plainSpeTag_ne_pending hi) (fun _ _ _ _ _ => rfl)
  | withString i hi =>
    dsimp only [RunDrop.speOwnedAt]
    have r1 : (a ↦₆₄ speWord i) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ∗
          memRegion (a + 32#64) 16 =
        (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ∗
          (memRegion (a + 32#64) 16 ∗ (a ↦₆₄ speWord i)) := by ac_rfl
    rw [r1]; refine ent_bind (Entails.refl _) fun bs => ?_
    have hm := memRegion16_words (a + 32#64); simp only [BitVec.add_assoc, bv32_8] at hm
    refine conv_vec_at8_tail16 A a (speWord i) bs (memRegion (a + 32#64) 16)
      (strSpeTag_ne_pending hi) (TH := fun _ _ => emp)
      (Entails.trans hm (Entails.sepExists_elim fun p =>
        Entails.sepExists_right p (Entails.of_eq (sepConj_emp _).symm)))
      fun w₁ w₂ w₃ _ _ => ?_
    dsimp only [dpErrHeap]; rw [sepConj_emp, pure_sepConj_eq_of_true _ rfl]
    exact Entails.sepExists_right bs (Entails.refl _)
  | sessionNotFound addr op =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt]
    have r1 : (vecU8 A a addr.name ∗ ((a + 24#64) ↦₈ addr.device) ∗ memRegion (a + 25#64) 7) ∗
          strRefAt (a + 32#64) (LibsignalTripleRatchetRepr.utf8 op) =
        vecU8 A a addr.name ∗ ((((a + 24#64) ↦₈ addr.device) ∗ memRegion ((a + 24#64) + 1#64) 7) ∗
            strRefAt (a + 32#64) (LibsignalTripleRatchetRepr.utf8 op)) := by
      simp only [BitVec.add_assoc, bv24_1]; ac_rfl
    rw [r1]; refine ent_bind (vecU8_words A a addr.name) fun ⟨w₀, w₁, w₂⟩ => ?_
    have r2 : (((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂)) ∗
          (⌜w₂ = BitVec.ofNat 64 addr.name.length⌝ ∗ vecU8Heap A w₀ w₁ addr.name)) ∗
          ((((a + 24#64) ↦₈ addr.device) ∗ memRegion ((a + 24#64) + 1#64) 7) ∗
            strRefAt (a + 32#64) (LibsignalTripleRatchetRepr.utf8 op)) =
        (((a + 24#64) ↦₈ addr.device) ∗ memRegion ((a + 24#64) + 1#64) 7) ∗
          (strRefAt (a + 32#64) (LibsignalTripleRatchetRepr.utf8 op) ∗
            ((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂)) ∗
            (⌜w₂ = BitVec.ofNat 64 addr.name.length⌝ ∗ vecU8Heap A w₀ w₁ addr.name)) := by ac_rfl
    rw [r2]; refine ent_bind (byte_memRegion7_words (a + 24#64) addr.device) fun w₃ => ?_
    rw [sepConj_assoc]; refine ent_pure_left fun hw₃ => ?_
    have r3 : ((a + 24#64) ↦₆₄ w₃) ∗ (strRefAt (a + 32#64) (LibsignalTripleRatchetRepr.utf8 op) ∗
            ((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂)) ∗
            (⌜w₂ = BitVec.ofNat 64 addr.name.length⌝ ∗ vecU8Heap A w₀ w₁ addr.name)) =
        strRefAt (a + 32#64) (LibsignalTripleRatchetRepr.utf8 op) ∗
          (((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗
            (⌜w₂ = BitVec.ofNat 64 addr.name.length⌝ ∗ vecU8Heap A w₀ w₁ addr.name)) := by ac_rfl
    rw [r3]
    refine ent_bind (strRef_words (a + 32#64) (LibsignalTripleRatchetRepr.utf8 op)) fun ⟨w₄, w₅⟩ => ?_
    simp only [BitVec.add_assoc, bv32_8]
    have r4 : ((((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)) ∗
          strRefHeap w₄ w₅ (LibsignalTripleRatchetRepr.utf8 op)) ∗
          (((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗ ((a + 24#64) ↦₆₄ w₃)) ∗
            (⌜w₂ = BitVec.ofNat 64 addr.name.length⌝ ∗ vecU8Heap A w₀ w₁ addr.name)) =
        ⌜w₂ = BitVec.ofNat 64 addr.name.length⌝ ∗ (vecU8Heap A w₀ w₁ addr.name ∗
            (strRefHeap w₄ w₅ (LibsignalTripleRatchetRepr.utf8 op) ∗
              ((a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
                ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) ∗ ((a + 40#64) ↦₆₄ w₅)))) := by ac_rfl
    rw [r4]; refine ent_pure_left fun hw₂ => ?_
    unfold vecU8Heap; rw [sepConj_assoc]; refine ent_pure_peek fun ⟨_, hcap, _⟩ => ?_
    rw [← sepConj_assoc]; change vecU8Heap A w₀ w₁ addr.name ∗ _ ⊢ _
    refine mk_dpWords6 a w₀ w₁ w₂ w₃ w₄ w₅ (cap_lt_half_ne_pending hcap)
      (P := vecU8Heap A w₀ w₁ addr.name ∗ strRefHeap w₄ w₅ (LibsignalTripleRatchetRepr.utf8 op))
      (Entails.of_eq (by ac_rfl)) ?_
    dsimp only [dpErrHeap]; exact ent_pure_right ⟨hw₂, hw₃⟩ (Entails.refl _)
  | untrustedIdentity addr =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt]
    simp only [BitVec.add_assoc, bv8_24, bv8_25]
    have r1 : (a ↦₆₄ speWord speUntrustedIdentity) ∗
          (vecU8 A (a + 8#64) addr.name ∗ ((a + 32#64) ↦₈ addr.device) ∗ memRegion (a + 33#64) 7) ∗
          memRegion (a + 40#64) 8 =
        vecU8 A (a + 8#64) addr.name ∗
          ((((a + 32#64) ↦₈ addr.device) ∗ memRegion ((a + 32#64) + 1#64) 7) ∗
            memRegion (a + 40#64) 8 ∗ (a ↦₆₄ speWord speUntrustedIdentity)) := by
      simp only [BitVec.add_assoc, bv32_1]; ac_rfl
    rw [r1]
    have hv := vecU8_words A (a + 8#64) addr.name; simp only [BitVec.add_assoc, bv8_8, bv8_16] at hv
    refine conv_mid24_byte32_mem8
      (MH := fun w₁ w₂ w₃ => ⌜w₃ = BitVec.ofNat 64 addr.name.length⌝ ∗ vecU8Heap A w₁ w₂ addr.name)
      a (speWord speUntrustedIdentity) addr.device
      (vecU8 A (a + 8#64) addr.name) (by decide) hv fun w₁ w₂ w₃ w₄ w₅ hw₄ => ?_
    dsimp only [dpErrHeap]
    exact ent_pure_left fun hw₃ => ent_pure_right ⟨rfl, hw₃, hw₄⟩ (Entails.refl _)
  | proto fnName e =>
    cases e with
    | panic => exact false_entails _
    | invalidProtobufEncoding => exact conv_tag_mem40 a (speWord 2) (by decide) (fun _ _ _ _ _ => rfl)
    | noKeyTypeIdentifier => exact conv_tag_mem40 a (speWord 7) (by decide) (fun _ _ _ _ _ => rfl)
    | invalidKeyAgreement => exact conv_tag_mem40 a (speWord 10) (by decide) (fun _ _ _ _ _ => rfl)
    | legacyCiphertextVersion v =>
      exact conv_tag_byte_mem39 a (speWord 4) v (by decide) (fun _ _ _ _ _ => rfl)
    | unrecognizedCiphertextVersion v =>
      exact conv_tag_byte_mem39 a (speWord 5) v (by decide) (fun _ _ _ _ _ => rfl)
    | badKeyType t =>
      exact conv_tag_byte_mem39 a (speWord 8) t (by decide) (fun _ _ _ _ _ => rfl)
    | ciphertextMessageTooShort n =>
      exact conv_tag_word_mem32 a (speWord 3) (BitVec.ofNat 64 n) (by decide) (fun _ _ _ _ => rfl)
    | badKeyLength n =>
      exact conv_tag_word_mem32 a (speWord 9) (BitVec.ofNat 64 n) (by decide) (fun _ _ _ _ => rfl)
    | duplicatedMessage i c =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      have hp : ((a + 8#64) ↦₃₂ i) ∗ ((a + 12#64) ↦₃₂ c) = ((a + 8#64) ↦₆₄ (c ++ i)) := by
        have h12 : (a + 8#64) + 4#64 = a + 12#64 := by rw [BitVec.add_assoc]; rfl
        rw [← h12, pointsTo32_pair]
      rw [← sepConj_assoc ((a + 8#64) ↦₃₂ i), hp]
      exact conv_tag_word_mem32 a (speWord 23) (c ++ i) (by decide) (fun _ _ _ _ => rfl)
    | invalidSessionStructure r =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      have r1 : (a ↦₆₄ speWord 20) ∗ strRefAt (a + 8#64) (invalidSessionStructureStr r) ∗ memRegion (a + 24#64) 24 =
          strRefAt (a + 8#64) (invalidSessionStructureStr r) ∗ (memRegion (a + 24#64) 24 ∗ (a ↦₆₄ speWord 20)) := by ac_rfl
      rw [r1]; refine ent_bind (strRef_words (a + 8#64) (invalidSessionStructureStr r)) fun ⟨w₁, w₂⟩ => ?_
      simp only [BitVec.add_assoc, bv8_8]
      have r2 : ((((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂)) ∗ strRefHeap w₁ w₂ (invalidSessionStructureStr r)) ∗
            (memRegion (a + 24#64) 24 ∗ (a ↦₆₄ speWord 20)) =
          memRegion (a + 24#64) 24 ∗ ((a ↦₆₄ speWord 20) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
              strRefHeap w₁ w₂ (invalidSessionStructureStr r)) := by ac_rfl
      rw [r2]; refine ent_bind (memRegion24_words (a + 24#64)) fun ⟨w₃, w₄, w₅⟩ => ?_
      simp only [BitVec.add_assoc, bv24_8, bv24_16]
      refine mk_dpWords6 a (speWord 20) w₁ w₂ w₃ w₄ w₅ (by decide)
        (P := strRefHeap w₁ w₂ (invalidSessionStructureStr r)) (Entails.of_eq (by ac_rfl)) ?_
      dsimp only [dpErrHeap, dpProtoHeap]; exact ent_pure_right rfl (Entails.refl _)
    | invalidState =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      have r1 : (a ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ∗
            strRefAt (a + 32#64) fnName =
          (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ∗
            (strRefAt (a + 32#64) fnName ∗ (a ↦₆₄ speWord 1)) := by ac_rfl
      rw [r1]; refine ent_bind (Entails.refl _) fun bs => ?_
      have hs := strRef_words (a + 32#64) fnName; simp only [BitVec.add_assoc, bv32_8] at hs
      refine conv_vec_at8_tail16 A a (speWord 1) bs (strRefAt (a + 32#64) fnName) (by decide)
        (TH := fun w₄ w₅ => strRefHeap w₄ w₅ fnName) hs fun w₁ w₂ w₃ w₄ w₅ => ?_
      dsimp only [dpErrHeap, dpProtoHeap]; rw [pure_sepConj_eq_of_true _ rfl]
      exact sepConj_mono (Entails.sepExists_right bs (Entails.refl _)) (Entails.refl _)
    | invalidMessage t r =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      have h40 : (a + 33#64) + 7#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
      rw [memRegion_split (a + 33#64) 7 8 (by decide), h40]
      have r1 : (a ↦₆₄ speWord 24) ∗ invalidMessageStrAt A (a + 8#64) r ∗
            ((a + 32#64) ↦₈ msgTypeByte t) ∗ (memRegion (a + 33#64) 7 ∗ memRegion (a + 40#64) 8) =
          invalidMessageStrAt A (a + 8#64) r ∗
            ((((a + 32#64) ↦₈ msgTypeByte t) ∗ memRegion ((a + 32#64) + 1#64) 7) ∗
              memRegion (a + 40#64) 8 ∗ (a ↦₆₄ speWord 24)) := by
        simp only [BitVec.add_assoc, bv32_1]; ac_rfl
      rw [r1]
      have hm := invalidMsg_words A (a + 8#64) r; simp only [BitVec.add_assoc, bv8_8, bv8_16] at hm
      refine conv_mid24_byte32_mem8 (MH := fun w₁ w₂ w₃ => invalidMsgStrHeap A w₁ w₂ w₃ r)
        a (speWord 24) (msgTypeByte t)
        (invalidMessageStrAt A (a + 8#64) r) (by decide) hm fun w₁ w₂ w₃ w₄ w₅ hw₄ => ?_
      dsimp only [dpErrHeap, dpProtoHeap]; exact ent_pure_right ⟨rfl, hw₄⟩ (Entails.refl _)
/-- Forward sret factorization for `decResAt A a e`. -/
theorem dpWords_resHeap_entails_decResAt (A : RustAlloc) (a : BitVec 64)
    (ws : List (BitVec 64)) (e : Except (ApiError AddrVal Unit) Bytes) :
    dpWordsAt a ws ∗ dpResHeap A ws e ⊢ decResAt A a e := by
  cases e with
  | error _ =>
    dsimp only [dpResHeap, decResAt]; rw [sepConj_comm]
    refine ent_bind (Entails.refl _) fun k => ?_; rw [sepConj_comm]
    exact Entails.trans (dpWords_errHeap_entails_speOwnedAt A a ws k)
      (Entails.sepExists_right k (Entails.refl _))
  | ok pt =>
    rcases ws with _ | ⟨w₀, _ | ⟨w₁, _ | ⟨w₂, _ | ⟨w₃, _ | ⟨w₄, _ | ⟨w₅, _ | _⟩⟩⟩⟩⟩⟩
    all_goals try (dsimp only [dpResHeap]; rw [sepConj_comm]; exact ent_pure_left False.elim)
    rw [dpWords6_eq]; dsimp only [dpResHeap, decResAt, vecResultAt]
    rw [sepConj_comm, sepConj_assoc]; refine ent_pure_left fun ⟨hw₀, hw₃⟩ => ?_; subst hw₀
    have hm16 := dpWords2_entails_memRegion16 (a + 32#64) w₄ w₅
    simp only [BitVec.add_assoc, bv32_8] at hm16
    have he := fwd_vec_at8_tail16 A a okTagVec w₁ w₂ w₃ w₄ w₅ pt emp
      (memRegion (a + 32#64) 16) (by rw [sepConj_emp]; exact hm16)
    rw [emp_sepConj, sepConj_assoc] at he
    exact Entails.trans (ent_pure_right hw₃ (Entails.refl _)) he
/-- Converse sret factorization for `decResAt A a e`. -/
theorem decResAt_entails_dpWords_resHeap (A : RustAlloc) (a : BitVec 64)
    (e : Except (ApiError AddrVal Unit) Bytes) : decResAt A a e ⊢ ∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗ dpWordsAt a ws ∗ dpResHeap A ws e := by
  cases e with
  | error _ =>
    dsimp only [decResAt, dpResHeap]; refine Entails.sepExists_elim fun k =>
      Entails.trans (speOwnedAt_entails_dpWords_errHeap A a k) (Entails.sepExists_elim fun ws => ?_)
    exact Entails.sepExists_right ws (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _) (Entails.sepExists_right k (Entails.refl _))))
  | ok pt =>
    dsimp only [decResAt, vecResultAt]
    have r1 : (a ↦₆₄ okTagVec) ∗ vecU8 A (a + 8#64) pt ∗ memRegion (a + 32#64) 16 =
        vecU8 A (a + 8#64) pt ∗ (memRegion (a + 32#64) 16 ∗ (a ↦₆₄ okTagVec)) := by ac_rfl
    rw [r1]
    have hm := memRegion16_words (a + 32#64); simp only [BitVec.add_assoc, bv32_8] at hm
    refine conv_vec_at8_tail16 A a okTagVec pt (memRegion (a + 32#64) 16) (by decide)
      (TH := fun _ _ => emp) (Entails.trans hm (Entails.sepExists_elim fun p =>
        Entails.sepExists_right p (Entails.of_eq (sepConj_emp _).symm)))
      fun w₁ w₂ w₃ _ _ => ?_
    dsimp only [dpResHeap]; rw [sepConj_emp]
    refine ent_pure_left fun hw₃ => ent_pure_right ⟨rfl, hw₃⟩ (Entails.refl _)
end SpeBijectionProofs

/-! ## 4. `(fs, trace)` coupling diagnostics, `dpSlotPollKState`, and slot theorems -/

/-- The 13 ABI argument words passed to `decrypt_prekey` (`x0..x7` + 5 stack words `[sp..sp+32]`). -/
def dpSlotArgs (img : Obj.Image) (x : DecPkGhost) : List (BitVec 64) :=
  [ x.msgA, x.peerA, x.meA, x.stores + 240#64, sessVt img, x.stores, idVt img, x.stores + 200#64,
    oneTimeVt img, x.stores + 80#64, signedVt img, x.stores + 120#64, kyberVt img ]

/-- `(dpPollSpec K stk).pre` is independent of `s0.fs`, motivating `RunProofs.DpPollKState` whose
invariant observes `(fs, trace)`. -/
theorem dpPollSpec_fs_unconstrained (K : DpPollK) (stk : Nat) (x : DpPollGhost K)
    (s0 : State) (fs' : FsState) :
    (dpPollSpec K stk).pre x { s0 with fs := fs' } = (dpPollSpec K stk).pre x s0 :=
  rfl

/-- `(cliDecryptPrekeySpec K stk).post` factors as a Cartesian product of `(fs, trace)` and memory
unless `res` couples `(fs0, tr0, fs1, tr1, ws)` as in `RunProofs.DpPollKState`. -/
theorem cliDecryptPrekeySpec_io_res_cartesian (K : DpPollK) (stk : Nat)
    (x : DecryptPrekeyGhost K) (R : SepProp) (s0 sf₁ sf₂ : State)
    (h₁ : sf₁.mem ⊨ (cliDecryptPrekeySpec K stk).post x s0 sf₁ ∗ R)
    (h₂ : sf₂.mem ⊨ (cliDecryptPrekeySpec K stk).post x s0 sf₂ ∗ R) :
    let sfCross : State := { sf₂ with fs := sf₁.fs, trace := sf₁.trace }
    sfCross.mem ⊨ (cliDecryptPrekeySpec K stk).post x s0 sfCross ∗ R := by
  intro sfCross
  unfold cliDecryptPrekeySpec at h₁ h₂ ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at h₁ h₂ ⊢
  exact ⟨h₁.1, h₂.2⟩

/-- `(fs, trace)`-only form of `slotTrace` (`Sem.lean`). -/
def slotTraceFT (fs0 : FsState) (tr0 : List TraceEvent)
    (fs1 : FsState) (tr1 : List TraceEvent) : Prop :=
  tr0 <+: tr1 ∧ fs1.files = fs0.files ∧
    ProcessOutcome.traceStreamBytes .stdout tr1 =
      ProcessOutcome.traceStreamBytes .stdout tr0

/-- Trace-only form of `slotOut` (`Sem.lean`). -/
def slotOutTr {α : Type} (ans : SlotAns α) (g' : StoresGhost)
    (e : Except (ApiError AddrVal Unit) α) (_tr0 _tr1 : List TraceEvent) : Prop :=
  e ≠ .error .panic ∧ e ≠ .error (.store ()) ∧
    match e with
    | .ok v => ans = some (some (g', v)) ∧ ∀ pw ∈ g'.writes, cliWrOk pw.1
    | .error _ => ans = some none

theorem slotTrace_iff_FT (s0 sf : State) :
    slotTrace s0 sf ↔ slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
  Iff.rfl

theorem slotOut_iff_Tr {α : Type} (a : SlotAns α) (g' : StoresGhost)
    (e : Except (ApiError AddrVal Unit) α) (s0 sf : State) :
    slotOut a g' e s0 sf ↔ slotOutTr a g' e s0.trace sf.trace :=
  Iff.rfl

/-- Polymorphic state-coupled `RunProofs.DpPollKState` over `(fs, trace)` supporting full `slotOut`. -/
def dpSlotPollKState (A : RustAlloc) (img : Obj.Image) (B : RunBudgets) (S : RunSem) :
    RunProofs.DpPollKState where
  Ghost := DecPkGhost
  args := dpSlotArgs img
  inv := fun x fs _ => ⌜fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.decPkOk x.F x.peer.val x.me.val x.msg⌝ ∗
      slotFrame A img x.toSlotCtx ∗ preKeyMsgAt A x.msgG x.msgA x.msg
  res := fun x fs0 tr0 fs1 tr1 ws =>
    ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
      ⌜slotTraceFT fs0 tr0 fs1 tr1 ∧
        slotOutTr (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e tr0 tr1⌝ ∗
        storesAt A x.stores g' ∗ dpResHeap A ws e ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        preKeyMsgAt A x.msgG x.msgA x.msg ∗ logOff img ∗ A.pool ∗ anyHeap
  panics := fun x => S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none
  need := dpPollNeed B

/-- Concrete state-coupled poll contract `K₀_state` at `E2E.HooksE.A0`. -/
abbrev K₀_state (img : Obj.Image) (B : RunBudgets) (S : RunSem) : RunProofs.DpPollKState :=
  dpSlotPollKState E2E.HooksE.A0 img B S

section ConsequenceHelpers

private theorem subroutine_ok_of_outcome_map {α β : Type} {prog : Program} {entry : BitVec 64}
    {spec₁ : Spec α} {spec₂ : Spec β} (f : β → α) (h : subroutine_ok prog entry spec₁)
    (hconseq : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec₂.pre y s0 ∗ R) →
        (s0.mem ⊨ spec₁.pre (f y) s0 ∗ R) ∧
          ∀ sf, SubroutineOutcome spec₁ (f y) R s0 sf → SubroutineOutcome spec₂ y R s0 sf) :
    subroutine_ok prog entry spec₂ :=
  subroutine_ok.of_codeLoaded fun y R s0 hpc hrun hpre hsp _ => let ⟨hpre₁, hm⟩ := hconseq y R s0 hpre
    h.mono_outcome (f y) R s0 hpc hrun hpre₁ hsp hm

private theorem dpSlotStack5_eq (sp : BitVec 64) (img : Obj.Image) (x : DecPkGhost) :
    dpWordsAt sp ((dpSlotArgs img x).drop 8) =
      (sp ↦₆₄ oneTimeVt img) ∗ ((sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
        ((sp + 16#64) ↦₆₄ signedVt img) ∗ ((sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
        ((sp + 32#64) ↦₆₄ kyberVt img) :=
  dpWords5_eq sp (oneTimeVt img) (x.stores + 80#64) (signedVt img) (x.stores + 120#64) (kyberVt img)

private theorem dpSlotState_post_entails (A : RustAlloc) (img : Obj.Image) (B : RunBudgets)
    (S : RunSem) (stk : Nat) (x : DecPkGhost) (s0 sf : State) :
    (RunProofs.cliDecryptPrekeySpecState (dpSlotPollKState A img B S) stk).post ⟨x.ret, x⟩ s0 sf ⊢
      (decPkSlotSpec A img S stk).post x s0 sf := by
  unfold RunProofs.cliDecryptPrekeySpecState; refine ent_bind (Entails.refl _) fun ws => ?_
  rw [sepConj_assoc]; refine ent_pure_left fun _ => ?_
  have r1 : (dpWordsAt x.ret ws ∗
          (dpSlotPollKState A img B S).res x s0.fs s0.trace sf.fs sf.trace ws) ∗
        (dpWordsAt s0.sp (((dpSlotPollKState A img B S).args x).drop 8) ∗ stackAt s0.sp stk) =
      (dpSlotPollKState A img B S).res x s0.fs s0.trace sf.fs sf.trace ws ∗ (dpWordsAt x.ret ws ∗
          dpWordsAt s0.sp ((dpSlotArgs img x).drop 8) ∗ stackAt s0.sp stk) := by ac_rfl
  rw [r1]; unfold dpSlotPollKState; refine ent_bind (Entails.refl _) fun g' => ?_
  refine ent_bind (Entails.refl _) fun e => ?_
  rw [sepConj_assoc]; refine ent_pure_left fun ⟨htrace, hout⟩ => ?_
  rw [dpSlotStack5_eq]
  have r2 : (storesAt A x.stores g' ∗ dpResHeap A ws e ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        preKeyMsgAt A x.msgG x.msgA x.msg ∗ logOff img ∗ A.pool ∗ anyHeap) ∗ (dpWordsAt x.ret ws ∗
          ((s0.sp ↦₆₄ oneTimeVt img) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
            ((s0.sp + 16#64) ↦₆₄ signedVt img) ∗ ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
            ((s0.sp + 32#64) ↦₆₄ kyberVt img)) ∗ stackAt s0.sp stk) =
      (dpWordsAt x.ret ws ∗ dpResHeap A ws e) ∗ (storesAt A x.stores g' ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          preKeyMsgAt A x.msgG x.msgA x.msg ∗
          (s0.sp ↦₆₄ oneTimeVt img) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
          ((s0.sp + 16#64) ↦₆₄ signedVt img) ∗ ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
          ((s0.sp + 32#64) ↦₆₄ kyberVt img) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap) := by ac_rfl
  rw [r2]; refine Entails.trans (sepConj_mono_left (dpWords_resHeap_entails_decResAt A x.ret ws e)) ?_
  unfold decPkSlotSpec Spec.inImage; refine Entails.sepExists_right g' (Entails.sepExists_right e ?_)
  exact ent_pure_right ⟨htrace, hout⟩ (Entails.of_eq (by ac_rfl))

end ConsequenceHelpers

/-- Polymorphic state-coupled wrapper-to-slot adapter for `decrypt_prekey`. -/
theorem dpSlot_ok_state_inImage {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets) (S : RunSem) (stk : Nat)
    (_hstk : decPkNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDecryptPrekeyName)
      ((RunProofs.cliDecryptPrekeySpecState (dpSlotPollKState A img B S) stk).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec A img S stk) := by
  refine subroutine_ok_of_outcome_map (fun x => ⟨x.ret, x⟩) hw fun x R s0 hpre => ?_
  have hpre1 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = x.msgA ∧ s0.readReg64 .x1 = x.peerA ∧ s0.readReg64 .x2 = x.meA ∧
        s0.readReg64 .x3 = x.stores + 240#64 ∧ s0.readReg64 .x4 = sessVt img ∧
        s0.readReg64 .x5 = x.stores ∧ s0.readReg64 .x6 = idVt img ∧
        s0.readReg64 .x7 = x.stores + 200#64 ∧
        s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        S.decPkOk x.F x.peer.val x.me.val x.msg ∧ stk ≤ s0.sp.toNat⌝ ∗
      (slotFrame A img x.toSlotCtx ∗ preKeyMsgAt A x.msgG x.msgA x.msg ∗
        (s0.sp ↦₆₄ oneTimeVt img) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
        ((s0.sp + 16#64) ↦₆₄ signedVt img) ∗ ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
        ((s0.sp + 32#64) ↦₆₄ kyberVt img) ∗ memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R)) := by
    simpa only [decPkSlotSpec, Spec.inImage, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre1; obtain ⟨hinv, hpre2⟩ := hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le⟩, hspatial⟩ := hpre2
  refine ⟨?_, ?_⟩
  · have htake : ((dpSlotPollKState A img B S).args x).take 8 =
        [s0.readReg64 .x0, s0.readReg64 .x1, s0.readReg64 .x2, s0.readReg64 .x3,
         s0.readReg64 .x4, s0.readReg64 .x5, s0.readReg64 .x6, s0.readReg64 .x7] := by
      simp only [dpSlotPollKState, dpSlotArgs, List.take, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7]
    have hinv_sp : s0.mem ⊨ (dpSlotPollKState A img B S).inv x s0.fs s0.trace ∗
          dpWordsAt s0.sp (((dpSlotPollKState A img B S).args x).drop 8) ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R := by
      unfold dpSlotPollKState
      rw [dpSlotStack5_eq, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF0, hfOk, hdOk⟩,
        by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hspatial⟩
    unfold Spec.inImage; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hinv, ?_⟩
    unfold RunProofs.cliDecryptPrekeySpecState; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, rfl, htake, hsp_le⟩,
      by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hinv_sp⟩
  · intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
    · exact Or.inl ⟨hret, hcc,
        Satisfies.mono (sepConj_mono_left (dpSlotState_post_entails A img B S stk x s0 sf)) hpost⟩
    · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
      have hp' : sf.mem ⊨ ⌜s0.trace <+: sf.trace ∧ (allocFailedIn s0 sf ∨
              S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none)⌝ ∗
          (anyHeap ∗ R) := by
        simpa only [Spec.inImage, RunProofs.cliDecryptPrekeySpecState, dpSlotPollKState,
          sepConj_assoc] using hp
      rw [satisfies_pure_sepConj] at hp'; obtain ⟨⟨_, hp_or⟩, hany⟩ := hp'
      have hp_goal : sf.mem ⊨ ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none ∨
            allocFailedIn s0 sf⌝ ∗ (anyHeap ∗ R) := by
        rw [satisfies_pure_sepConj]; exact ⟨hp_or.symm, hany⟩
      simpa only [decPkSlotSpec, Spec.inImage, sepConj_assoc] using hp_goal
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem decPk_slot_ok_state_ext (A : RustAlloc) (ext : String → Option (State → State))
    (img : Obj.Image) (B : RunBudgets) (S : RunSem) (stk : Nat)
    (hstk : decPkNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDecryptPrekeyName)
      ((RunProofs.cliDecryptPrekeySpecState (dpSlotPollKState A img B S) stk).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec A img S stk) :=
  dpSlot_ok_state_inImage B S stk hstk hstk64 hw

theorem decPk_slotOk_state_ext (A : RustAlloc) (ext : String → Option (State → State))
    (img : Obj.Image) (B : RunBudgets) (S : RunSem) (needs : RunNeeds)
    (hneed : needs.decryptPrekey = decPkNeed B)
    (hw : ∀ stk, decPkNeed B ≤ stk → stk ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr cliDecryptPrekeyName)
        ((RunProofs.cliDecryptPrekeySpecState (dpSlotPollKState A img B S) stk).inImage img)) :
    (slotsOf A img S needs).decryptPrekey.Ok img ext wrapDecryptPrekeyName :=
  fun stk h1 h2 => decPk_slot_ok_state_ext A ext img B S stk (hneed ▸ h1) h2 (hw stk (hneed ▸ h1) h2)

/-- Adapts `RunProofs.cliDecryptPrekeySpecState (K₀_state img B S)` on `cliDecryptPrekeyName` to
`decPkSlotSpec E2E.HooksE.A0 img S stk` on `wrapDecryptPrekeyName`. -/
theorem decPk_slot_ok_state (W : CliHooks) (img : Obj.Image) (B : RunBudgets) (S : RunSem) (stk : Nat)
    (hstk : decPkNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliDecryptPrekeyName)
      ((RunProofs.cliDecryptPrekeySpecState (K₀_state img B S) stk).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapDecryptPrekeyName)
      (decPkSlotSpec E2E.HooksE.A0 img S stk) :=
  decPk_slot_ok_state_ext E2E.HooksE.A0 (cliExterns W) img B S stk hstk hstk64 hw

theorem decPk_slotOk_state (W : CliHooks) (img : Obj.Image)
    (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (hneed : needs.decryptPrekey = decPkNeed B)
    (hw : ∀ stk, decPkNeed B ≤ stk → stk ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
        ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliDecryptPrekeyName)
        ((RunProofs.cliDecryptPrekeySpecState (K₀_state img B S) stk).inImage img)) :
    (slotsOf E2E.HooksE.A0 img S needs).decryptPrekey.Ok img (cliExterns W) wrapDecryptPrekeyName :=
  decPk_slotOk_state_ext E2E.HooksE.A0 (cliExterns W) img B S needs hneed hw

end CryptoVerification.SignalSession.Cli.RunCompose
