/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields

/-!
# Record Representation Leaf (`deserReprG_ok`) for General `SessionRecord::deserialize`

Proves `deserReprG_ok`, converting `deserOutRecordG` at `out` into `sessionRecordAt` holding `r`
with `CanonRecord`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserReprG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonCur CanonSession)

private theorem vecAt_prev_zero_eq (out : BitVec 64) :
    vecAt A0 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    SeedLengthFacts.pure_true_sepConj hpure]

theorem deserReprG_ok_of (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r) (out : BitVec 64)
    (hAfter : ∀ (s : Session (List (BitVec 8))), r.currentSession = some s →
      ssgAfter r (recFields r).length = ssgOf s)
    (hRepr : ∀ (s : Session (List (BitVec 8))), r.currentSession = some s → ∀ (ss : BitVec 64),
      prostSSGAt A0 ss (ssgOf s) ⊢ ∃∗ G : SessionGhost, ⌜CanonSession G s⌝ ∗ sessionStateReprAt A0 ss G s) :
    deserOutRecordG out r ⊢
      ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r := by
  obtain ⟨s, hs, _⟩ := hr.2
  have hdef :
      deserOutRecordG out r =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          prostSSGAt A0 (out + 0x18#64) (ssgOf s) := by
    unfold deserOutRecordG
    rw [hAfter s hs]
    ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right (hRepr s hs (out + 0x18#64))) ?_
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
    rw [vecAt_prev_zero_eq]
    exact Entails.refl _

theorem deserReprG_ok (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r) (out : BitVec 64)
    (hRepr : ∀ (s : Session (List (BitVec 8))), r.currentSession = some s → ∀ (ss : BitVec 64),
      prostSSGAt A0 ss (ssgOf s) ⊢ ∃∗ G : SessionGhost, ⌜CanonSession G s⌝ ∗ sessionStateReprAt A0 ss G s) :
    deserOutRecordG out r ⊢
      ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r :=
  deserReprG_ok_of r hr out (ssgAfter_recFields r hr) hRepr

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserReprG

