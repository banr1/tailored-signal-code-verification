/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual
public import ProofLib.SepLogic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core

/-!
# Stage P4 Callee Contracts and Prekey-ID Tuple Packing Helpers

Defines isolated Stage P4 store-persistence callee contracts (`save_identity`,
`mark_kyber_pre_key_used`, `remove_pre_key`, `store_session`, and `SessionRecord` drop) together
with sub-word merge/split lemmas for `(opkId?, kyberPreKeyId?, signedPreKeyId)`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Isolated Provisional Callee Contracts for Stage P4 -/

/-- Isolated Stage P4 callee addresses for `message_decrypt_prekey::{closure#0}`:
- `saveIdentityShimAddr`, `saveIdentityPollAddr`, `saveIdentityDropAddr`:
  vtable-dispatched `IdentityKeyStore::save_identity` shim, future poll, and future drop.
- `kyberMarkUsedShimAddr`, `kyberMarkUsedPollAddr`, `kyberMarkUsedDropAddr`:
  vtable-dispatched `KyberPreKeyStore::mark_kyber_pre_key_used` shim, future poll, and future drop.
- `removePreKeyShimAddr`, `removePreKeyPollAddr`, `removePreKeyDropAddr`:
  vtable-dispatched `PreKeyStore::remove_pre_key` shim, future poll, and future drop.
- `storeSessionShimAddr`, `storeSessionPollAddr`, `storeSessionDropAddr`:
  vtable-dispatched `SessionStore::store_session` shim, future poll, and future drop.
- `sessionStateDropInPlaceAddr`: `b + 0x70dc0#64` (`drop_in_place::<SessionState>`). -/
structure StageP4CalleeContracts (b : BitVec 64) where
  saveIdentityShimAddr : BitVec 64
  saveIdentityPollAddr : BitVec 64
  saveIdentityDropAddr : BitVec 64
  kyberMarkUsedShimAddr : BitVec 64
  kyberMarkUsedPollAddr : BitVec 64
  kyberMarkUsedDropAddr : BitVec 64
  removePreKeyShimAddr : BitVec 64
  removePreKeyPollAddr : BitVec 64
  removePreKeyDropAddr : BitVec 64
  storeSessionShimAddr : BitVec 64
  storeSessionPollAddr : BitVec 64
  storeSessionDropAddr : BitVec 64
  sessionStateDropInPlaceAddr : BitVec 64 := b + 0x70dc0#64

/-! ## 2. Sub-Word Merge/Split Helpers for `(opkId?, kyberPreKeyId?, signedPreKeyId)` -/

theorem pointsTo32_pair_coro_298 (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    (((coroPtr + 0x298#64) ↦₃₂ lo) ∗ ((coroPtr + 0x29c#64) ↦₃₂ hi)) =
      ((coroPtr + 0x298#64) ↦₆₄ (hi ++ lo)) := by
  have h : coroPtr + 0x29c#64 = (coroPtr + 0x298#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

theorem pointsTo32_pair_coro_2ac (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x2ac#64) ↦₆₄ (hi ++ lo)) =
      (((coroPtr + 0x2ac#64) ↦₃₂ lo) ∗ ((coroPtr + 0x2b0#64) ↦₃₂ hi)) := by
  have h : coroPtr + 0x2b0#64 = (coroPtr + 0x2ac#64) + 4#64 := by bv_omega
  rw [h, ← pointsTo32_pair]

theorem pointsTo32_pair_coro_2b4 (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x2b4#64) ↦₆₄ (hi ++ lo)) =
      (((coroPtr + 0x2b4#64) ↦₃₂ lo) ∗ ((coroPtr + 0x2b8#64) ↦₃₂ hi)) := by
  have h : coroPtr + 0x2b8#64 = (coroPtr + 0x2b4#64) + 4#64 := by bv_omega
  rw [h, ← pointsTo32_pair]

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_0_32_append_32 (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 0 32 = lo :=
  BitVec.extractLsb'_append_eq_right

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_32_32_append_32 (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 32 32 = hi :=
  BitVec.extractLsb'_append_eq_left

@[local simp, local arm64_norm, local wp_norm]
theorem setWidth_32_append_32 (hi lo : BitVec 32) :
    (hi ++ lo).setWidth 32 = lo := by
  simp only [BitVec.setWidth_append, Nat.le_refl, ↓reduceDIte, BitVec.setWidth_eq]

@[local simp, local arm64_norm, local wp_norm]
theorem append_1_32_getElem_zero (x : BitVec 32) : (x ++ 1#32)[0] = true := by
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append]
  rfl

end CryptoVerification.E2E.Pqxdh.ResponderClosure
