/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs

/-!
# Empty-`previous_sessions` Bridge Lemmas

Re-exports `ResponderClosure.Over.HeapDefs` and establishes the `ps = []` unfolding and
`sessionRecordAt = sessionRecordPrevAt ... []` bridge lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr

/-- `prevVecAt` on `[]` coincides definitionally with the empty `Vec` header/buffer in
`sessionRecordAt`. -/
theorem prevVecAt_nil_eq (A : RustAlloc) (r cap ptr : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) r cap ptr [] = prevVecAt A r cap ptr [] :=
  rfl

/-- `prevVecAt` on `[]` with `cap = 0#64` unfolds to `HdrP r 0#64 ptr 0#64 ∗ ⌜ptr ≠ 0#64⌝`. -/
theorem prevVecAt_zero_nil_eq (A : RustAlloc) (r ptr : BitVec 64) :
    prevVecAt A r 0#64 ptr [] = HdrP r 0#64 ptr 0#64 ∗ ⌜ptr ≠ 0#64⌝ := by
  unfold prevVecAt vecAt vecBuf
  simp only [List.length_nil, Nat.zero_le, BitVec.toNat_zero, Nat.zero_mul,
    show (0 : Nat) < 2 ^ 63 by decide, true_and, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]

/-- `prevVecAt` on `[]` with nonzero `cap` unfolds into header, live token, and spare `memRegion`. -/
theorem prevVecAt_ne_zero_nil_eq (A : RustAlloc) (r cap ptr : BitVec 64) (hcap : cap ≠ 0#64) :
    prevVecAt A r cap ptr [] =
      HdrP r cap ptr 0#64 ∗
        ⌜cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (A.live ptr (cap.toNat * 24) 8 ∗ memRegion ptr (cap.toNat * 24)) := by
  unfold prevVecAt vecAt vecBuf
  simp only [List.length_nil, Nat.zero_le, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, true_and, hcap, ↓reduceIte, arrayAt, emp_sepConj]

/-- For `ps = []`, `sessionRecordPrevAt` is definitionally equal to `sessionRecordAt`. -/
theorem sessionRecordAt_eq_prevAt (A : RustAlloc) (r : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A r g rec = sessionRecordPrevAt A r g [] rec := by
  unfold sessionRecordAt sessionRecordPrevAt recCurAt
  cases g.cur <;> cases rec.currentSession <;> rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
