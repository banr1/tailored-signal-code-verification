/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Aesop.BuiltinRules
public import Arm64.Trusted.ISA.Semantics
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegMidBase
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv` Segment Helpers (`S5Spec`)

Framing and outcome-threading helpers around `spqr::recv` (`+0x5b8 → +0x5dc / +0x30c`).
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

namespace BS8

end BS8

/-- Attach a pure fact `p` to the normal-return arm of an S5 outcome (the `spqr::recv` post's no-panic
conjunct, threaded into `S6State` / `ErrTailState`). -/
theorem s5_out_add_np {prog : Program} {s : State} {N PanicOut : State → Prop} {p : Prop}
    (hp : p) (h : ∃ s', Steps prog s s' ∧ (N s' ∨ PanicOut s')) :
    ∃ s', Steps prog s s' ∧ ((N s' ∧ p) ∨ PanicOut s') := by
  obtain ⟨s', hs, hN | hP⟩ := h
  · exact ⟨s', hs, Or.inl ⟨hN, hp⟩⟩
  · exact ⟨s', hs, Or.inr hP⟩

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC
