/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RustHeap.Alloc
public import Arm64
public import ProofLib.SepLogic.Stack

/-!
# Non-Vacuity Room Predicate for `RustAlloc` Hooks

Defines `AllocSucceedsWithRoom`, asserting that `__rust_alloc` and `__rust_realloc` hooks return
non-null whenever an unmapped aligned block of the requested size exists.
-/

@[expose] public section

namespace CryptoVerification.RustHeap
open Arm64 ProofLib

/-- The `alloc` / `realloc` hooks of `hooks` fail only when there is no room: from any running,
`sp`-aligned state that meets their precondition (with any frame `R`), if some non-null,
`align`-aligned block of the requested size is unmapped, they return a non-null `x0`.

"Never fails" cannot be required: a frame owning all mapped memory forces `x0 = 0`. Satisfiable
by mapping a fresh unmapped block (`Memory.mapFresh`). Used only to state non-vacuity
(`ConsumeMessageKeySpecSatisfiable`), never as a proof assumption. -/
def AllocSucceedsWithRoom (A : RustAlloc) (hooks : String → Option (State → State)) : Prop :=
  (∀ f, hooks "__rustc::__rust_alloc" = some f →
    ∀ size align R (s : State), s.status = .Running → s.spAligned = true →
      (s.mem ⊨ (rustAllocSpec A).pre (size, align) s ∗ R) →
      (∃ p : BitVec 64, p ≠ 0 ∧ p.toNat % align = 0 ∧ Unmapped s.mem p size) →
      (f s).readReg64 .x0 ≠ 0) ∧
  (∀ f, hooks "__rustc::__rust_realloc" = some f →
    ∀ p old align new bs R (s : State), s.status = .Running → s.spAligned = true →
      (s.mem ⊨ (rustReallocSpec A).pre (p, old, align, new, bs) s ∗ R) →
      (∃ q : BitVec 64, q ≠ 0 ∧ q.toNat % align = 0 ∧ Unmapped s.mem q new) →
      (f s).readReg64 .x0 ≠ 0)

end CryptoVerification.RustHeap
