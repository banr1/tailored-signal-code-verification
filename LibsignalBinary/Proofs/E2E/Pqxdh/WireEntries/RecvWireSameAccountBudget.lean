/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount

/-!
# `VmPreserved`-Augmented `<IdentityKey>::is_same_account` Specifications

Augments `isSameAccountDistinctRawSpec` and `isSameAccountDistinctSpec` (Block `17`) with
`VmPreserved` so `RustCliAllocBudget M` callers can transport `A.pool lim st` across the
zero-allocation `<IdentityKey>::is_same_account` call.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget

open Arm64 ProofLib
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.E2E.Pqxdh.WireEntries
  (IsSameAccountDistinctRawGhost IsSameAccountDistinctGhost)

def isSameAccountDistinctRawSpec (parse : UuidParser) : Spec IsSameAccountDistinctRawGhost :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctRawSpec parse)

/-- `VmPreserved`-augmented `isSameAccountDistinctSpec` (callers with `A : RustCliAllocBudget M`
    instantiate `A` at `A.repAlloc`). -/
def isSameAccountDistinctSpec (A : RustAlloc) (parse : UuidParser) :
    Spec IsSameAccountDistinctGhost :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec A parse)

end LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget
