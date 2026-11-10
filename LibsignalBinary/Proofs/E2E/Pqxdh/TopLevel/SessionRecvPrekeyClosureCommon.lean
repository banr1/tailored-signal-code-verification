/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.TopLevel
open Arm64 ProofLib

theorem stackAt_sub_split (sp : BitVec 64) (n m : Nat) (h1 : m ≤ n) (h2 : n ≤ 2 ^ 64) :
    stackAt sp n =
      memRegion (sp - BitVec.ofNat 64 n) (n - m) ∗ stackAt sp m := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 n) (b' := sp - BitVec.ofNat 64 m)
    (N := n) (n := n - m) (k := m) (by omega)
    (by
      have h : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - m) + BitVec.ofNat 64 m := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel h1]
      rw [h]; bv_lin)
    (by omega)

end CryptoVerification.E2E.Pqxdh.TopLevel
