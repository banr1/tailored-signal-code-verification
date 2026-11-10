/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytes
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeW

/-!
# Bytes Arms Under `AllocContractsX`

Discharges `BytesMerge6OkExtW` via `bytes_merge_6_ok_ext_w_of_alloc` to establish
`OverDecArmStmtTR OverDecBytesField` for tags 2, 3, 4, 13, and 15.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.E2E.Record (A0)

/-- Allocator-polymorphic `OverDecArmStmtTRExt` for all five bytes arms (tags 2, 3, 4, 13, 15). -/
theorem overDecArm_bytes_okTR_ext {A : RustAlloc} : OverDecArmStmtTRExt A OverDecBytesField := by
  intro img ext hL hAC s0 s g v fl rest hP hok _hfr hsuf hlen hregs hx0 _hx22
  exact overDecArm_bytes_of_bm6w_ext img ext
    (bytes_merge_6_ok_ext_w_of_alloc hL hAC)
    s0 s g v fl rest hP hok hsuf hlen hregs hx0

theorem overDecArm_bytes_okTR : OverDecArmStmtTR OverDecBytesField :=
  overDecArm_bytes_okTR_ext

alias overDecArm_bytes_cli_okTR_ext := overDecArm_bytes_okTR_ext
alias overDecArm_bytes_cli_okTR := overDecArm_bytes_okTR

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
