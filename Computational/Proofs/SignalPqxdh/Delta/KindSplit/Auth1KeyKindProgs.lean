/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK -- proof-setup: allow-public-import
public import Computational.Specifications.Pqxdh.Bound
public import Computational.Specifications.Pqxdh.Security.Headline

/-!
# Per-Query-Kind Costed Reduction Family for One-Key PQXDH `Auth`

Packages the seven shadow-indexed per-query-kind `pqAtomicOps` reductions from `AuthGapDhK` and
`AuthCoreKArms` into `pqxdhAuth1KeyKindCostedSims : Auth1KeyCostedReductionFamily S`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs

open _root_.SignalPqxdh (Setup QueryBudget)
open _root_.SignalPqxdh.Security (Auth1KeyCostedReductionFamily)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (shcrAuth1KeyKindProg prfCk1KeyKindProg prfMsgKeys1KeyKindProg
   aeadCpa1KeyKindProg prfHmac1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (a1s2KindProg a1g2KindProg)

/-- Shadow-indexed per-query-kind `Auth1KeyCostedReductionFamily` over `pqAtomicOps`. -/
@[expose] def pqxdhAuth1KeyKindCostedSims (S : Setup) : Auth1KeyCostedReductionFamily S where
  sig  b := a1s2KindProg S b
  shcr b := shcrAuth1KeyKindProg S b
  gdh  b := a1g2KindProg S b
  ck   b := prfCk1KeyKindProg S b
  mk   b := prfMsgKeys1KeyKindProg S b
  cpa  b := aeadCpa1KeyKindProg S b
  int  b := prfHmac1KeyKindProg S b

theorem pqxdhAuth1KeyKindCostedSims_sig (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).sig b = a1s2KindProg S b := rfl

theorem pqxdhAuth1KeyKindCostedSims_shcr (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).shcr b = shcrAuth1KeyKindProg S b := rfl

theorem pqxdhAuth1KeyKindCostedSims_gdh (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).gdh b = a1g2KindProg S b := rfl

theorem pqxdhAuth1KeyKindCostedSims_ck (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).ck b = prfCk1KeyKindProg S b := rfl

theorem pqxdhAuth1KeyKindCostedSims_mk (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).mk b = prfMsgKeys1KeyKindProg S b := rfl

theorem pqxdhAuth1KeyKindCostedSims_cpa (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).cpa b = aeadCpa1KeyKindProg S b := rfl

theorem pqxdhAuth1KeyKindCostedSims_int (S : Setup) (b : QueryBudget) :
    (pqxdhAuth1KeyKindCostedSims S).int b = prfHmac1KeyKindProg S b := rfl

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs
