/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacDsl
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacProofs

/-!
# Cost and Query Wiring for `prfHmacDslAdv`

Instantiates the cost and query bounds for `prfHmacRedProg` at `K = b.q_total`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf SignalPqxdh.Security.ReductionDsl.AuthAead

abbrev prfHmacDslProg (S : Setup) (b : QueryBudget) :=
  prfHmacRedProg S b.q_total

/-- Step-cost bound for `prfHmacDslProg`. -/
theorem prfHmacDslProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (prfHmacDslProg S b).totalCost b.q_total ≤ stepCostBudget S b :=
  prfHmacRedProg_totalCost_security_le S b

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
