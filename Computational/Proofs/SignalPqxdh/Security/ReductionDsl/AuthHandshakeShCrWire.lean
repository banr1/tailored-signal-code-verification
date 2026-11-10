/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs

/-!
# Cost Bounds for the `ReductionDsl` `Auth` `KemShCr` Adversary

Specializes the `shcrReductionAuthProg` step-cost bounds to `shcrAuthDslProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl

abbrev shcrAuthDslProg (S : Setup) (b : QueryBudget) :=
  shcrReductionAuthProg S b.q_total b.q_total

theorem shcrAuthDslProg_totalCost_le_sec (S : Setup) (b : QueryBudget) :
    (shcrAuthDslProg S b).totalCost b.q_total ≤ SignalPqxdh.Security.stepCostBudget S b :=
  shcrReductionAuthProg_totalCost_le_sec S b

theorem shcrAuthDslProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (shcrAuthDslProg S b).totalCost b.q_total ≤ stepCostBudget S b :=
  shcrReductionAuthProg_totalCost_le S b

end SignalPqxdh.Security.ReductionDsl.AuthHs
