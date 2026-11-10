/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M3d
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5D
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC5
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
public import Computational.Proofs.SignalPqxdh.Security.Reductions
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c5
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmac
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect

/-!
# PQXDH authentication sub-hops 4–5 bundle assembly

Packages the multi-key AEAD integrity reduction `aeadMuIntReductionAuth` and the
`G3.8 → G5` hop bound into `authSubHops4to5Bundle`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp
open scoped ENNReal

namespace Proofs.SignalPqxdh.Security

/-- Assembles `AuthSubHops4to5Bundle S` from `aeadMuIntReductionAuth` and `auth_hop_G3_8_split_g5_boolBias_le_mu`. -/
def authSubHops4to5Bundle (S : Setup) : AuthSubHops4to5Bundle S :=
  authSubHops4to5Bundle_of_int S
    (aeadMuIntReductionAuth S)
    (aeadMuIntReductionAuth_queries S)
    (aeadMuIntReductionAuth_enc_queries S)
    (aeadMuIntReductionAuth_prim_queries S)
    (auth_hop_G3_8_split_g5_boolBias_le_mu S)

end Proofs.SignalPqxdh.Security

namespace SignalPqxdh.Security

export _root_.Proofs.SignalPqxdh.Security (authSubHops4to5Bundle)

end SignalPqxdh.Security

