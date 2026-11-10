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
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c5
public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmac
public import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
public import Computational.Proofs.SignalPqxdh.Security.AuthAssembly
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHop
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopA
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthPrfHmac
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthPrfHmacHA2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M3a
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M3d
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `Auth` `G3.8 → G5` Bundle

Assembles `AuthSubHops4to5Bundle1Key` over `pqxdhAuthImpl1KeyG` from the multi-key AEAD ciphertext
integrity reduction `aeadMuIntReductionAuth1Key` and `auth_hop_G3_8_split_g5_boolBias_le_mu1Key`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp
open scoped ENNReal

namespace Proofs.SignalPqxdh.Security

def authSubHops4to5Bundle1Key (S : Setup) : AuthSubHops4to5Bundle1Key S :=
  authSubHops4to5Bundle_of_int1Key S
    (aeadMuIntReductionAuth1Key S)
    (aeadMuIntReductionAuth_queries1Key S)
    (aeadMuIntReductionAuth_enc_queries1Key S)
    (aeadMuIntReductionAuth_prim_queries1Key S)
    (auth_hop_G3_8_split_g5_boolBias_le_mu1Key S)

end Proofs.SignalPqxdh.Security

namespace SignalPqxdh.Security

end SignalPqxdh.Security
