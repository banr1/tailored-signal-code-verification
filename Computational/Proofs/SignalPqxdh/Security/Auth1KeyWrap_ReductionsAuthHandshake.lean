/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key split-key hash collision reduction

One-key (`pqxdhAuthImpl1KeyG`) counterpart `shcrReductionAuthAt1Key` of `shcrReductionAuthAt`
from `ReductionsAuthHandshake`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open FgGapDh

def shcrReductionAuthAt1Key (S : Setup) (b : QueryBudget) (idx : ℕ)
    (A : AuthAdversary S) : KemShCrAdv where
  State := AuthShCrFinishState S
  choosePk := choosePkAuthPrimAt1Key S b (idx / S.N_send_tot) (idx % S.N_send_tot) A
  findCollision := findCollisionAuthPrim1Key S b
  q_prim := primQueryBudget S b

end SignalPqxdh.Security
