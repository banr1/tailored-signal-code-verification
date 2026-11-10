/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHmac
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.Headline

/-!
# Shallow Concrete Reductions for PQXDH

Bundles the shallow concrete reductions used in the game-hop proofs into `pqxdhKeyIndSimulators`
(`KeyInd2KeyReductionFamily S`) and `pqxdhAuthSimulators` (`AuthReductionFamily S`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh

/-- The shallow two-key key-indistinguishability reductions. -/
def pqxdhKeyIndSimulators (S : Setup) : KeyInd2KeyReductionFamily S where
  sig  := sigReductionKeyInd S
  shcr := shcrReductionKeyInd S
  gdh  := fgKeyIndGapDhAdv4 S

/-- The shallow authentication reductions. -/
def pqxdhAuthSimulators (S : Setup) : AuthReductionFamily S where
  sig  := sigReductionAuth S
  shcr := shcrReductionAuth S
  gdh  := fgAuthGapDhAdv4 S
  ck   := prfCkReductionAuthFixed S
  mk   := prfMsgKeysReductionAuthFixed S
  cpa  := aeadCpaReductionAuthFixed S
  int  := prfHmacReductionAuth S

/-- Shallow-simulator two-key key-indistinguishability statement (`pqxdhKeyIndSimulators S`). -/
def PqxdhKeyIndConcreteStatement (S : Setup) : Prop :=
  KeyInd2KeyReductionQueryBounds S (pqxdhKeyIndSimulators S) ∧
  PqxdhKeyIndStatementWith S (pqxdhKeyIndSimulators S)

/-- Shallow-simulator authentication statement (`pqxdhAuthSimulators S`). -/
def PqxdhAuthConcreteStatement (S : Setup) : Prop :=
  AuthReductionQueryBounds S (pqxdhAuthSimulators S) ∧
  PqxdhAuthStatementWith S (pqxdhAuthSimulators S)

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (
  sigReductionKeyInd
  shcrReductionKeyInd
  fgKeyIndGapDhAdv4
  sigReductionAuth
  shcrReductionAuth
  fgAuthGapDhAdv4
  prfCkReductionAuthFixed
  prfMsgKeysReductionAuthFixed
  aeadCpaReductionAuthFixed
  aeadMuIntReductionAuth
  prfHmacOfMu
  prfHmacReductionAuth
  pqxdhKeyIndSimulators
  pqxdhAuthSimulators
  PqxdhKeyIndConcreteStatement
  PqxdhAuthConcreteStatement
)

end SignalPqxdh

