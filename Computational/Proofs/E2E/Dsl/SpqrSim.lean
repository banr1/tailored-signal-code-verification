/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.SpqrSimSend
public import Computational.Proofs.E2E.Dsl.SpqrSimRecv
public import Computational.Proofs.E2E.Dsl.DrSessionSimHooks

/-!
# SPQR V1 `ReductionDsl` Simulation

Re-exports `spqrSendComp` and `spqrRecvComp` with their cost, zero-query, and evaluation
theorems, and bundles them into `spqrDslHooks`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.SpqrSim

open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (SpqrDslHooks)

export SpqrSimSend (spqrSendComp spqrSendComp_cost spqrSendComp_queries spqrSendComp_eval)
export SpqrSimRecv (spqrRecvComp spqrRecvComp_cost spqrRecvComp_queries spqrRecvComp_eval)

/-- Concrete `SpqrDslHooks` bundle backed by `spqrSendComp` and `spqrRecvComp`. -/
def spqrDslHooks (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    SpqrDslHooks ℓ P C K decT encT where
  sendC := spqrSendComp
  sendC_cost := spqrSendComp_cost
  sendC_queries := spqrSendComp_queries
  sendC_eval := spqrSendComp_eval
  recvC := spqrRecvComp
  recvC_cost := spqrRecvComp_cost
  recvC_queries := spqrRecvComp_queries
  recvC_eval := spqrRecvComp_eval

end Computational.Proofs.E2E.Dsl.SpqrSim
