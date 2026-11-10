/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyHeadline
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindBundle
public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyD
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCrEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfCk
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyAeadCpa
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac
public import Computational.Proofs.SignalPqxdh.Headline
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs

/-!
# One-Key PQXDH `Auth` Headline Theorems

Assembles unconditional one-key PQXDH authentication security (`pqxdh_auth1KeySecureδ`) and the
combined correctness, `KeyInd`, and `Auth` theorem (`pqxdhCorrectAndSecureWithAuthδ_holds`) from
`auth1KeyKindDslFamily` and the per-principal signature bound.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open _root_.ReductionDsl
open SignalPqxdh SignalPqxdh.Costed SignalPqxdh.Security Proofs.SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open SignalPqxdh.Security.ReductionDsl
open SignalPqxdh.Security.ReductionDsl.AuthHs
open SignalPqxdh.Security.ReductionDsl.AuthPrf
open SignalPqxdh.Security.ReductionDsl.AuthAead
open SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindBundle (auth1KeyKindDslFamily)

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

theorem auth1KeySigPerKStmt_holds (S : Setup) : Auth1KeySigPerKStmt S :=
  fun P hP b A k _ => authSig1KeyPerKBound_holds S P hP b A k

/-- Unconditional one-key PQXDH authentication security. -/
theorem pqxdh_auth1KeySecureδ (S : Setup) : PqxdhAuth1KeySecureδ S :=
  pqxdhAuth1KeySecureδ_of S (auth1KeyKindDslFamily S)
    (auth1KeySigHopStmt_of_perK S (auth1KeySigPerKStmt_holds S)) (auth1KeyGapDhAnyStmt_holds S)

/-- Unconditional PQXDH correctness, one-key `KeyInd` security, and one-key `Auth` security. -/
theorem pqxdhCorrectAndSecureWithAuthδ_holds : PqxdhCorrectAndSecureWithAuthδ :=
  pqxdhCorrectAndSecureWithAuthδ_of_perK' auth1KeyKindDslFamily auth1KeySigPerKStmt_holds

end Proofs.SignalPqxdh.Security.PqxdhDelta

#print axioms Proofs.SignalPqxdh.Security.PqxdhDelta.pqxdh_auth1KeySecureδ
#print axioms Proofs.SignalPqxdh.Security.PqxdhDelta.pqxdhCorrectAndSecureWithAuthδ_holds
