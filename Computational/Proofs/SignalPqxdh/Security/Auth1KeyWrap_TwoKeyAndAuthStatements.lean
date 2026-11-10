/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key `Auth` game experiment

One-key (`pqxdhAuthImpl1KeyG`) counterparts `pqxdhAuthExpCore1Key` and `pqxdhAuthExp1Key` of the
Game 2 authentication experiment in `TwoKeyAndAuthStatements`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-- Core one-key Game 2 (`Auth`/`FirstMsg`) experiment over `pqxdhAuthImpl1KeyG` (cf. DEV-PQ13). -/
noncomputable def pqxdhAuthExpCore1Key (useRo checkAuth : Bool) (S : Setup)
    (P : Primitives) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthImpl1KeyG useRo checkAuth S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allChallengedClean := finalSt.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P useRo finalSt.principals s)
  if checkAuth && finalSt.hasWonAuth then
    return true
  else if !allChallengedClean then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

/-- One-key Game 2 experiment (`useRo = true`, `checkAuth = true`) for first-message privacy and authentication. -/
noncomputable def pqxdhAuthExp1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp Bool :=
  pqxdhAuthExpCore1Key true true S P A

end SignalPqxdh

namespace SignalPqxdh.Costed

open _root_.ReductionDsl OracleSpec OracleComp

end SignalPqxdh.Costed

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.ReductionDsl (Ty CostedReduction TwoStageCostedReduction Mid)
open SignalPqxdh.Costed

end SignalPqxdh.Security

namespace SignalPqxdh

end SignalPqxdh

namespace SignalPqxdh.Costed

end SignalPqxdh.Costed

namespace SignalPqxdh.Security.Costed

end SignalPqxdh.Security.Costed
