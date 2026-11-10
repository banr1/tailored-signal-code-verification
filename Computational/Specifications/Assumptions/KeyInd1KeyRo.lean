/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KeyInd1KeyReal

/-!
# Key indistinguishability with one-key identities and a random-oracle key derivation

**Trusted: definitions used by the statement.** Lemma 1 (`PqxdhCorrectAndSecureδ`,
`Security/HeadlineDelta.lean`) bounds `KeyInd1KeyRoAdvantage` on `pqxdhKeyIndImpl1KeyRo`, and
clause 2 of the PQXDH CLI statements (e.g. `CliPqxdhElfSecure`) uses `KeyIndRoGap`. Read with
`Computational/Specifications/Pqxdh/Game.lean` (`pqxdhKeyIndImpl`), `Assumptions.lean`
(`GapDhWithSign`, `KemShCr`, `GapSigEufCma`), and `KeyInd1KeyReal.lean`. See
`Computational/docs/TRUSTED_BASE.md` and `Computational/docs/DEVIATIONS.md` (DEV-CLI16).

The CLI statements relate the real one-key handshake game (`KeyInd1KeyRealAdvantage`) to the
one-key random-oracle game (`KeyInd1KeyRoAdvantage`, replacing `P.hkdfDerive96` with `HkdfRO`,
DEV-PQ14) via `KeyIndRoGap`, while Lemma 1 bounds `KeyInd1KeyRoAdvantage` under `GapSigEufCma`,
`KemShCr`, and `GapDhWithSign`. Against `pqxdhKeyIndImpl1KeyReal`, `pqxdhKeyIndImpl1KeyRo`
differs only in using `evalHkdfOrRo true` (`HkdfRO`) rather than `evalHkdfOrRo false`
(`P.hkdfDerive96`), as checked in `Computational/Tests/Guards/KeyInd1KeyRoGuard.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-- Key-indistinguishability oracle with single-scalar identities and random-oracle key derivation.
Delegates `.initPrin u` to `pqxdhKeyIndImpl1KeyReal` and all other queries to
`pqxdhKeyIndImpl true S P`, which uses one shared lazy `HkdfRO` cache (`evalHkdfOrRo true`) across
`.roQuery`, `initiate*`, and `accept*` and disables `.revealDhSecrets`. -/
def pqxdhKeyIndImpl1KeyRo (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp) := fun q =>
  match q with
  | .initPrin u => pqxdhKeyIndImpl1KeyReal S P (.initPrin u)
  | q => pqxdhKeyIndImpl true S P q

/-- Distinguishing advantage of `A` in `pqxdhKeyInd1KeyExpForHandshake` against
`pqxdhKeyIndImpl1KeyRo`. -/
noncomputable def KeyInd1KeyRoAdvantage (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ℝ≥0∞ :=
  𝒟[pqxdhKeyInd1KeyExpForHandshake S P (pqxdhKeyIndImpl1KeyRo S P) A].boolBias

/-- Random-oracle gap (`HkdfRO`, DEV-PQ14) on the one-key handshake game for `A`: bounds
`KeyInd1KeyRealAdvantage` by `KeyInd1KeyRoAdvantage + ε`. Takes `ε = 0` in the random-oracle model
of FG24 and BJKS24 (`pqxdhKeyIndAdvantageBoundActiveδ`); remains an unproved hypothesis in the
standard model (DEV-CLI16). -/
def KeyIndRoGap (S : Setup) (P : Primitives) (A : KeyIndAdversary S) (ε : ℝ≥0∞) : Prop :=
  KeyInd1KeyRealAdvantage S P A ≤ KeyInd1KeyRoAdvantage S P A + ε

end SignalPqxdh
