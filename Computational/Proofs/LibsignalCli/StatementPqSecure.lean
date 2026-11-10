/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPq
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.LibsignalCli.StatementPqElf

/-!
# CLI Security Statement on PQXDH Directories with SPQR

**Checked by Lean.** Defines `LibsignalCliPqSecure`, specializing `CliPqxdhSecurityFor`
(`Computational/Specifications/LibsignalCli/StatementPqElf.lean`) to arbitrary CLI implementations
`run` satisfying `CliSpecPqxdh run X W` with no excused aborts (`exc? := none`).

**DEV-CLI16 (formalization): the key-indistinguishability term is that of the real handshake.**
Clause 1 bounds `CliPqxdhAdvantage` using `KeyInd1KeyRealAdvantage` (one identity key for X25519
and XEdDSA, real HKDF) with no random oracle; Clause 2 reduces `KeyInd1KeyRealAdvantage` to the
proved one-key PQXDH bound `pqxdhKeyIndAdvantageBoundδ` under the explicit random-oracle gap
hypothesis `KeyIndRoGap` (see `Computational/docs/DEVIATIONS.md`).
-/

@[expose] public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-- Specializes `CliPqxdhSecurityFor` to every `run` satisfying `CliSpecPqxdh run X W` with no
excused aborts (`exc? := none`). -/
abbrev LibsignalCliPqSecure {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  CliPqxdhSecurityFor (Pt := Pt) S ℓ fun Bound =>
    ∀ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (_hCli : CliSpecPqxdh run X W),
      Bound run X W none

end CryptoVerification.E2E
