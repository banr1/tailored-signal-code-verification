/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# Session Parameters Parameterized by SPQR Model

**Checked by Lean.** Generalizes `spqrOffSessionParams` (`SchemeModel.lean`) from `spqrOffB` to an
arbitrary SPQR model `S : Spqr Bytes PQC`. See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CryptoVerification.E2E.V1

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.LibsignalTripleRatchetRepr

/-- `spqrOffSessionParams C` (`Specifications/LibsignalE2E/SchemeModel.lean`) with the SPQR model `S` in place
of `spqrOffB`. Only the `spqr` field changes. Instantiating `S` with the V1 SPQR model
`spqrV1SessionUniformCoins C.F K` (`LibsignalSpqrV1/Init.lean`) gives the SPQR-enabled parameters. -/
def sessionParamsForSpqr {PQC : Type} (C : Crypto) (S : Spqr Bytes PQC) : Params Bytes PQC :=
  ⟨C, protoSignalCodec, S, partyIdentityKey .A, partyIdentityKey .B, serializedPartyAddresses uuidTryParse .A .B,
    serializedPartyAddresses uuidTryParse .B .A⟩

end CryptoVerification.E2E.V1
