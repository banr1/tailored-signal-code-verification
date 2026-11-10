/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSpkModel
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel

/-!
# Session parameters at arbitrary identity keys and the leaked-pre-key session scheme

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use
`idsOf`, `paramsIdsWithSpqr` and `sessionSchemeFixedSpk`. The statements `SessionSecureIds`,
`SessionSecureUIds`, `SessionSecureSpkIds` and `SessionSecureSpkIdsWithSpqr`, and `paramsIds`, are
in `Computational/Proofs/SpecLemmas/Session/StatementIdsModel.lean`, checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Defines session parameters for caller-chosen identity keys `idA`, `idB` (which enter the wire MACs)
and the leaked-pre-key session scheme `sessionSchemeFixedSpk`, where Bob's signed-pre-key scalar `s`
is fixed externally while the remaining initial keys are sampled via `SampledSessionKey`.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession

/-! ## Session parameters -/

/-- Session parameters for SPQR instance `spqr` and party identity keys `idA`, `idB`, with
`protoSignalCodec` and serialized UUID party addresses (`uuidTryParse`). -/
def paramsIdsWithSpqr (C : Crypto) {PQC : Type} (spqr : Spqr Bytes PQC)
    (idA idB : IdentityKey) : Params Bytes PQC :=
  ⟨C, protoSignalCodec, spqr, idA, idB,
    serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B,
    serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .B .A⟩

/-- Assigns identity key `idA` to `.A` and `idB` to `.B`. -/
def idsOf (idA idB : IdentityKey) : Party → IdentityKey
  | .A => idA
  | .B => idB

/-! ## Leaked-pre-key session scheme -/

/-- Single-session `SMSchemeR` with Bob's signed-pre-key coins fixed to `s`, keyed by
`SampledSessionKey` via `initKeysOfSampled s` with plaintexts fitted to `ℓ` bytes. -/
def sessionSchemeFixedSpk {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ) (s : BitVec 256) :
    SMSchemeR SampledSessionKey (GhostState PQ) (Plain ℓ) PQC (BitVec 256) Bytes where
  initA k := P.initA (initKeysOfSampled s k)
  initB k := P.initB (initKeysOfSampled s k)
  send g m r := P.send g m.toList r
  receive g c rc := (P.receive g c rc).map fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)

end CryptoVerification.E2E
