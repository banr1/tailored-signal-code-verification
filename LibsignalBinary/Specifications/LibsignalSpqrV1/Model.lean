/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble

/-!
# SPQR V1: assembled models (`spqrV1`, `spqrV1Recv`)

**Trusted in part.** The theorems of `Computational/Theorems/` use `spqrV1`; `spqrV1Recv` is checked
by Lean (see `Computational/docs/TRUSTED_BASE.md`).

Packages the concrete SPQR V1 models over `F : ShaCompress` and `K : MlKem` (`Assemble.lean`):
`spqrV1 F K : SpqrModel` for the session model and `spqrV1Recv F K : SpqrRecvModel` returning the
exact `Option Bytes` message key (DEV-SPQR2).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchet

/-- Concrete SPQR V1 `SpqrModel` (`Top.toSpqrModel` instantiated with `spqrDeps F K`). -/
def spqrV1 (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) : SpqrModel :=
  spqrV1Assembled F K

/-- Concrete SPQR V1 `SpqrRecvModel` returning exact `Option Bytes` message keys (DEV-SPQR2). -/
def spqrV1Recv (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) : SpqrRecvModel :=
  spqrV1RecvAssembled F K

theorem spqrV1_eq (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) :
    spqrV1 F K = toSpqrModel (spqrDeps F K) (spqrHkdfWith F) := rfl

theorem spqrV1Recv_eq (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) :
    spqrV1Recv F K = toSpqrRecvModel (spqrDeps F K) (spqrHkdfWith F) := rfl

end CryptoVerification.LibsignalSpqrV1
