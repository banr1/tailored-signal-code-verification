/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.PQXDH

/-!
# PQXDH Root-Key Helpers

Defines `kdfRk` and `createChain` for deriving root and chain keys from Diffie-Hellman outputs.
-/

@[expose] public section

namespace DY.Libsignal.PQXDH

variable [HasExecBytes]

open DY.Comparse
open Literal Concat DiffieHellman KdfExtract PQKem

/-- Derives a `(rootKey, chainKey)` pair from root key `rk` and DH output `dhOut` via HKDF with
info `"WhisperRatchet"`. -/
def kdfRk (rk dhOut: Bytes): Bytes × Bytes :=
  let prk := hmac rk dhOut
  (hkdfBlock1 prk (lit "WhisperRatchet"), hkdfBlock2 prk (lit "WhisperRatchet"))

/-- Derives a `(rootKey, chainKey)` pair from root key `rk`, normalized peer public key `theirPk`,
and local secret key `ourSk`. -/
def createChain (rk theirPk ourSk: Bytes): Bytes × Bytes :=
  kdfRk rk (DiffieHellman.dh (X25519.normalizeX25519Key theirPk) ourSk)

end DY.Libsignal.PQXDH
