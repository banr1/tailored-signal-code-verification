/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Concrete.ImageSymbols

/-!
# Proof-side cryptographic stub symbols

Defines `StubSymbol` constants for incremental ML-KEM-768, SHA-512 compression, and Ed25519
curve-core operations used by `ExternInterpretationTotalOnUsedSymbols` and extern-witness tests.
-/

@[expose] public section

namespace DY.Libsignal.PQXDH.Refinement

open DY.Libsignal.Refinement (StubSymbol)

abbrev mlkem768FromSeedSymbol : StubSymbol :=
  "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed"

abbrev mlkem768Encaps1Symbol : StubSymbol := "libcrux_ml_kem::mlkem768::incremental::encapsulate1"

abbrev mlkem768Encaps2Symbol : StubSymbol := "libcrux_ml_kem::mlkem768::incremental::encapsulate2"

abbrev mlkem768ValidatePkSymbol : StubSymbol :=
  "libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes"

abbrev mlkem768DecapsSymbol : StubSymbol :=
  "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key"

abbrev sha512CompressSymbol : StubSymbol := "sha2::sha512::compress512"

abbrev edwardsCompressSymbol : StubSymbol := "<curve25519_dalek::edwards::EdwardsPoint>::compress"

abbrev edwardsNegSymbol : StubSymbol :=
  "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg"

abbrev doubleScalarMulSymbol : StubSymbol :=
  "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint"

abbrev scalarModOrderSymbol : StubSymbol :=
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order"

abbrev scalarModOrderWideSymbol : StubSymbol :=
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide"

end DY.Libsignal.PQXDH.Refinement
