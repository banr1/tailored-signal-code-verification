/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Symbol Names for SPQR KDF Subroutines

Binary symbol names for `spqr::kdf::hkdf_to_slice`, `spqr::kdf::hkdf_to_vec`, and their
monomorphized `Hmac<Sha256>` callees.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Kdf


abbrev newFromSlice3Name : String :=
  "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#2]"

abbrev finalizeFixed3Name : String :=
  "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#2]"

abbrev hkdfToSliceName : String :=
  "spqr::kdf::hkdf_to_slice"

abbrev hkdfToVecName : String :=
  "spqr::kdf::hkdf_to_vec"

end CryptoVerification.SpqrV1.Kdf
