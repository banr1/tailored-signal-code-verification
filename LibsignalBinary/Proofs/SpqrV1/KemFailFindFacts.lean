/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.KemFailFind
public import LibsignalBinary.Proofs.SpqrV1.MlKemCorrectFacts
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire

set_option warningAsError false

/-!
# Non-Vacuity and Error-Reduction Facts for `KemFailFind`

Establishes that `KemFailFind` has advantage `0` against `MlKem.ideal` and advantage `1` against
`MlKem.toyFailing`, and shows that on valid inputs all wrapper and length error branches in
`MlKem.honestExchangeFails` vanish, reducing failure to decapsulation mismatch.
-/

@[expose] public section
