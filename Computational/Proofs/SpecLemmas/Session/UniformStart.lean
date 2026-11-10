/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.SpkHop2Red

/-!
# Uniform-start PRG distinguisher

**Checked by Lean.**

Defines the shallow PRG distinguisher `uniformStartDistinguisher` for replacing root-KDF epoch-0
keys with uniform keys in `libsignalSessionSchemeFromEpoch0Keys`.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession

/-- PRG distinguisher running `SM.runR` on `libsignalSessionSchemeFromEpoch0Keys` with epoch-0 keys
`rc` and a uniform hidden bit. -/
def uniformStartDistinguisher {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (qep : ℕ) (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    PRGScheme.PRGAdversary (Ratchet.RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let (b', s) ← SM.runR (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep cfg b A
  return (b == b' || s.win)

end CryptoVerification.E2E
