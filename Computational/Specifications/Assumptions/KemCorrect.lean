/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Game

/-!
# δ-correctness and cryptographic well-formedness of the PQXDH primitives

**Trusted: definitions used by the statement.** `kemHonestExchangeFails`, `KemDeltaCorrect`,
`CryptoWellFormedDh`, `CryptoWellFormedKemδ` and `CryptoWellFormedPrimitivesδ` are read by the
δ-statement (`Security/HeadlineDelta.lean` under `Computational/Specifications/Pqxdh/`); see
`Computational/docs/TRUSTED_BASE.md`.

Kyber-1024 (`libcrux_ml_kem::kyber1024` in libsignal) has a small nonzero decapsulation-failure
probability (DEV-PQ21) rather than perfect KEM correctness (`WellFormedPrimitives.kem_corr`).
Together with `WellFormedPrimitivesδ` (`Model.lean`), this file defines `KemDeltaCorrect P δ`,
bounding the honest failure probability by `δ`, and `CryptoWellFormedPrimitivesδ P`, recording the
X25519 and Kyber-1024 public-key collision bounds and wire-length rejection laws. The bound `δ` is
taken as a hypothesis: FIPS 203 (Aug. 2024, Table 1) gives `δ = 2^-174.8` for ML-KEM-1024 and the
Kyber v3.02 specification (§1.4, Table 1) gives `2^-174` under heuristic noise models.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open scoped ENNReal
open OracleComp OracleSpec ENNReal

/-! ## δ-correctness of the KEM -/

/-- Honest KEM decapsulation-failure event for key-generation seed `seed` and encapsulation coins
    `r`: encapsulation succeeds with `some (ss, ct)`, yet decapsulation under the paired secret key
    does not return `some ss` (encapsulation returning `none` is not counted). -/
def kemHonestExchangeFails (P : Primitives) (seed r : Bytes) : Bool :=
  match P.kemEncaps (P.kemKeyGen seed).1 r with
  | none => false
  | some (ss, ct) => decide (P.kemDecaps (P.kemKeyGen seed).2 ct ≠ some ss)

/-- δ-correctness of the KEM (Fiedler–Günther, ePrint 2024/702, §2; FIPS 203 §3.3):
    `kemHonestExchangeFails P seed r` occurs with probability at most `δ` over uniform 64-byte
    `seed` and 32-byte `r`. -/
def KemDeltaCorrect (P : Primitives) (δ : ℝ≥0∞) : Prop :=
  𝒟[do
      let seed ← sampleRandom64
      let r ← sampleCoins32
      pure (kemHonestExchangeFails P seed r)] {true} ≤ δ

/-! ## Cryptographic well-formedness -/

/-- Cryptographic X25519 and cofactor-8 subgroup laws on `P`: public-key collision bound,
    scalar-multiplication injectivity modulo `pow8`, and 32-byte length of base-point subgroup
    preimages. -/
structure CryptoWellFormedDh (P : Primitives) : Prop where
  /-- Tight `2^-250` public-key collision bound modulo `pow8`: a clamped X25519 scalar `s = 8k`
      draws `k` uniformly from `[2^251, 2^252)` (`2^251` values), and targets with
      `k₁ ∈ [2^251, ℓ - 2^251]` have two clamped preimages `k₁` and `ℓ - k₁` (`k ≡ ±k₁ (mod ℓ)`),
      attaining probability `2 / 2^251 = 2^-250`. -/
  ec_coll_bound :
    ∀ (targetPk : Bytes),
      𝒟[do
        let sk ← sampleScalar32
        pure (P.pow8 (P.x25519Base sk) == P.pow8 targetPk)] {true}
        ≤ 1 / (2 : ℝ≥0∞) ^ 250
  /-- Injectivity of X25519 scalar multiplication modulo `pow8` on 32-byte inputs: for RFC 7748
      clamped scalars `8k` with `2^251 ≤ k < 2^252 < ℓ, ℓ'`, `[k]` is injective on the prime-order
      subgroups of the curve and twist, the output u-coordinate fixes the twist bit, and output `0`
      forces `[8]Q = ∞`. -/
  x25519_inj_pow8 :
    ∀ (a pk1 pk2 : Bytes), a.length = 32 → pk1.length = 32 → pk2.length = 32 →
      P.x25519 a pk1 = P.x25519 a pk2 → P.pow8 pk1 = P.pow8 pk2
  /-- Any byte string whose `pow8` projection matches a base-point output `x25519Base e` (of prime
      order `ℓ`) has length 32, since `pow8` maps non-32-byte inputs to the identity encoding `0^32`. -/
  pow8_base_len :
    ∀ (p e : Bytes), P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32

/-- Cryptographic Kyber-1024 laws on `P`: public-key collision bound and wire-length rejection for
    ciphertexts and public keys. -/
structure CryptoWellFormedKemδ (P : Primitives) : Prop where
  /-- Public-key collision bound `2^-255` under uniform 64-byte seed sampling: Kyber-1024 key
      generation hashes only the 32-byte seed half `d` via `G = SHA3-512`, where a random
      `G : {0,1}^256 → {0,1}^512` has 2-collisions with probability `1 - e^{-1/2} ≈ 0.39` (ruling
      out `2^-256`) while 3-collisions have probability `≈ 2^-258.6`. -/
  kem_coll_bound :
    ∀ (targetPk : Bytes),
      𝒟[do let (pk, _) ← sampleKemKeyGen P; pure (pk == targetPk)] {true}
        ≤ 1 / (2 : ℝ≥0∞) ^ 255
  /-- **DEV-PQ32 (formalization): Kyber-1024 ciphertext and public-key length rejection.**
      Decapsulation rejects any ciphertext whose raw length (after the `0x08` key-type prefix byte)
      differs from `kyberCtLen = 1568` (`Ciphertext::deserialize`). -/
  kemDecaps_len_reject :
    ∀ (sk ct : Bytes), ct.length ≠ kyberCtLen → P.kemDecaps sk ct = none
  /-- Encapsulation rejects any public key whose raw length (after the `0x08` key-type prefix byte)
      differs from `kyberPkLen = 1568` (`PublicKey::deserialize`). -/
  kemEncaps_len_reject :
    ∀ (pk r : Bytes), pk.length ≠ kyberPkLen → P.kemEncaps pk r = none

/-- Cryptographic well-formedness of `P` without perfect KEM correctness (`kem_corr`), combining
    `WellFormedPrimitivesδ P`, `CryptoWellFormedDh P`, and `CryptoWellFormedKemδ P`. -/
structure CryptoWellFormedPrimitivesδ (P : Primitives) : Prop
    extends WellFormedPrimitivesδ P, CryptoWellFormedDh P, CryptoWellFormedKemδ P

end SignalPqxdh
