/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect

/-!
# SPQR V1: ML-KEM-768 failure-finding assumption (`KemFailFind`) and bad event (`KemFailBad`)

**Trusted in part.** `MlKem.KemFailFindAdversary`, `MlKem.kemFailFindGame`,
`MlKem.kemFailFindAdvantage`, `MlKem.tapePairFails` and `MlKem.KemFailBad`
(`Computational/docs/TRUSTED_BASE.md` §3): computational failure-search game (`KemFailFind`,
`kemFailFindAdvantage`) on `K : MlKem` and the real-game bad event charged by the headline
statements.

In `LibsignalGame`, sender coins on `transmit-P` and `chall-P` are chosen by the adversary (whereas
receive coins are uniform, DEV-LS1), so average-case correctness (`MlKem.CorrectWith`) does not rule
out decapsulation failure along an execution trace. Because `K : MlKem` is an unkeyed deterministic
primitive with non-zero failure density (`δ ≈ 2^-164.8` in ML-KEM-768, FIPS 203 §3.2 Table 1), a
non-uniform constant adversary achieves advantage `1`, so headline statements must not quantify over
`sup_B` or evaluate `kemFailFindAdvantage` on an `∃`-bound reduction. Instead, the headline
statements charge `MlKem.KemFailBad` directly on the protocol adversary's logged 64-byte send tapes;
a fixed extractor outputting a logged pair `(seed, m)` reduces `KemFailBad` to `KemFailFind`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open OracleComp OracleSpec ENNReal

/-- Coin-only probabilistic adversary outputting a candidate 64-byte key-generation seed and 32-byte
encapsulation randomness `(seed, m)`. -/
abbrev MlKem.KemFailFindAdversary : Type :=
  ProbComp (List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32)

/-- `KemFailFind` game for `K : MlKem`: runs `B` and returns `K.honestExchangeFails seed m`. -/
def MlKem.kemFailFindGame (K : MlKem) (B : MlKem.KemFailFindAdversary) : ProbComp Bool := do
  let (seed, m) ← B
  return K.honestExchangeFails seed m

abbrev KemFailFind (K : MlKem) (B : MlKem.KemFailFindAdversary) : ProbComp Bool :=
  K.kemFailFindGame B

/-- Advantage in the `KemFailFind` game (`𝒟[K.kemFailFindGame B] {true}`). -/
noncomputable def MlKem.kemFailFindAdvantage (K : MlKem) (B : MlKem.KemFailFindAdversary) :
    ℝ≥0∞ :=
  𝒟[K.kemFailFindGame B] {true}

noncomputable abbrev kemFailFindAdvantage (K : MlKem) (B : MlKem.KemFailFindAdversary) : ℝ≥0∞ :=
  K.kemFailFindAdvantage B

/-! ## Real-game KEM-failure bad event (`KemFailBad`) -/

/-- Whether 64-byte send tapes `t₁`, `t₂` form a failing honest SPQR V1 ML-KEM exchange
(`K.honestExchangeFails t₁ (t₂.take 32)`). -/
def MlKem.tapePairFails (K : MlKem) (t₁ t₂ : List (BitVec 8)) : Bool :=
  if h₁ : t₁.length = 64 then
    if h₂ : t₂.length = 64 then
      K.honestExchangeFails ⟨t₁, h₁⟩ ⟨t₂.take 32, by simp [h₂]⟩
    else false
  else false

/-- KEM-failure bad event on a log of 64-byte send tapes: some ordered pair `(t₁, t₂)` satisfies
`K.tapePairFails t₁ t₂`. -/
def MlKem.KemFailBad (K : MlKem) (log : List (List (BitVec 8))) : Bool :=
  log.any fun t₁ => log.any fun t₂ => K.tapePairFails t₁ t₂

end CryptoVerification.LibsignalSpqrV1
