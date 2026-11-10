/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.States

/-!
# SPQR V1: ML-KEM-768 δ-correctness (`MlKem.CorrectWith`)

**Trusted in part.** The theorems of `Computational/Theorems/` use `MlKem.honestExchangeFails` from this
file; `CorrectWith` is checked by Lean (see `Computational/docs/TRUSTED_BASE.md`).

Defines the single-exchange failure predicate `MlKem.honestExchangeFails` over the incremental
ML-KEM wrappers (`generate`, `encaps1`, `ek_matches_header`, `encaps2` with the issue-1275 fix-up,
and `decaps` in `States.lean`), and the average-case δ-correctness hypothesis `MlKem.CorrectWith`
over uniform 64-byte keygen seed and 32-byte encapsulation randomness (FIPS 203 §3.2, Table 1;
DEV-SPQR6).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open OracleComp ENNReal

/-- Returns `true` when one honest SPQR ML-KEM exchange fails on 64-byte keygen `seed` and 32-byte
encapsulation randomness `m`: any wrapper (`generate`, `encaps1`, `encaps2`, `decaps`) errors,
`ek_matches_header` rejects the generated `ek`, or the decapsulated secret differs from the
encapsulated one. -/
def MlKem.honestExchangeFails (K : MlKem) (seed : List.Vector (BitVec 8) 64)
    (m : List.Vector (BitVec 8) 32) : Bool :=
  match LibsignalSpqrV1.generate K seed.toList with
  | .error _ => true
  | .ok (keys, _) =>
    match LibsignalSpqrV1.encaps1 K keys.hdr m.toList with
    | .error _ => true
    | .ok ((ct1, es, ssB), _) =>
      if !(LibsignalSpqrV1.ek_matches_header K keys.ek keys.hdr) then true else
      match LibsignalSpqrV1.encaps2 K keys.ek es with
      | .error _ => true
      | .ok ct2 =>
        match LibsignalSpqrV1.decaps K keys.dk ct1 ct2 with
        | .error _ => true
        | .ok ssA => decide (ssA ≠ ssB)

/-- Average-case δ-correctness for the incremental ML-KEM API (`K : MlKem`): over uniform 64-byte
keygen `seed` and uniform 32-byte encapsulation randomness `m`, `K.honestExchangeFails seed m` is
`true` with probability at most `δ` (FIPS 203 §3.2, Table 1: `δ = 2^-164.8` for ML-KEM-768;
DEV-SPQR6). -/
def MlKem.CorrectWith (K : MlKem) (δ : ℝ≥0∞) : Prop :=
  𝒟[do
      let seed ← $ᵗ (List.Vector (BitVec 8) 64)
      let m ← $ᵗ (List.Vector (BitVec 8) 32)
      pure (K.honestExchangeFails seed m)] {true} ≤ δ

end CryptoVerification.LibsignalSpqrV1
