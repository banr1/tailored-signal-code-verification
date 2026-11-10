/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Game

/-!
# Closed-form handshake security bound for PQXDH

**Trusted: the statement.** `pqxdhKeyIndBoundActive` (with `activeIdCount`, `activeSpkCount`,
`activeOpkCount`, `activeSendCount`, `activeSendOpkCount`, `activeDhCount`) and
`Security.kemDecapsFailureTerm` are used directly by the `KeyInd` and CLI security statements
(`Security/HeadlineDelta.lean`, `LibsignalCli/StatementPqElf.lean`); the static `pqxdhKeyIndBound`
is used by `pqxdhAuthBound` (`Security/Auth/Game.lean`) and `pqxdhKeyIndBoundActive_le`. The HNDL
(`-D KEM`) bounds and `deploymentSetup` live in
`Computational/Proofs/SpecLemmas/SignalPqxdh/Bound.lean`. See `Computational/docs/TRUSTED_BASE.md`.

`pqxdhKeyIndBoundActive` bounds the adversary's advantage in the multi-session PQXDH
key-indistinguishability game (`KeyInd1KeyRoAdvantage`) in the classical `-D DH` regime where the
handshake KDF (`HkdfRO`) is a random oracle, in terms of the online query budget `q_on`, `Setup`
replication capacities, and handshake assumption advantages (`Assumptions/Assumptions.lean`). See
`Computational/docs/PQXDH.md` for term-by-term derivations and numerical evaluation.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open scoped ENNReal

/-- Static-capacity upper bound on `KeyInd` advantage in the `-D DH` regime from the handshake
    assumption advantages (`GapSigEufCma`, `KemShCr`, `GapDhWithSign`; see `DEV-PQ17`) and `Setup`
    counts. The X25519 collision term sums `2^-250` per unordered pair over `N_dh` public keys and
    `N_send_tot` initiator `dh2` values; the Kyber-1024 collision term sums `2^-255` over unordered
    `N_spk_tot` PQSPK pairs. -/
noncomputable def pqxdhKeyIndBound
    (S : Setup)
    (epsSig epsKemShCr epsGapDh : ℝ≥0∞) : ℝ≥0∞ :=
  (S.N_id : ℝ≥0∞) * epsSig +
  ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 251 +
  (S.N_spk_tot : ℝ≥0∞) * (S.N_send_tot : ℝ≥0∞) * epsKemShCr +
  ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 +
  2 * ((S.N_spk_tot : ℝ≥0∞) * ((S.N_id : ℝ≥0∞) + (S.N_send_tot : ℝ≥0∞)) +
    (S.N_id : ℝ≥0∞) * (S.N_send_tot : ℝ≥0∞) +
    (S.N_opk_tot : ℝ≥0∞) * (S.N_send_opk_tot : ℝ≥0∞)) * epsGapDh

namespace Security

/-- KEM δ-correctness term: union bound of honest decapsulation failure (`KemDeltaCorrect P δ`)
    over `(N_send_tot, N_spk_tot)` session–pre-key pairs, scaled by the `boolBias` factor `2`. -/
noncomputable def kemDecapsFailureTerm (S : Setup) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  2 * (S.N_send_tot : ℝ≥0∞) * (S.N_spk_tot : ℝ≥0∞) * δ

end Security

/-! ## Activity-bounded key-indistinguishability bound

Each online `KeyIndQuery S` (`isKeyIndOnlineQuery`, excluding `.roQuery`) creates at most one
honest principal, pre-key bundle, one-time pre-key, initiator session, and X25519 public key, so
every active count is bounded by `min q_on S.N_*`. -/

def activeIdCount (S : Setup) (q_on : Nat) : Nat := min q_on S.N_id

def activeSpkCount (S : Setup) (q_on : Nat) : Nat := min q_on S.N_spk_tot

def activeOpkCount (S : Setup) (q_on : Nat) : Nat := min q_on S.N_opk_tot

def activeSendCount (S : Setup) (q_on : Nat) : Nat := min q_on S.N_send_tot

def activeSendOpkCount (S : Setup) (q_on : Nat) : Nat := min q_on S.N_send_opk_tot

def activeDhCount (S : Setup) (q_on : Nat) : Nat := min q_on S.N_dh

/-- Activity-bounded upper bound on `KeyInd` advantage in the `-D DH` regime, obtained from
    `pqxdhKeyIndBound` by replacing static `Setup` capacities with `min q_on S.N_*`. -/
noncomputable def pqxdhKeyIndBoundActive
    (S : Setup) (q_on : Nat)
    (epsSig epsKemShCr epsGapDh : ℝ≥0∞) : ℝ≥0∞ :=
  let n_id := activeIdCount S q_on
  let n_spk := activeSpkCount S q_on
  let n_opk := activeOpkCount S q_on
  let n_send := activeSendCount S q_on
  let n_send_opk := activeSendOpkCount S q_on
  let n_dh := activeDhCount S q_on
  (n_id : ℝ≥0∞) * epsSig +
  ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 251 +
  (n_spk : ℝ≥0∞) * (n_send : ℝ≥0∞) * epsKemShCr +
  ((n_spk * (n_spk - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 +
  2 * ((n_spk : ℝ≥0∞) * ((n_id : ℝ≥0∞) + (n_send : ℝ≥0∞)) +
    (n_id : ℝ≥0∞) * (n_send : ℝ≥0∞) +
    (n_opk : ℝ≥0∞) * (n_send_opk : ℝ≥0∞)) * epsGapDh

/-- The activity-bounded advantage bound is at most the static capacity bound. -/
theorem pqxdhKeyIndBoundActive_le
    (S : Setup) (q_on : Nat)
    (epsSig epsKemShCr epsGapDh : ℝ≥0∞) :
    pqxdhKeyIndBoundActive S q_on epsSig epsKemShCr epsGapDh ≤
      pqxdhKeyIndBound S epsSig epsKemShCr epsGapDh := by
  unfold pqxdhKeyIndBoundActive pqxdhKeyIndBound
    activeIdCount activeSpkCount activeOpkCount
    activeSendCount activeSendOpkCount activeDhCount
  dsimp only
  have hid : min q_on S.N_id ≤ S.N_id := Nat.min_le_right _ _
  have hspk : min q_on S.N_spk_tot ≤ S.N_spk_tot := Nat.min_le_right _ _
  have hopk : min q_on S.N_opk_tot ≤ S.N_opk_tot := Nat.min_le_right _ _
  have hsend : min q_on S.N_send_tot ≤ S.N_send_tot := Nat.min_le_right _ _
  have hsopk : min q_on S.N_send_opk_tot ≤ S.N_send_opk_tot := Nat.min_le_right _ _
  have hdh : min q_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hec : min q_on S.N_dh * (min q_on S.N_dh - 1) +
      min q_on S.N_send_tot * (min q_on S.N_send_tot - 1) ≤
      S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) :=
    Nat.add_le_add (Nat.mul_le_mul hdh (Nat.sub_le_sub_right hdh 1))
      (Nat.mul_le_mul hsend (Nat.sub_le_sub_right hsend 1))
  have hkem : min q_on S.N_spk_tot * (min q_on S.N_spk_tot - 1) ≤
      S.N_spk_tot * (S.N_spk_tot - 1) :=
    Nat.mul_le_mul hspk (Nat.sub_le_sub_right hspk 1)
  gcongr

end SignalPqxdh
