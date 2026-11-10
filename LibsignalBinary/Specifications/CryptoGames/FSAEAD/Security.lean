/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction

/-!
# FS-AEAD security statement: ACD19 Thm 5 for the symmetric ratchet

**Trusted in part.** The theorems of `Computational/Theorems/` use only `RatchetAdversary` from this
file: read it. Everything else here is checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

States ACD19 Thm 5 (`Theorem5Statement`) for the symmetric ratchet `fromAEADPRG` against a
`RatchetAdversary`, parameterized by explicit reductions `prgRed` and `aeadRed` (DEV-FS15) under
windowed correctness (DEV-FS5) and uncompromised-record `corr-B` blocking (DEV-FS6); AD-dependent
ideal ciphertexts (DEV-FS17) and restricted-AD correctness (DEV-FS18) are stated in
`SecurityWith.lean` and `Theorem5On.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.FSAEAD

variable {ChainKey MessageKey AssocData Message Ciphertext : Type}
  [DecidableEq AssocData] [DecidableEq Message] [DecidableEq Ciphertext]
  [SampleableType ChainKey] [SampleableType MessageKey] [SampleableType Ciphertext]

/-- FS-AEAD adversary against `fromAEADPRG` (ACD19 Def. 15). -/
abbrev RatchetAdversary (ChainKey MessageKey AssocData Message Ciphertext : Type) :=
  Adversary (RatchetSenderState ChainKey) (RatchetReceiverState ChainKey MessageKey)
    AssocData Message (ℕ × Ciphertext)

/-- ACD19 Thm 5 security bound for `fromAEADPRG` parameterized by reductions `prgRed` and `aeadRed`.

**DEV-FS12 (paper fix): bounded-skip hybrid slot count, not `q`.** Bounded skipping (DEV-FS9) yields
`2(q+1)(maxSkip+1)` hybrid steps here, tightened on the headline chain (`Theorem5On.lean`) to
`2q + (maxSkip + 1)` active slots.

**DEV-FS13 (formalization): factor 2.** Bias convention `2 · |Pr[win] - 1/2|` (Def. 15) introduces a
leading factor of `2`.

**DEV-FS14 (paper fix): a second hybrid chain for lookahead forgeries.** Odd steps `j = 2k + 1` run
a lookahead hybrid chain stopping at the first corruption to bound accepted injections ahead of
`lastSentIdx`.

**DEV-FS15 (formalization): named reductions.** Reductions `prgRed` and `aeadRed` are explicit
parameters rather than existential quantifiers. -/
def Theorem5Statement (ae : AEADScheme MessageKey (ℕ × AssocData) Message Ciphertext)
    (G : ℕ → PRGScheme ChainKey (ChainKey × MessageKey)) (maxSkip : ℕ)
    (prgRed : ℕ → RatchetAdversary ChainKey MessageKey AssocData Message Ciphertext →
      PRGScheme.PRGAdversary (ChainKey × MessageKey))
    (aeadRed : ℕ → RatchetAdversary ChainKey MessageKey AssocData Message Ciphertext →
      AEADScheme.OTCCAAdversary (ℕ × AssocData) Message Ciphertext) : Prop :=
  ∀ (A : RatchetAdversary ChainKey MessageKey AssocData Message Ciphertext) (q : ℕ),
    MakesAtMostQueries A q →
    advantage (fromAEADPRG ae G maxSkip) A ≤
      2 * ∑ j ∈ Finset.range (2 * ((q + 1) * (maxSkip + 1))),
        ((G (j / 2)).prgAdvantage (prgRed j A) + ae.otccaAdvantage (aeadRed j A))

end CryptoGames.FSAEAD
