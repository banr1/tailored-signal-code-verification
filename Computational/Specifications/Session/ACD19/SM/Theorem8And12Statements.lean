/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction -- shake: keep

/-!
# Theorems 8 and 12: authenticity and privacy of the Fig. 8 SM scheme (statements)

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use
`healEpoch` and `SM.specDF`, the only definitions in this file. `SchemeAdversary`, `Theorem8` and
`Theorem12` are in `Computational/Proofs/SpecLemmas/Session/ACD19/SM/Theorem8And12Statements.lean`,
checked by Lean. See `Computational/docs/TRUSTED_BASE.md` §7.

In ACD19 (Alwen, Coretti, Dodis, ePrint 2018/1037, §5.3.2–5.3.3, Theorems 8 and 12), the Fig. 8
Double Ratchet secure-messaging scheme (`LibsignalBinary/Specifications/CryptoGames/SM/Construction.lean`)
achieves authenticity and privacy for `Δ_SM = 2 + Δ_CKA` from a CKA scheme, a root PRF-PRNG, and an
FS-AEAD scheme:

* `Adv^{auth}_{t*_L,t*}(A) ≤ Adv^{CKA}(R₁ A) + Adv^{PP}(R₂ A) + Σ_{j<q} Adv^{fs-aead}(R₃,j A)`,
* `Adv^{priv}_{t*_L,t*}(A) ≤ 2·Adv^{CKA}(R₁ A) + 2·Adv^{PP}(R₂ A) + Adv^{fs-aead}(R₃ A)
    + 2·Adv^{fs-aead}(R₃' A)`,

for `q`-query adversaries `A`, attacked epoch `t*`, last prior leak `t*_L`, and CKA healing epoch
`t_heal = t*_L + 2` (`healEpoch`). `Theorem8` and `Theorem12` parameterize over the reductions
`R₁`, `R₂`, `R₃`, instantiated and proved in `Computational/Proofs/CryptoGames/SM/`.

Authenticity is a winning probability while CKA and PRF-PRNG advantages are real/ideal distances, so
each hop costs `1×` advantage, and `R₃,j` attacks the `j`-th epoch-`t*` FS-AEAD session and outputs
a coin. Privacy is a bias (`2·|Pr − 1/2|`), so each distance hop costs `2×` advantage (DEV-SM20) and
the final FS-AEAD hop costs `Adv(R₃) + 2·Adv(R₃')`, where `R₃'` outputs a coin on forgery
(DEV-SM25); ACD19 writes factor `1` on both bounds and omits the forgery term in Lemma 15.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM

/-- Six-oracle `DeliverForge` SM specification extending `SM.spec` with
`(Party × C × C) →ₒ Option (RecvResult Msg)` for distinct ciphertexts sharing wire bytes. -/
abbrev specDF (St Msg Coins C : Type) :=
  SM.spec St Msg Coins C + ((Party × C × C) →ₒ Option (RecvResult Msg))

end CryptoGames.SM

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

/-- CKA challenge (healing) epoch `t_heal = t*_L + 2`, or `0` when `t*_L = −∞`.

**DEV-SM27 (formalization): `t*_L = −∞`.** ACD19 (§5.3.2, footnote 13) omits the case with no leak
before `t*`, where the root RNG starts uncorrupted and no CKA step is needed. Setting
`healEpoch none = 0` places the CKA challenge at epoch `0`, which has no challenge and thus zero
advantage for every adversary. -/
def healEpoch : Option ℕ → ℕ
  | none => 0
  | some l => l + 2

variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

end CryptoGames.SM.Construction
