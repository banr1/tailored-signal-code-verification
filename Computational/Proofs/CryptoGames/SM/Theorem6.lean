/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions
public import Computational.Proofs.CryptoGames.SM.Theorem12
public import Computational.Proofs.CryptoGames.SM.Theorem8
import Computational.Proofs.CryptoGames.SM.Theorem1

/-!
# Theorem 6: Security of the Fig. 8 SM Scheme

**Checked by Lean.** Defines the concrete advantage bound `theorem6Bound` for ACD19 Theorem 6
(DEV-SM17, DEV-SM22), shared by the full game (`SM/DDHFig6Composition.lean`, DEV-SM26) and the `H1`
blanked variant on the libsignal chain (`SM/Theorem6Libsignal.lean`, DEV-LS6, DEV-LS13).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

/-- Concrete ACD19 Theorem 6 advantage bound for an adversary `A` making at most `q` queries
against `scheme cka prng fs lam`, summed over epoch and last-leak guesses with parameterized
epoch-`i` privacy reductions `privRed i` (DEV-SM2, DEV-SM19, DEV-SM20, DEV-SM25, DEV-SM27). -/
noncomputable def theorem6Bound (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep q : ℕ)
    (privRed : ℕ → SchemeAdversary Γ T Sig SS RS M CCoins E →
      SchemeAdversary Γ T Sig SS RS M CCoins E)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) : ℝ≥0∞ :=
  2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) t,
      (CKA.advantage cka Δcka (healEpoch tL)
          (redCKAAuth cka prng fs lam Δcka qep tL t (Thm1.challSim (2 + Δcka) qep A))
        + PRFPRNG.advantage prng
          (redPRNGAuth cka prng fs lam Δcka qep tL t (Thm1.challSim (2 + Δcka) qep A))
        + ∑ j ∈ Finset.range q, FSAEAD.advantage fs
            (redFSAuth cka prng fs lam Δcka qep j tL t (Thm1.challSim (2 + Δcka) qep A)))
    + 2 * ∑ i ∈ Finset.range (qep + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) i,
      (2 * CKA.advantage cka Δcka (healEpoch tL)
          (redCKAPriv cka prng fs lam Δcka qep tL i (privRed i A))
        + 2 * PRFPRNG.advantage prng
          (redPRNGPriv cka prng fs lam Δcka qep tL i (privRed i A))
        + FSAEAD.advantage fs
          (redFSPriv cka prng fs lam Δcka qep tL i (privRed i A))
        + 2 * FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam Δcka qep tL i
          (privRed i A)))

/-! **DEV-SM22 (formalization): correctness is a hypothesis.** ACD19 Thm 6 derives SM correctness
from Thm 7, whereas `theorem6_concrete` assumes CKA and SM correctness explicitly because generic
FS-AEAD correctness is not defined (DEV-SM23). -/

end CryptoGames.SM.Construction

/-! **DEV-SM23 (formalization): Thm 7 for the Fig. 6 FS-AEAD.** Correctness of Fig. 8 is proved for
`FSAEAD.fromAEADPRG` rather than an arbitrary FS-AEAD scheme. -/

/-! **DEV-CKA9 (formalization): calls out of ping-pong order return key `0`.** The DDH CKA scheme of
ACD19 §4.1.2 is made total by returning key `0` on out-of-order state cases. -/
