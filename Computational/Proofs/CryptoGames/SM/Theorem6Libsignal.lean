/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import Computational.Proofs.CryptoGames.SM.Theorem6
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs
import Computational.Proofs.CryptoGames.SM.SessionProofs.BlankLemma18
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.CryptoGames.SM.Theorem12
import Computational.Proofs.CryptoGames.SM.Theorem8

/-!
# Theorem 6 on the Libsignal Chain

**Checked by Lean.** Proves `theorem6_h1_blank_concrete`, the ACD19 Theorem 6 bound for hybrid
`Config.h1` (DEV-LS6) with blanked privacy reductions `ThmB.privRedB` on equal-public-part challenge
adversaries (DEV-LS13).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM

variable {Key St Msg Coins C Pub : Type} [DecidableEq Msg] [DecidableEq C] [DecidableEq Pub]
  [SampleableType Key] [SampleableType Coins]

/-- Theorem 1 at `Config.h1` with blanked privacy reductions `ThmB.privRedB` for equal-pub
adversaries. -/
theorem theorem1_h1_blank (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (pubOf : Msg → Pub) (blank : Msg → Msg) (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁)
    (A : Adversary St Msg Coins C) (heq : EqualPubChalls pubOf A) :
    hybridAdvantage sm Δ qep Config.h1 A ≤
      2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
            authAdvantage sm Δ qep tL t (Thm1.challSim Δ qep A)
        + 2 * ∑ i ∈ Finset.range (qep + 1), ∑ tL ∈ admissibleLastLeakGuesses Δ i,
            privAdvantage sm Δ qep tL i (ThmB.privRedB Δ qep i blank A) := by
  exact CryptoGames.LibsignalSM.Proofs.BlankLemma18.theorem1_h1_blank_proof sm Δ qep hΔ pubOf blank hblank A heq

end CryptoGames.SM

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] [DecidableEq Pub]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

/-- Concrete Theorem 6 bound `theorem6Bound` for `Config.h1` with blanked privacy reductions
`ThmB.privRedB` on equal-pub adversaries (DEV-LS6, DEV-LS13, DEV-SM2, DEV-SM19, DEV-SM20,
DEV-SM25). -/
theorem theorem6_h1_blank_concrete (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (hc : cka.Correct)
    (pubOf : M → Pub) (blank : M → M) (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) (heq : EqualPubChalls pubOf A) (q : ℕ)
    (hq : MakesAtMostQueries A q) :
    hybridAdvantage (scheme cka prng fs lam) (2 + Δcka) qep Config.h1 A ≤
      theorem6Bound cka prng fs lam Δcka qep q (fun i => ThmB.privRedB (2 + Δcka) qep i blank) A := by
  have h := theorem1_h1_blank (scheme cka prng fs lam) (2 + Δcka) qep (by omega) pubOf blank hblank
    A heq
  refine h.trans ?_
  unfold theorem6Bound
  gcongr with t _ tL _ i _ tL _
  · exact theorem8 cka prng fs lam Δcka qep hc tL t q _ (Thm1.challSim_queries _ _ A q hq)
  · exact theorem12 cka prng fs lam Δcka qep hc tL i _

end CryptoGames.SM.Construction
