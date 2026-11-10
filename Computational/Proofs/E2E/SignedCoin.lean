/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Proofs.E2E.ComposedPrefixHelpers

/-!
# Coin FS-AEAD adversaries on mixtures

**Checked by Lean.** Relates the bias of a mixture of coin FS-AEAD games
(`C o >>= fun _ => sampleT Bool`) to the expected FS-AEAD advantage across the prefix `oa`.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.SM.Construction CryptoGames.SM.Construction.AuthL11

section Coin

variable {K SS RS AD M E : Type} [DecidableEq AD] [DecidableEq M] [DecidableEq E]
  [SampleableType K]

/-- The win experiment of `C` in the FS-AEAD game with bit `b`. -/
def fsWinB {α : Type} (fs : FSAEADScheme K SS RS AD M E)
    (C : FSAEAD.AdversaryComp SS RS AD M E α) (b : Bool) : ProbComp Bool :=
  ($ᵗ K : ProbComp K) >>= fun k =>
    (simulateQ (implFS fs) C).run (FSAEAD.initState fs k b) >>= fun z => pure z.2.win

theorem game_coin_eq {α : Type} (fs : FSAEADScheme K SS RS AD M E)
    (C : FSAEAD.AdversaryComp SS RS AD M E α) :
    FSAEAD.game fs (show FSAEAD.AdversaryComp SS RS AD M E Bool from C >>= fun _ => sampleT Bool) =
      (($ᵗ Bool : ProbComp Bool) >>= fun b => fsWinB fs C b >>= fun w =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b' || w)) := by
  unfold FSAEAD.game fsWinB
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, simulateQ_sampleT_run]

/-- The bias of a mixture of coin FS-AEAD games equals the expected advantage over `oa`. -/
theorem boolBias_mix_coin {β α : Type} (oa : ProbComp β) (fs : β → FSAEADScheme K SS RS AD M E)
    (C : β → FSAEAD.AdversaryComp SS RS AD M E α) :
    letI : MeasurableSpace β := ⊤
    𝒟[oa >>= fun o => FSAEAD.game (fs o)
        (show FSAEAD.AdversaryComp SS RS AD M E Bool from C o >>= fun _ => sampleT Bool)].boolBias =
      ∫⁻ o, FSAEAD.advantage (fs o)
        (show FSAEAD.AdversaryComp SS RS AD M E Bool from C o >>= fun _ => sampleT Bool)
        ∂𝒟[oa] := by
  let _ : MeasurableSpace β := ⊤
  simp_rw [advantage_bind_sampleT_bool, game_coin_eq]
  have h1 : 𝒟[oa >>= fun o => ($ᵗ Bool : ProbComp Bool) >>= fun b => fsWinB (fs o) (C o) b >>=
        fun w => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b' || w)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => (oa >>= fun o => fsWinB (fs o) (C o) b) >>=
        fun w => ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b' || w)] := by
    rw [OracleComp.evalDist_bind_bind_swap]
    simp only [bind_assoc]
  rw [h1, boolBias_bind_coin_or, OracleComp.evalDist_bind_bind_swap, evalDist_bind_apply_lintegral]
  refine lintegral_congr fun o => ?_
  unfold fsWin fsWinB
  rfl

end Coin

section Red

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

end Red

end CryptoVerification.E2E.Signed
