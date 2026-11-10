/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security

/-!
# OT-CCA and ACD19 Thm 5 with an AD-dependent ideal ciphertext (DEV-FS17)

**Checked by Lean.** No theorem of `Computational/Theorems/` uses anything from this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust the results. See
`Computational/docs/TRUSTED_BASE.md`.

Generalizes `otccaGame` and `Theorem5Statement` from uniform ideal ciphertexts `$ᵗ C` to an
AD-dependent ideal distribution `ideal a` (`otccaGameAdIdeal`, `otccaAdvantageAdIdeal`,
`Theorem5StatementAdIdeal`), avoiding `SampleableType C` for wire formats carrying public headers.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

namespace AEADScheme

variable {Key AD M C : Type}

/-- OT-CCA `encrypt(a, m)` oracle sampling ideal ciphertexts from `ideal a`.

**DEV-FS17 (libsignal): the ideal ciphertext may depend on the AD.** Replaces uniform `$ᵗ C` in
ACD19 Def. 2 with `ideal a` (independent of `m`) for wire formats carrying public headers; when
`ideal = fun _ => $ᵗ C`, `otccaAdvantageWith_uniform` recovers `otccaAdvantage` by `rfl`. -/
def otccaEncryptAdIdeal (ae : AEADScheme Key AD M C) (ideal : AD → ProbComp C) :
    QueryImpl ((AD × M) →ₒ Option C) (StateT (OTCCAState Key AD C) ProbComp) := fun ⟨a, m⟩ => do
  let st ← get
  if st.chal.isSome then return none
  let e ← if st.b then liftM (ideal a) else pure (ae.enc st.key a m)
  set { st with chal := some (a, e) }
  return some e

/-- OT-CCA hidden-bit game with ideal ciphertexts drawn from `ideal`. -/
def otccaGameAdIdeal [SampleableType Key] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme Key AD M C) (ideal : AD → ProbComp C) (A : OTCCAAdversary AD M C) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let key ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (OTCCAState Key AD C) ProbComp)
    + (ae.otccaEncryptAdIdeal ideal + ae.otccaDecrypt)
  let b' ← (simulateQ impl A).run' { key, b }
  return b == b'

/-- OT-CCA advantage `Adv^{ot-cca}_{AE, ideal}(A)` with AD-dependent ideal ciphertexts. -/
noncomputable def otccaAdvantageAdIdeal [SampleableType Key] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme Key AD M C) (ideal : AD → ProbComp C) (A : OTCCAAdversary AD M C) : ℝ≥0∞ :=
  𝒟[ae.otccaGameAdIdeal ideal A].boolBias

theorem otccaAdvantageWith_uniform [SampleableType Key] [DecidableEq AD] [DecidableEq C]
    [SampleableType C] (ae : AEADScheme Key AD M C) (A : OTCCAAdversary AD M C) :
    ae.otccaAdvantageAdIdeal (fun _ => $ᵗ C) A = ae.otccaAdvantage A := rfl

end AEADScheme

namespace FSAEAD

variable {CK MK AD M C : Type}

/-- ACD19 Thm 5 security bound (`Theorem5Statement`) with AD-dependent OT-CCA ideal ciphertexts
`ideal`. -/
def Theorem5StatementAdIdeal [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType CK]
    [SampleableType MK] (ae : AEADScheme MK (ℕ × AD) M C) (ideal : ℕ × AD → ProbComp C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (prgRed : ℕ → RatchetAdversary CK MK AD M C → PRGScheme.PRGAdversary (CK × MK))
    (aeadRed : ℕ → RatchetAdversary CK MK AD M C → AEADScheme.OTCCAAdversary (ℕ × AD) M C) :
    Prop :=
  ∀ (A : RatchetAdversary CK MK AD M C) (q : ℕ),
    MakesAtMostQueries A q →
    advantage (fromAEADPRG ae G maxSkip) A ≤
      2 * ∑ j ∈ Finset.range (2 * ((q + 1) * (maxSkip + 1))),
        ((G (j / 2)).prgAdvantage (prgRed j A) + ae.otccaAdvantageAdIdeal ideal (aeadRed j A))

theorem theorem5With_uniform [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType CK]
    [SampleableType MK] [SampleableType C] (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (prgRed : ℕ → RatchetAdversary CK MK AD M C → PRGScheme.PRGAdversary (CK × MK))
    (aeadRed : ℕ → RatchetAdversary CK MK AD M C → AEADScheme.OTCCAAdversary (ℕ × AD) M C) :
    Theorem5StatementAdIdeal ae (fun _ => $ᵗ C) G maxSkip prgRed aeadRed ↔
      Theorem5Statement ae G maxSkip prgRed aeadRed := Iff.rfl

end FSAEAD

end CryptoGames
