/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Samplers
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRG.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables
import Computational.Proofs.ReductionDsl.Size

/-!
# Size-Honesty Instances for Shared Operation and Sampler Tables

Proves `OpsSizeHonest` and `SampSizeHonest` for `unifSamplers`, `unifSamplers0`, `prgOps`,
`otccaOps`, and `idealSamplers`.
-/

@[expose] public section

namespace ReductionDsl

open OracleComp

theorem sampleIndex_fits (N B : ℕ) :
    ∀ y ∈ support (sampleIndex N), (Ty.nat (S := S)).Fits (B + (bits N + 1)) y := by
  intro y hy
  simp only [sampleIndex] at hy
  split_ifs at hy with h
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨x, -, rfl⟩ := hy
    have hle : x.val ≤ N := Nat.le_of_lt x.isLt
    have hb := bits_mono hle
    simp only [Ty.Fits]; omega
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    have h0 : bits 0 = 1 := rfl
    simp only [Ty.Fits]; omega

theorem SampSizeHonest.unifSamplers {S : Sig} {B : Type} (f : B → S.Base)
    (w : B → ℕ) [∀ b, SampleableType (S.den (f b))]
    (hw : ∀ b y, S.sz (f b) y ≤ w b := by intros; exact le_rfl) :
    SampSizeHonest (unifSamplers (S := S) f w)
  | .bool, _, _, _, _, _ => trivial
  | .index N, _, B₀, _, y, hy => sampleIndex_fits N B₀ y hy
  | .base b, _, B₀, _, y, _ => by
    change S.sz (f b) y ≤ B₀ + w b
    have := hw b y; omega

theorem SampSizeHonest.unifSamplers0 (S : Sig) : SampSizeHonest (unifSamplers0 S) :=
  @SampSizeHonest.unifSamplers S Empty Empty.elim Empty.elim (fun b => b.elim) (fun b => b.elim)

end ReductionDsl

namespace CryptoGames

open ReductionDsl OracleComp

section PRG

open CryptoGames.PRG.Costed

theorem prgOps_sizeHonest {S : Sig} (seedT outT : Ty S) (gen : seedT.denote → outT.denote)
    (k : ℕ) (hout : ∀ x, outT.Fits k (gen x)) :
    OpsSizeHonest (prgOps seedT outT gen k) := by
  intro _ x B _
  exact Ty.fits_mono (by change k ≤ B + k; omega) outT (gen x) (hout x)

theorem prgOps_sizeHonest_pair {S : Sig} (seedT : Ty S) (b₁ b₂ : S.Base)
    (gen : seedT.denote → S.den b₁ × S.den b₂) (k : ℕ)
    (h₁ : ∀ y, S.sz b₁ y ≤ k := by intros; omega)
    (h₂ : ∀ y, S.sz b₂ y ≤ k := by intros; omega) :
    OpsSizeHonest (prgOps seedT (.prod (.base b₁) (.base b₂)) gen k) :=
  prgOps_sizeHonest seedT (.prod (.base b₁) (.base b₂)) gen k fun x => ⟨h₁ (gen x).1, h₂ (gen x).2⟩

end PRG

section OTCCA

open CryptoGames.OTCCA.Costed

theorem otccaOps_sizeHonest {S : Sig} (keyT aeadAdT adT msgT ctT : Ty S)
    [DecidableEq adT.denote] [DecidableEq msgT.denote] [DecidableEq ctT.denote]
    (ae : AEADScheme keyT.denote aeadAdT.denote msgT.denote ctT.denote) (k : ℕ)
    (saltT : Ty S) [DecidableEq saltT.denote] (saltOf : aeadAdT.denote → saltT.denote)
    (hct : ∀ c, ctT.Fits k c) (hmsg : ∀ m, msgT.Fits k m) (hsalt : ∀ s, saltT.Fits k s) :
    OpsSizeHonest (otccaOps keyT aeadAdT adT msgT ctT ae k saltT saltOf)
  | .enc, (key, a, m), B, _ =>
    Ty.fits_mono (by change k ≤ B + k; omega) ctT _ (hct (ae.enc key a m))
  | .dec, (key, a, c), B, _ => by
    simp only [otccaOps]
    rcases ae.dec key a c with _ | m
    · trivial
    · exact Ty.fits_mono (by omega) msgT m (hmsg m)
  | .saltOf, a, B, _ =>
    Ty.fits_mono (by change k ≤ B + k; omega) saltT _ (hsalt (saltOf a))
  | .eqAD, _, _, _ | .eqM, _, _, _ | .eqC, _, _, _ | .eqSalt, _, _, _ => trivial

theorem idealSamplers_sizeHonest {S : Sig} (adT ctT : Ty S)
    (ideal : adT.denote → ProbComp ctT.denote) (kIdeal : ℕ)
    (hct : ∀ a c, c ∈ support (ideal a) → ctT.Fits kIdeal c) :
    SampSizeHonest (idealSamplers adT ctT ideal kIdeal) := by
  intro _ a B _ c hc
  exact Ty.fits_mono (by change kIdeal ≤ B + kIdeal; omega) ctT c (hct a c hc)

end OTCCA

section PRF

open CryptoGames.PRF.Costed

end PRF

section FSAEAD

open CryptoGames.FSAEAD.Costed

end FSAEAD

end CryptoGames
