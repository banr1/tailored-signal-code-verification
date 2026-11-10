/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.BinaryHarnessCostedRedsHonest

/-!
# Multi-Session Composition Statement Contracts over `M3SubprogramsIface`

Instantiates `M4KindRedSpec`, `M4PrefixRedSpec`, `M4CompositionBundleSpec`,
`M4CompositionFamilySpec`, and `ModelSecureHonestFamilyStmt` from `kindRedHonest` and
`prefixRedHonest` given step-cost and size bounds against `bhE2ECostBudgetHonest`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Computational.Proofs.E2E.Dsl.KeyInd1RealRedsHonest

open ReductionDsl (bits reductionSizeBudget)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open Computational.Proofs.E2E.Dsl.M3Interfaces (M3SubprogramsIface M3SubprogramsSizeIface)
open Computational.Proofs.E2E.Dsl.M4ReductionsIface (bhE2ECostBudgetHonest
  M4KindRedSpec M4PrefixRedSpec M4CompositionBundleSpec M4CompositionFamilySpec
  ModelSecureHonestFamilyStmt modelSecureHonestFamily_of_spec)
open Computational.Proofs.E2E.Dsl.PrefixRedsHonest (prefixRedHonest_totalQueries₁
  prefixRedHonest_totalQueries₂_le prefixRedHonest_makesAtMostQueries_of_target
  evalDist_gameR_prefixRedHonest_eq)
open Computational.Proofs.E2E.Dsl.BinaryHarnessCostedRedsHonest (kindRedHonest prefixRedHonest
  compositionRedsHonest compositionFamilyHonest m3LeafCostBound m3LeafSizeBound
  M3SubprogramsCostBoundedAt M3SubprogramsBundleCostBounded M3SubprogramsCostBounded
  kindRedHonest_totalQueries_le kindRedHonest_queryBounded_of_target
  evalDist_pqxdhKeyIndExp_kindRedHonest_eq)

export Computational.Proofs.E2E.Dsl.BinaryHarnessCostedRedsHonest (kindRedHonest prefixRedHonest
  compositionRedsHonest compositionFamilyHonest)

section Specs

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

theorem m4KindRedSpec_honest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hCost :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      (kindRedHonest subs b qStart qDR qep).totalCost qTot ≤
        bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      (kindRedHonest subs b qStart qDR qep).size ≤
        reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ)) :
    M4KindRedSpec P C K qep decT encT b qStart qs
      (kindRedHonest subs b qStart (∑ k ∈ Finset.range qStart, qs k) qep) :=
  M4KindRedSpec.of_keyIndExp_evalDist_eq
    (kindRedHonest subs b qStart (∑ k ∈ Finset.range qStart, qs k) qep)
    hCost
    hSize
    (kindRedHonest_totalQueries_le subs b qStart (∑ k ∈ Finset.range qStart, qs k) qep _)
    (fun B_A hB =>
      kindRedHonest_queryBounded_of_target subs b qStart qs
        (∑ k ∈ Finset.range qStart, qs k) qep B_A hB)
    (fun hP B_A hB =>
      evalDist_pqxdhKeyIndExp_kindRedHonest_eq subs b qStart qs qep
        (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) hP B_A hB)

theorem m4PrefixRedSpec_honest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hCost :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      ∀ k < qStart,
        (prefixRedHonest subs b qStart qDR qep k).totalCost qTot ≤
          bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      ∀ k < qStart,
        (prefixRedHonest subs b qStart qDR qep k).size ≤
          reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ)) :
    M4PrefixRedSpec P C K qep decT encT b qStart qs
      (prefixRedHonest subs b qStart (∑ k ∈ Finset.range qStart, qs k) qep) :=
  M4PrefixRedSpec.of_gameR_evalDist_eq
    (prefixRedHonest subs b qStart (∑ k ∈ Finset.range qStart, qs k) qep)
    hCost
    hSize
    (fun k _ =>
      prefixRedHonest_totalQueries₁ subs b qStart (∑ j ∈ Finset.range qStart, qs j) qep k)
    (fun k _ =>
      prefixRedHonest_totalQueries₂_le subs b qStart (∑ j ∈ Finset.range qStart, qs j) qep k _)
    (fun B_A hB =>
      prefixRedHonest_makesAtMostQueries_of_target subs b qStart qs qep B_A hB)
    (fun hP B_A hB =>
      evalDist_gameR_prefixRedHonest_eq subs b qStart qs qep hP B_A hB)

theorem m4CompositionBundleSpec_honest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hCost : M3SubprogramsBundleCostBounded b qStart
      (∑ k ∈ Finset.range qStart, qs k) qep subs) :
    M4CompositionBundleSpec P C K qep decT encT b qStart qs
      (compositionRedsHonest (qep := qep) subs b qStart
        (∑ k ∈ Finset.range qStart, qs k)) :=
  ⟨m4KindRedSpec_honest subs b qStart qs hCost.kindCost_le hCost.kindSize_le,
   m4PrefixRedSpec_honest subs b qStart qs hCost.prefixCost_le hCost.prefixSize_le⟩

theorem m4CompositionBundleSpec_of_leafCostBound (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hLeaf :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      m3LeafCostBound subs b qStart qDR qep qTot ≤
        bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      m3LeafSizeBound sz b qStart qDR qep ≤
        reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ)) :
    M4CompositionBundleSpec P C K qep decT encT b qStart qs
      (compositionRedsHonest (qep := qep) subs b qStart
        (∑ k ∈ Finset.range qStart, qs k)) :=
  m4CompositionBundleSpec_honest subs b qStart qs
    (M3SubprogramsCostBoundedAt.of_leafCostBound sz hLeaf hSize)

theorem m4CompositionFamilySpec_honest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (hCost : M3SubprogramsCostBounded qep subs) :
    M4CompositionFamilySpec P C K qep decT encT
      (compositionFamilyHonest (qep := qep) subs) :=
  fun b qStart qs =>
    m4CompositionBundleSpec_honest subs b qStart qs
      (hCost b qStart (∑ k ∈ Finset.range qStart, qs k))

theorem m4CompositionFamilySpec_of_leafCostBound (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (sz : M3SubprogramsSizeIface subs)
    (hLeaf : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
      m3LeafCostBound subs b qStart qDR qep (b.q_total + qStart + qDR) ≤
        bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hSize : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
      m3LeafSizeBound sz b qStart qDR qep ≤
        reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ)) :
    M4CompositionFamilySpec P C K qep decT encT
      (compositionFamilyHonest (qep := qep) subs) :=
  m4CompositionFamilySpec_honest subs
    (fun b qStart qDR => M3SubprogramsCostBoundedAt.of_leafCostBound sz
      (hLeaf b qStart qDR) (hSize b qStart qDR))

end Specs

theorem modelSecureHonestFamily_of_m3 {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (mkSubs : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
      M3SubprogramsIface ℓ S P C K decT encT)
    (hCost : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
      M3SubprogramsCostBounded qep (mkSubs P C K decT encT)) :
    ModelSecureHonestFamilyStmt (Pt := Pt) S ℓ :=
  modelSecureHonestFamily_of_spec (Pt := Pt) S ℓ fun P C K qep decT encT =>
    ⟨compositionFamilyHonest (qep := qep) (mkSubs P C K decT encT),
     m4CompositionFamilySpec_honest (mkSubs P C K decT encT) (hCost P C K qep decT encT)⟩

/-- Establishes `ModelSecureHonestFamilyStmt` from a parametric `M3SubprogramsIface` constructor bounded by `bhE2ECostBudgetHonest`. -/
theorem modelSecureHonestFamily_of_m3_leaf {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (mkSubs : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
      M3SubprogramsIface ℓ S P C K decT encT)
    (mkSz : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
      M3SubprogramsSizeIface (mkSubs P C K decT encT))
    (hLeaf : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
      (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
      m3LeafCostBound (mkSubs P C K decT encT) b qStart qDR qep (b.q_total + qStart + qDR) ≤
        bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hSize : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
      (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
      m3LeafSizeBound (mkSz P C K decT encT) b qStart qDR qep ≤
        reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ)) :
    ModelSecureHonestFamilyStmt (Pt := Pt) S ℓ :=
  modelSecureHonestFamily_of_m3 (Pt := Pt) S ℓ mkSubs
    (fun P C K qep decT encT b qStart qDR =>
      M3SubprogramsCostBoundedAt.of_leafCostBound (mkSz P C K decT encT)
        (hLeaf P C K qep decT encT b qStart qDR) (hSize P C K qep decT encT b qStart qDR))

end Computational.Proofs.E2E.Dsl.KeyInd1RealRedsHonest
