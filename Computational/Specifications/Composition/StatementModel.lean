/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.ModelIface
public import Computational.Specifications.Assumptions.KeyInd1KeyReal

/-!
# Multi-session model composition with costed reductions (Lemma 3, `L3`)

**Trusted: the statement.** Read with `Computational/Specifications/Game/ModelIface.lean`
(`modelIface` and `KeyIndAdvantageForHandshake`),
`Computational/Specifications/Assumptions/KeyInd1KeyReal.lean` (`pqxdhKeyIndImpl1KeyReal`), and
`Computational/Specifications/Reductions/Pqxdh/StatementPqReds.lean`
(`CompositionCostedReductions`, `CompositionCostedReductionFamily`, and
`CompositionCostedReductionFamilyBounded`). See `Computational/docs/TRUSTED_BASE.md`.

`ModelSecure S ℓ` states Lemma 3 (label `L3`, proved as `model_secure_costed` in
`Computational/Theorems/Lemmas.lean`) for the one-key real-HKDF handshake
`ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`. It asserts a budget-indexed family of
`ReductionDsl` reductions `reds : CompositionCostedReductionFamily S ℓ P C K qep decT encT`
(`kindRed` against `ki` and two-stage `prefixRed k` against single-session `SM.gameR`) whose
syntactic step-cost, query, and block-size bounds `CompositionCostedReductionFamilyBounded` hold
unconditionally in `P`.

Under `SignalPqxdh.WellFormedPrimitivesδ P` (which supplies the byte-length laws for fixed-width
`ReductionDsl` handshake simulation) and `ModelAdversaryPerInstanceBounded A b qStart qs`,
instantiating `R_e2e := reds b qStart qDR qInst` yields a `KeyInd` adversary `advK` within
`keyIndReductionBudget S qStart b`, stage-2 adversaries making at most `qs k` queries, and
`ComposedAdvantage (modelIface … ki …) A ≤
  2 · KeyIndAdvantageForHandshake S P ki advK + ∑ k < qStart, ⨆ flip, …`,
where each summand is the single-session `SM.gameR` bias of `(R_e2e.prefixRed k).eval2` mixed over
stage 1. Because composition stops at single-session `SM.gameR`, no single-session primitive or
message-counter assumptions appear here.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open OracleComp OracleSpec MeasureTheory ENNReal
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

namespace CryptoVerification.E2E

/-- Whether a `composedSpec` query targets secure-messaging instance `k`. -/
def composedIsInstQuery {S : SignalPqxdh.Setup} {ℓ : ℕ} {St : Type} (k : ℕ) :
    (composedSpec S ℓ St).Domain → Bool
  | .inr ⟨i, _⟩ => i == k
  | _ => false

/-- Query bounds for an adversary `A` of `G(Σ_model)`: bounds random-oracle, initiator, responder,
total `KeyInd`, non-RO `KeyInd`, `startDR` (`≤ S.N_send_tot` and `≤ qStart`), per-instance ratchet
(`≤ qs k` for `k < qStart`), and total ratchet (`≤ ∑ k < qStart, qs k`) queries. -/
def ModelAdversaryPerInstanceBounded {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) : Prop :=
  A.IsQueryBoundP (fun q => q matches .inl (.inl (.inr (.roQuery _)))) b.q_ro ∧
  A.IsQueryBoundP (fun q => q matches .inl (.inl (.inr (.initiateOPK ..)))
      || q matches .inl (.inl (.inr (.initiateNoOPK ..)))) S.N_send_tot ∧
  A.IsQueryBoundP (fun q => q matches .inl (.inl (.inr (.acceptOPK ..)))
      || q matches .inl (.inl (.inr (.acceptNoOPK ..)))) S.N_recv_tot ∧
  A.IsQueryBoundP (fun q => q matches .inl (.inl (.inr _))) b.q_total ∧
  A.IsQueryBoundP (fun q => q matches .inl (.inl (.inr _))
      && !(q matches .inl (.inl (.inr (.roQuery _))))) b.q_on ∧
  A.IsQueryBoundP (fun q => q matches .inl (.inr _)) S.N_send_tot ∧
  A.IsQueryBoundP (fun q => q matches .inr _) (∑ k ∈ Finset.range qStart, qs k) ∧
  A.IsQueryBoundP (fun q => q matches .inl (.inr _)) qStart ∧
  ∀ k < qStart, A.IsQueryBoundP (fun q => composedIsInstQuery k q) (qs k)

/-- Multi-session model composition (Lemma 3, `L3`) with costed reductions over
`ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`: bounds `ComposedAdvantage` in `G(Σ_model^ki)` by
twice the `KeyInd` advantage against `ki` plus the sum over promoted sessions `k < qStart` of the
worst-`flip` single-session `SM.gameR` bias mixed over stage 1 of `prefixRed k`. -/
def ModelSecure {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  ∀ (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
  let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
  ∃ reds : CompositionCostedReductionFamily S ℓ P C K qep decT encT,
    CompositionCostedReductionFamilyBounded P C K qep decT encT reds ∧
    ∀ (_hP : SignalPqxdh.WellFormedPrimitivesδ P)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool)
      (_hA : ModelAdversaryPerInstanceBounded A b qStart qs),
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qInst := Finset.sup (Finset.range qStart) qs
      let qTot := b.q_total + qStart + qDR
      let R_e2e := reds b qStart qDR qInst
      let B_A := modelAdvRun A
      let advK : SignalPqxdh.KeyIndAdversary S := ⟨R_e2e.kindRed.eval (fun _ => B_A) ()⟩
      SignalPqxdh.QueryBounded advK (keyIndReductionBudget S qStart b) ∧
      (∀ k < qStart,
        ∀ o ∈ support (stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
        ∀ flip,
        SM.MakesAtMostQueries ((R_e2e.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
      ComposedAdvantage (modelIface (ℓ := ℓ) P ki C K qep decT encT) A ≤
        2 * KeyIndAdvantageForHandshake S P ki advK +
          ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
            𝒟[stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
              fun o =>
                SM.gameR
                  (sessionSchemeFixedSpk
                    (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
                    ℓ o.1.2.2)
                  3 qep (configRefuseEarlyBobCorr decT encT)
                  ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)].boolBias

end CryptoVerification.E2E
