/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.LibsignalCli.MainOfLemmas
public import Computational.Proofs.LibsignalCli.MainHaltedDefs
import Computational.Proofs.LibsignalCli.MainHaltedAdapterBound
import Computational.Proofs.LibsignalCli.MainHaltedSessBound
import Computational.Proofs.LibsignalCli.MainHaltedCompBound
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Measure

/-!
# Halted-Game Composition for `CliPqxdhSecurityFor`

Combines the halted CLI-to-model adapter coupling (`MainHaltedAdapterBound`), halted single-session
bound (`MainHaltedSessBound`), and halted multi-session composition bound (`MainHaltedCompBound`)
to establish `CliHaltedBoundProp`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.MainHaltedGame

open scoped ENNReal BigOperators
open OracleComp OracleSpec
open CryptoVerification.LibsignalSpqrV1 (spqrV1SessionUniformCoins)
open CryptoVerification.E2E (bhPrefixFullBoundMixV1With cliGameAdversaryReassoc
  configRefuseEarlyBobCorr modelPrims paramsIdsWithSpqr sessionSchemeFixedSpk stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (gameRSessionTracked)
open Computational.Proofs.LibsignalCli.MainHaltedDefs (TargetAdvPerInstanceBounded
  kemFailCoreTracker)
open Computational.Proofs.LibsignalCli.MainHaltedAdapterBound (exists_cliHaltedAdapterCoupling)
open Computational.Proofs.LibsignalCli.MainHaltedSessBound (exists_haltedSessionBound)
open Computational.Proofs.LibsignalCli.MainHaltedCompBound (exists_haltedCompositionRedsBound)
open Computational.Proofs.LibsignalCli.MainOfLemmas (CliHaltedBoundProp)

section TopSpine

/-- Proves `CliHaltedBoundProp` for `MainOfLemmas` by combining the halted adapter, session, and
multi-session composition bounds. -/
theorem cliHaltedBoundProp_holds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    CliHaltedBoundProp (Pt := Pt) S ℓ := by
  obtain ⟨L_cli, hL_cost, hL_qb, hCoupl⟩ := exists_cliHaltedAdapterCoupling (Pt := Pt) S ℓ
  obtain ⟨D, hD_cost, hSess⟩ := exists_haltedSessionBound (Pt := Pt) S ℓ
  obtain ⟨reds, hReds_cost, hComp⟩ := exists_haltedCompositionRedsBound (Pt := Pt) S ℓ
  refine ⟨L_cli, D, reds, ⟨hD_cost, hL_cost, hReds_cost⟩, ?_⟩
  intro run X Wp hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec
    hdum hz hD hkerAll b qStart qs hq32 δ hδ A hA
  let B_A := (L_cli decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
  have hB_qb : TargetAdvPerInstanceBounded B_A b qStart qs := hL_qb decT encT A b qStart qs hA
  obtain ⟨δ_extra, hδ_le, hPtwise⟩ := hCoupl run X Wp hCli hK_tot hP δ_kem hKemBin
    Dh encPt encT decT qep hℓ hDh hX hdec hdum hz hD b qStart qs hq32 A hA
  obtain ⟨hQ_ki, hQ_sm, hTel⟩ := hComp X Wp hK_tot hP Dh encPt encT decT qep hℓ
    hDh hX hdec hdum hz hD b qStart qs B_A hB_qb
  have hSum_le :
      (∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
        𝒟[stageOneAsProbComp
            (((reds (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT b qStart
                (∑ k ∈ Finset.range qStart, qs k)
                (Finset.sup (Finset.range qStart) qs)).prefixRed k).eval1 (fun _ => B_A) ()
              (b.q_total + qStart + ∑ k ∈ Finset.range qStart, qs k) false) >>=
          fun o =>
            Prod.fst <$> gameRSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K)
              (sessionSchemeFixedSpk
                (paramsIdsWithSpqr Wp.C (spqrV1SessionUniformCoins Wp.C.F Wp.Q.K) o.1.1 o.1.2.1)
                ℓ o.1.2.2)
              (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
              (((reds (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT b qStart
                  (∑ k ∈ Finset.range qStart, qs k)
                  (Finset.sup (Finset.range qStart) qs)).prefixRed k).eval2 o.2 flip
                (b.q_total + qStart + ∑ k ∈ Finset.range qStart, qs k) false)].boolBias) ≤
      ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
        bhPrefixFullBoundMixV1With S (modelPrims X Wp) ℓ D Wp.C Wp.Q.K
          Dh encPt encT decT qep
          (b.q_total + qStart + ∑ k ∈ Finset.range qStart, qs k) (qs k) δ k flip
          (reds (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT b qStart
            (∑ k ∈ Finset.range qStart, qs k) (Finset.sup (Finset.range qStart) qs)) B_A := by
    refine Finset.sum_le_sum fun k hk => iSup_mono fun flip => ?_
    have hk_lt : k < qStart := Finset.mem_range.mp hk
    exact hSess X Wp hK_tot Dh encPt encT decT qep hℓ hDh hX hdec hdum hz hD hkerAll δ hδ
      _ B_A _ (qs k) (hq32 k hk_lt) k flip (fun o ho => hQ_sm k hk_lt o ho flip)
  refine ⟨hQ_ki, hQ_sm, ⟨_, δ_extra, hPtwise, ?_⟩⟩
  exact add_le_add (hTel.trans (add_le_add le_rfl hSum_le)) hδ_le

end TopSpine

end Computational.Proofs.LibsignalCli.MainHaltedGame
