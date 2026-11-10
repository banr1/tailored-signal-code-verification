/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPqOomGame
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
public import Computational.Specifications.Assumptions.KeyInd1KeyReal
public import Computational.Proofs.LibsignalCli.StatementPqSecure
public import Computational.Proofs.LibsignalCli.CliPqAdapterDefs
public import Computational.Proofs.LibsignalCli.CliPqBadKemBound
public import Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Measure
import Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBAux
import Computational.Proofs.LibsignalCli.CliPqKeyIndStep
import Computational.Proofs.LibsignalCli.CliPqStartStep
import Computational.Proofs.LibsignalCli.CliPqAdapterSmStep

/-!
# Send-coin-logged CLI to E2E model coupling

Bounds the good-log outcome probability in `cliPqExpProjCoinLogged` by the corresponding outcome
probability in `cliE2EExpWithKiCoinLogged` plus `cliRunBadKemExp`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.CliKemFailCouplingHopB

open OracleComp
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh dummyKey)
open CryptoVerification.LibsignalSpqrV1 (coinBytes)
open CryptoVerification.SignalSession (CliRun CliSpecPqxdh)
open CryptoVerification.E2E (Bytes CliGameAdversary CliGameAdversaryPerInstanceBounded L_bh
  MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds PEParams UnreachedPqxdhPrimitives
  cliGameAdversaryReassoc cliKeyIndStepBridgeProp_holds cliRunBadKemExp
  cliSmStepBridgeProp_holds cliStartStepBridgeProp_holds modelPrims)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs (cliE2EExpWithKiCoinLogged
  cliPqExpProjCoinLogged)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingHopBAux (
  cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged_of_step_bridges_pr)

/-- Bounds the good-log probability in `cliPqExpProjCoinLogged` by that in
`cliE2EExpWithKiCoinLogged true` plus the `cliRunBadKemExp` probability. -/
theorem cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hCli : CliSpecPqxdh run X W)
    (hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs)
    (val : Bool) :
    let P := modelPrims X W
    let B_Lbh := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()
    Pr{let w ← cliPqExpProjCoinLogged S run X W ℓ qep decT encT A}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] ≤
      Pr{let w ← cliE2EExpWithKiCoinLogged true S P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep decT encT B_Lbh}[
        w.1 = val ∧ ¬ (W.Q.K.KemFailBad (w.2.map coinBytes) = true)] +
      𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} := by
  have hinj : Function.Injective encT := fun x y hxy =>
    Option.some.inj (by rw [← hdec x, ← hdec y, hxy])
  exact cliPqExpProjCoinLogged_good_val_le_e2eCoinLogged_of_step_bridges_pr
    run X W qep decT encT hCli hℓ
    (cliKeyIndStepBridgeProp_holds S ℓ X W hK_tot hP qep decT encT)
    (cliStartStepBridgeProp_holds S ℓ run X W hCli hK_tot hP Dh encPt encT decT qep hℓ
      hDh hX hdec hinj hdum hz hD)
    (cliSmStepBridgeProp_holds S ℓ run X W hCli hK_tot hP Dh encPt encT decT qep hℓ
      hDh hX hdec hinj hdum hz hD)
    b_bud qStart qs A hA val

end Computational.Proofs.LibsignalCli.CliKemFailCouplingHopB
