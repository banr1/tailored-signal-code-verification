/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqAdapterCoupling
import Computational.Proofs.LibsignalCli.CliPqAdapterSmBobSim
import Computational.Proofs.LibsignalCli.CliPqAdapterSmSendCorrA

/-!
# Per-instance SM oracle step coupling

**Checked by Lean.** Proves `CliSmStepBridgeProp` by combining the SM oracle step couplings from
`CliPqAdapterSmSendCorrA` and `CliPqAdapterSmBobSim`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

set_option linter.unusedVariables false in
/-- Discharges `CliSmStepBridgeProp` across all SM oracle constructors. -/
theorem cliSmStepBridgeProp_holds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hCli : CliSpecPqxdh run X W) (hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x) :
    CliSmStepBridgeProp S ℓ run X W qep decT encT := by
  intro b qStart qs_rem st_cli ds_cli σ_ad σ_e2e hRel hRem hGood i q hq_pos
  let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W)
  have hRemDrv : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e :=
    cliAdapterDrvRemoteIdInv_of_cliE2ERemoteIdInv hRem
  have hUpd : ∀ k, Function.update qs_rem i (qs_rem i - 1) k ≤
      (if k = i then qs_rem k - 1 else qs_rem k) := by
    intro k
    by_cases hk : k = i <;> simp [Function.update, hk]
  by_cases hi : i < ds_cli.bhInsts.length
  · rcases q with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
    · exact cliDrvSM_adapter_coupling_tr run X W qep decT encT bhNoExtWithSpqr ki
        hCli hℓ hRel hRemDrv i p m r (hq_pos hi)
    · exact cliDrvSM_adapter_coupling_ch run X W qep decT encT bhNoExtWithSpqr ki
        hCli hℓ hRel hRemDrv i p m0 m1 r (hq_pos hi)
    · cases p with
      | A =>
        exact cliDrvSM_adapter_coupling_dl_A run X W qep decT encT bhNoExtWithSpqr ki
          hCli hRel hRemDrv i c hq_pos
      | B =>
        exact (cliDrvSM_bob_dl_coupled run X W hCli ki qep decT encT bhNoExtWithSpqr
          hRel hRem hGood i c hq_pos).mono_qs_rem hUpd
    · cases p with
      | A =>
        exact cliDrvSM_adapter_coupling_ij_A run X W qep decT encT bhNoExtWithSpqr ki
          hCli hRel hRemDrv i c hq_pos
      | B =>
        exact (cliDrvSM_bob_ij_coupled run X W hCli ki qep decT encT bhNoExtWithSpqr
          hRel hRem i c hq_pos).mono_qs_rem hUpd
    · exact cliDrvSM_adapter_coupling_cr run X W qep decT encT bhNoExtWithSpqr ki hRel i p
  · exact cliDrvSM_adapter_coupling_oob run X W qep decT encT bhNoExtWithSpqr ki
      hRel i q (Nat.le_of_not_lt hi)

end CryptoVerification.E2E
