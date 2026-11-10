/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.HeadlinePqCliMixEq
public import Computational.Proofs.LibsignalCli.StatementPqSecure
import Computational.Proofs.LibsignalCli.MainHaltedGame
import Computational.Proofs.LibsignalCli.MainOfLemmas
import Computational.Proofs.LibsignalCli.Oom.Transfer

/-!
# CLI security on PQXDH directories with SPQR from bridge premises

Proves `LibsignalCliPqSecure S ℓ` from `PqxdhKeyIndSecureδ S` and `cliHaltedBoundProp_holds` via
the halted-game `KemFailBad` transfer `cliPqAdvantage_le_add_kemFail`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open scoped ENNReal
open Computational.Proofs.LibsignalCli.Oom.Transfer (cliPqAdvantage_le_add_kemFail)

/-- `LibsignalCliPqSecure S ℓ` from `CliPqAdapterBoundProp S ℓ` and `PqxdhKeyIndSecureδ S`. -/
theorem libsignalCliPqSecure_of_bridges
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (_hAdapter : CliPqAdapterBoundProp (Pt := Pt) S ℓ)
    (hKi : SignalPqxdh.Security.PqxdhKeyIndSecureδ S) :
    LibsignalCliPqSecure (Pt := Pt) S ℓ := by
  rcases hKi with ⟨RK, hCostRK, hSimRK, hKiBound⟩
  rcases Computational.Proofs.LibsignalCli.MainHaltedGame.cliHaltedBoundProp_holds (Pt := Pt) S ℓ with
    ⟨L_cli, D, reds, ⟨hSlotD, hBounds⟩, hMainH⟩
  refine ⟨L_cli, RK, D, reds, hCostRK, hSimRK, hSlotD, hBounds, ?_⟩
  intro run X W hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec
    hdum hz hD hkerAll b qStart qs hq32 δ hδ A hA P qDR qInst qTot B_A Re b_ki advK
  obtain ⟨hK, hQueries, ⟨exp_H, δ_extra, hPtwise, hBiasH⟩⟩ :=
    hMainH run X W hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ hDh hX hdec
      hdum hz hD hkerAll b qStart qs hq32 δ hδ A hA
  refine ⟨hK, hQueries, ?_⟩
  intro prefixSum
  have hTrans :=
    cliPqAdvantage_le_add_kemFail S run X W ℓ qep decT encT A exp_H δ_extra hPtwise
  have hClause1 :
      CliPqxdhAdvantage S run X W ℓ qep decT encT A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P advK + prefixSum +
          SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
          2 * CliKemFailProb S run X W ℓ qep decT encT A :=
    hTrans.trans (add_le_add hBiasH le_rfl)
  refine ⟨hClause1, fun ε_ro hRo => hClause1.trans ?_⟩
  have hGapLe :
      SignalPqxdh.KeyInd1KeyRealAdvantage S P advK ≤
        (let R := RK.eval
         let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
         SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on δ_kem
           (SignalPqxdh.GapSigEufCma P P.isValidDhTriple (R.sig _ Ab))
           (SignalPqxdh.KemShCr P (R.shcr _ Ab))
           (SignalPqxdh.GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh _ Ab)) + ε_ro) :=
    le_trans hRo (add_le_add (hKiBound P hP δ_kem hKemBin b_ki ⟨advK, hK⟩) le_rfl)
  dsimp only [withExcusedAbortTerm]
  gcongr

end CryptoVerification.E2E
