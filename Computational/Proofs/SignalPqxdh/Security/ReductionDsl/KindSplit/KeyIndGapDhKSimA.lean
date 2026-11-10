/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMisc
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMiscArms
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMiscReveal
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimRo
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimSess

/-!
# Forgetful Step Simulation for One-Key `KeyInd` `GapSigEufCma` and `GapDhWithSign`

Composes the per-query `KeyIndStepSim` obligations with initial and finalizer agreement into
`ForgetSim` packages for `sigKeyInd1KeyKindAtomicProg` and `fgKeyInd1KeyGapDhKindAtomicProg`.
-/

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimA

public section

open _root_.ReductionDsl (Ty pqAtomicSig PB)
open _root_.Computational.Proofs.ReductionDsl.StepSim (ForgetSim)
open _root_.SignalPqxdh (Setup QueryBudget)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  sigKeyInd1KeyActiveAtomicProg fgKeyInd1KeyGapDhActiveAtomicProg)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  sigKeyInd1KeyKindAtomicProg fgKeyInd1KeyGapDhKindAtomicProg)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  keyIndSimPred keyIndSimBounds)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (
  forgetSig1KeyActiveK forgetGdh1KeyActiveK Sig1KeyActiveSimInv Gdh1KeyActiveSimInv
  hHandle_of_keyIndStepSim)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMisc (
  sigKeyInd1KeyKindAtomicProg_hInit sigKeyInd1KeyKindAtomicProg_hFinish
  fgKeyInd1KeyGapDhKindAtomicProg_hInit fgKeyInd1KeyGapDhKindAtomicProg_hFinish)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMiscArms (
  sigKeyInd1KeyKindAtomicProg_hStep_initPrin sigKeyInd1KeyKindAtomicProg_hStep_genSPK
  sigKeyInd1KeyKindAtomicProg_hStep_genOPK sigKeyInd1KeyKindAtomicProg_hStep_registerKey
  fgKeyInd1KeyGapDhKindAtomicProg_hStep_initPrin fgKeyInd1KeyGapDhKindAtomicProg_hStep_genSPK
  fgKeyInd1KeyGapDhKindAtomicProg_hStep_genOPK fgKeyInd1KeyGapDhKindAtomicProg_hStep_registerKey)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMiscReveal (
  sigKeyInd1KeyKindAtomicProg_hStep_corruptIK sigKeyInd1KeyKindAtomicProg_hStep_testSession
  sigKeyInd1KeyKindAtomicProg_hStep_revealDhSecrets sigKeyInd1KeyKindAtomicProg_hStep_revealSessionKey
  sigKeyInd1KeyKindAtomicProg_hStep_revealSpkSk
  fgKeyInd1KeyGapDhKindAtomicProg_hStep_corruptIK fgKeyInd1KeyGapDhKindAtomicProg_hStep_testSession
  fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealDhSecrets fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealSessionKey
  fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealSpkSk)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimRo (
  sigKeyInd1KeyKindAtomicProg_hStep_roQuery fgKeyInd1KeyGapDhKindAtomicProg_hStep_roQuery)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimSess (
  sigKeyInd1KeyKindAtomicProg_hStep_initiateOPK sigKeyInd1KeyKindAtomicProg_hStep_initiateNoOPK
  sigKeyInd1KeyKindAtomicProg_hStep_acceptOPK sigKeyInd1KeyKindAtomicProg_hStep_acceptNoOPK
  fgKeyInd1KeyGapDhKindAtomicProg_hStep_initiateOPK fgKeyInd1KeyGapDhKindAtomicProg_hStep_initiateNoOPK
  fgKeyInd1KeyGapDhKindAtomicProg_hStep_acceptOPK fgKeyInd1KeyGapDhKindAtomicProg_hStep_acceptNoOPK)

/-- Forgetful step-simulation package from `sigKeyInd1KeyKindAtomicProg` to
    `sigKeyInd1KeyActiveAtomicProg` under `keyIndSimPred` / `keyIndSimBounds`. -/
theorem sigKeyInd1KeyKindAtomicProg_forgetSim (S : Setup) (b : QueryBudget) (pk : (PB 32).denote) :
    ForgetSim (sigKeyInd1KeyKindAtomicProg S b) (sigKeyInd1KeyActiveAtomicProg S b)
      (forgetSig1KeyActiveK S b) (keyIndSimPred S) (keyIndSimBounds b) pk
      (Sig1KeyActiveSimInv S b) where
  hInit := sigKeyInd1KeyKindAtomicProg_hInit S b pk
  hHandle := hHandle_of_keyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
    (sigKeyInd1KeyKindAtomicProg S b).handle (sigKeyInd1KeyActiveAtomicProg S b).handle
    (sigKeyInd1KeyKindAtomicProg_hStep_initPrin S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_corruptIK S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_genSPK S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_genOPK S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_initiateOPK S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_initiateNoOPK S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_acceptOPK S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_acceptNoOPK S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_testSession S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_roQuery S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_revealDhSecrets S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_revealSessionKey S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_registerKey S b)
    (sigKeyInd1KeyKindAtomicProg_hStep_revealSpkSk S b)
  hFinish := sigKeyInd1KeyKindAtomicProg_hFinish S b

/-- Forgetful step-simulation package from `fgKeyInd1KeyGapDhKindAtomicProg` to
    `fgKeyInd1KeyGapDhActiveAtomicProg` under `keyIndSimPred` / `keyIndSimBounds`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_forgetSim (S : Setup) (b : QueryBudget)
    (uv : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote) :
    ForgetSim (fgKeyInd1KeyGapDhKindAtomicProg S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b)
      (forgetGdh1KeyActiveK S b) (keyIndSimPred S) (keyIndSimBounds b) uv
      (Gdh1KeyActiveSimInv S b) where
  hInit := fgKeyInd1KeyGapDhKindAtomicProg_hInit S b uv
  hHandle := hHandle_of_keyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
    (fgKeyInd1KeyGapDhKindAtomicProg S b).handle (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_initPrin S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_corruptIK S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_genSPK S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_genOPK S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_initiateOPK S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_initiateNoOPK S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_acceptOPK S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_acceptNoOPK S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_testSession S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_roQuery S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealDhSecrets S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealSessionKey S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_registerKey S b)
    (fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealSpkSk S b)
  hFinish := fgKeyInd1KeyGapDhKindAtomicProg_hFinish S b

end

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimA
