/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `signal_session::run` Arm `R1c`: `Init` Sub-Hop 3 Contract

Budget-threaded (`RustCliAllocBudget M`) hop contracts `RunHopInit3Placed` and `RunHopInit3PlacedOf`
for Arm `R1c` (`R+0x28f0` → Join/Reject) on Block `579` (`signal_session::run`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtInit2Placed AtRunEntryPlaced Init2Data PanicK RunNeeds RunSem runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runNeed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (init2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)

/-- Budget-threaded relocatable (`[LibsignalPlacement]`) Arm R1c hop contract (`run_hop_init3_ok`):
from `AtInit2Placed` (`R+0x28f0`) at cost-model state `st` under `FitsEnv M lim st (Init3Env g d2)`,
calls `wrap_initiate` and drops the bundle to reach `JoinKPlacedEnv` or `RejectKPlacedEnv` with
`Qo = ⌜False⌝`. -/
def RunHopInit3Placed [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (Init3Env : RunCall → Init2Data → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s2 : State} {d2 : Init2Data} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtInit2Placed CodeOk g d2 s0 s2 →
    FitsEnv M lim st (Init3Env g d2) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init3Env g d2 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init3Env g d2 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
      (init2MemPlaced A lim st g d2 s0 s2 resStack) Q Qp
      (fun _ => ⌜False⌝)


def RunHopInit3PlacedOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (Init3Env : RunCall → Init2Data → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s2 : State} {d2 : Init2Data} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlaced A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtInit2Placed CodeOk g d2 s0 s2 →
    FitsEnv M lim st (Init3Env g d2) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init3Env g d2 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init3Env g d2 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
      (init2MemPlaced A lim st g d2 s0 s2 resStack) Q Qp
      (fun _ => ⌜False⌝)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget
