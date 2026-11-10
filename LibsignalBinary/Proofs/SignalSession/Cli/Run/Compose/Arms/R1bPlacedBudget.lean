/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Arm `R1b` Specification

Defines budget-threaded `RunHopInit2Placed` and `RunHopInit2PlacedOf` (`R+0x074c → R+0x28f0`) on
Block `579` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtInit1Placed AtInit2Placed AtRunEntryPlaced Init1Data Init2Data PanicK RunNeeds RunSem
   runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runNeed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (init1MemPlaced init2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)

/-- Budget-threaded relocatable Arm `R1b` contract from `AtInit1Placed` (`R+0x074c`) under `FitsEnv M lim st (Init2Env g d1)` to `AtInit2Placed` (`R+0x28f0`) or `RejectKPlacedEnv` / `PanicK`. -/
def RunHopInit2Placed [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (Init2Env : RunCall → Init1Data → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {d1 : Init1Data} {s0 s1 : State} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtInit1Placed CodeOk g d1 s0 s1 →
    FitsEnv M lim st (Init2Env g d1) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init2Env g d1 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2Placed CodeOk g d2 s0 s2 →
      Init2Env g d1 evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs st) g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      (init1MemPlaced A lim st g d1 s0 s1 resStack) Q Qp
      (fun _ => ⌜False⌝)


def RunHopInit2PlacedOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (Init2Env : RunCall → Init1Data → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {d1 : Init1Data} {s0 s1 : State} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlaced A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtInit1Placed CodeOk g d1 s0 s1 →
    FitsEnv M lim st (Init2Env g d1) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init2Env g d1 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2Placed CodeOk g d2 s0 s2 →
      Init2Env g d1 evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs st) g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      (init1MemPlaced A lim st g d1 s0 s1 resStack) Q Qp
      (fun _ => ⌜False⌝)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget
