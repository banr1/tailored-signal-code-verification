/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Arm `R0` Specification

Defines budget-threaded `RunHopPrePlaced` and `RunHopPrePlacedOf` (`R+0x0 → R+0x214`) on Block `579`
under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtRunEntryPlaced MeAtDispatch PanicK RunNeeds RunSem runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runNeed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (dispatchMemPlaced runEntryMemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)

/-- Budget-threaded relocatable Arm `R0` contract from `AtRunEntryPlaced` (`R+0x0`) under `FitsEnv M lim st (PreEnv g)` to `AtDispatchPlaced` (`R+0x214`) or `RejectKPlacedEnv` / `PanicK`. -/
def RunHopPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (PreEnv : RunCall → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 : State} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    FitsEnv M lim st (PreEnv g) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, PreEnv g evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ s (evs : List AllocEvent) (me : MeAtDispatch),
      AtDispatchPlaced CodeOk g me s0 s →
      PreEnv g evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
        (dispatchMemPlaced A lim (M.stepEvents evs st) g me s0 s resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s0
      (runEntryMemPlaced A lim st g s0 resStack) Q Qp
      (fun _ => ⌜False⌝)


def RunHopPrePlacedOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (PreEnv : RunCall → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 : State} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlaced A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    FitsEnv M lim st (PreEnv g) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, PreEnv g evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ s (evs : List AllocEvent) (me : MeAtDispatch),
      AtDispatchPlaced CodeOk g me s0 s →
      PreEnv g evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
        (dispatchMemPlaced A lim (M.stepEvents evs st) g me s0 s resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s0
      (runEntryMemPlaced A lim st g s0 resStack) Q Qp
      (fun _ => ⌜False⌝)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget
