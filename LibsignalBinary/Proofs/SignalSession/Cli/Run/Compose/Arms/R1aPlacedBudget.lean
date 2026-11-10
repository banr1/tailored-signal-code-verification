/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Arm `R1a` Specification

Defines budget-threaded `RunHopInit1Placed` and `RunHopInit1PlacedOf` (`R+0x214 → R+0x74c`) on
Block `579` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtInit1Placed AtRunEntryPlaced Init1Data MeAtDispatch PanicK RunNeeds RunSem
   runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runNeed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (dispatchMemPlaced init1MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)

/-- Budget-threaded relocatable Arm `R1a` contract from `AtDispatchPlaced` (`R+0x214`) under `FitsEnv M lim st (Init1Env g me peerV dir)` to `AtInit1Placed` (`R+0x74c`) or `RejectKPlacedEnv` / `PanicK`. -/
def RunHopInit1Placed [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (Init1Env : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {dir : List (BitVec 8)} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlaced CodeOk g me s0 s →
    g.c = .init peerV dir →
    FitsEnv M lim st (Init1Env g me peerV dir) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init1Env g me peerV dir evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ s1 (evs : List AllocEvent) (d1 : Init1Data),
      AtInit1Placed CodeOk g d1 s0 s1 →
      Init1Env g me peerV dir evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (init1MemPlaced A lim (M.stepEvents evs st) g d1 s0 s1 resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)


def RunHopInit1PlacedOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (Init1Env : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {dir : List (BitVec 8)} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlaced A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlaced CodeOk g me s0 s →
    g.c = .init peerV dir →
    FitsEnv M lim st (Init1Env g me peerV dir) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init1Env g me peerV dir evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ s1 (evs : List AllocEvent) (d1 : Init1Data),
      AtInit1Placed CodeOk g d1 s0 s1 →
      Init1Env g me peerV dir evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (init1MemPlaced A lim (M.stepEvents evs st) g d1 s0 s1 resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget
