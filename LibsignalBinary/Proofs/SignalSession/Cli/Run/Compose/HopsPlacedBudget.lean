/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Placed Continuation Abbreviations for `signal_session::run`

Budget-threaded (`RustCliAllocBudget M`) continuation abbreviations (`JoinKPlaced`,
`JoinKPlacedEnv`, `RejectKPlaced`, `RejectKPlacedEnv`) and `run_hop_dropSpeOwned_placed` on
Block `579` (`lsProg_579`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtJoinPlaced AtRejectPlaced Bytes RejectKind joinMem rejectMem runProgPlaced)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock cliDropSpeOwned_placed_at_block)

/-- Budget-threaded continuation from `AtJoinPlaced` (`R + 0xf8c`) on `runProgPlaced H`
(envelope-erased over any cost state `st : M.σ`, matching `runSpecAnyPlaced`; `Qo` defaults to
`⌜False⌝`). -/
abbrev JoinKPlaced [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : RunCall) (s0 : State) (resStack : Nat)
    (Q Qp : State → SepProp → Prop)
    (Qo : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  ∀ (s : State) (st : M.σ) (g' : StoresGhost) (out : Bytes),
    AtJoinPlaced CodeOk g g' out s0 s →
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (joinMem (A.atState lim st s) g g' out s0 resStack) Q Qp Qo

/-- Envelope-constrained continuation from `AtJoinPlaced` (`R + 0xf8c`) on `runProgPlaced H`
(for `runSpecPlaced` with an explicit cost-state invariant `EnvAt`). -/
abbrev JoinKPlacedEnv [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EnvAt : StoresGhost → Bytes → M.σ → Prop)
    (g : RunCall) (s0 : State) (resStack : Nat)
    (Q Qp : State → SepProp → Prop)
    (Qo : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  ∀ (s : State) (st : M.σ) (g' : StoresGhost) (out : Bytes),
    AtJoinPlaced CodeOk g g' out s0 s →
    EnvAt g' out st →
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (joinMem (A.atState lim st s) g g' out s0 resStack) Q Qp Qo

/-- Budget-threaded continuation from `AtRejectPlaced` (`R + 0x124` or `R + 0x2c7c`) on
`runProgPlaced H` (envelope-erased over any cost state `st : M.σ`, matching `runSpecAnyPlaced`;
`Qo` defaults to `⌜False⌝`). -/
abbrev RejectKPlaced [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : RunCall) (s0 : State) (resStack : Nat)
    (Q Qp : State → SepProp → Prop)
    (Qo : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  ∀ (s : State) (st : M.σ) (g' : StoresGhost) (rk : RejectKind),
    AtRejectPlaced CodeOk g g' rk s0 s →
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (rejectMem (A.atState lim st s) g g' rk s0 resStack) Q Qp Qo

/-- Envelope-constrained continuation from `AtRejectPlaced` (`R + 0x124` or `R + 0x2c7c`) on
`runProgPlaced H` (for `runSpecPlaced` with an explicit cost-state invariant `EnvAt`). -/
abbrev RejectKPlacedEnv [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EnvAt : StoresGhost → RejectKind → M.σ → Prop)
    (g : RunCall) (s0 : State) (resStack : Nat)
    (Q Qp : State → SepProp → Prop)
    (Qo : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  ∀ (s : State) (st : M.σ) (g' : StoresGhost) (rk : RejectKind),
    AtRejectPlaced CodeOk g g' rk s0 s →
    EnvAt g' rk st →
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (rejectMem (A.atState lim st s) g g' rk s0 resStack) Q Qp Qo

/-- `drop_glue::<SignalProtocolError>` (Block `552`) meets budget-threaded `dropSpeOwnedSpecPlaced`
on Block `579` (`lsProg_579 H`) from `halloc : AllocContractsXCliPlaced A lim H`. -/
theorem run_hop_dropSpeOwned_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : AllocContractsXCliPlaced A lim H) :
    DropSpeOwnedOkAtBlock (lsProg_579 H) A lim :=
  cliDropSpeOwned_placed_at_block (i := 579) halloc

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
