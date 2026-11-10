/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Hops
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `signal_session::run`: Placed Continuation Abbreviations

Relocatable (`[LibsignalPlacement]`) continuation abbreviations (`JoinKPlaced`, `RejectKPlaced`)
and `run_hop_dropSpeOwned_placed` on Block `579` (`lsProg_579`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed

/-- Continuation from `AtJoinPlaced` (`R + 0xf8c`) on `runProgPlaced H`. -/
abbrev JoinKPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustAlloc) (g : RunCall) (s0 : State) (resStack : Nat)
    (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s : State) (g' : StoresGhost) (out : Bytes),
    AtJoinPlaced CodeOk g g' out s0 s →
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (joinMem A g g' out s0 resStack) Q Qp (runOom s0)

/-- Continuation from `AtRejectPlaced` (`R + 0x124` or `R + 0x2c7c`) on `runProgPlaced H`. -/
abbrev RejectKPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (H : LibsignalHooks)
    (A : RustAlloc) (g : RunCall) (s0 : State) (resStack : Nat)
    (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s : State) (g' : StoresGhost) (rk : RejectKind),
    AtRejectPlaced CodeOk g g' rk s0 s →
    ProofLib.SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (rejectMem A g g' rk s0 resStack) Q Qp (runOom s0)

/-- `drop_glue::<SignalProtocolError>` (Block `552`) meets `dropSpeOwnedSpecPlaced` on Block `579`
(`lsProg_579 H`) from `halloc : AllocContractsXCliPlaced A H`. -/
theorem run_hop_dropSpeOwned_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (halloc : AllocContractsXCliPlaced A H) :
    RunDrop.DropSpeOwnedOkAtBlock (lsProg_579 H) A :=
  RunDrop.cliDropSpeOwned_placed_at_block (i := 579) halloc

end CryptoVerification.SignalSession.Cli.RunCompose
