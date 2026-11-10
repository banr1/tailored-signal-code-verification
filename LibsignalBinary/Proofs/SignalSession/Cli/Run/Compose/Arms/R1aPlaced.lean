/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Arm `R1a` Specification for `signal_session::run`

Defines `RunHopInit1PlacedOf` and `RunHopInit1Placed` (`R+0x214 → R+0x74c`) on Block `579` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-- Slot-parametric relocatable Arm `R1a` contract (`R+0x214 → R+0x74c` or `RejectKPlaced` / `PanicK`) for `g.c = .init peerV dir`. -/
def RunHopInit1PlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV} {dir : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A H →
    RunCalleesPlaced A H B slots →
    RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlaced CodeOk g me s0 s →
    g.c = .init peerV dir →
    PanicK g s0 Qp →
    RejectKPlaced CodeOk H A g s0 resStack Q Qp →
    (∀ s1 (d1 : Init1Data),
      AtInit1Placed CodeOk g d1 s0 s1 →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1 (init1MemPlaced A g d1 s0 resStack)
        Q Qp (runOom s0)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (dispatchMemPlaced A g me s0 resStack) Q Qp
      (runOom s0)

def RunHopInit1Placed [LibsignalPlacement] (CodeOk : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  RunHopInit1PlacedOf CodeOk A H B S (slotsOfPlaced A S needs) resStack

end CryptoVerification.SignalSession.Cli.RunCompose
