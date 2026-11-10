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
# `signal_session::run` Arm `R3a`: `Recv` Whisper Contract (`R+0x214` → Join/Reject)

Relocatable (`[LibsignalPlacement]`) hop contracts `RunHopRecvWPlaced` and `RunHopRecvWPlacedOf`
for Arm `R3a` (`g.c = .recv peerV`, `g.i.stdin = 2#8 :: rest`) on Block `579`.
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

/-- Parametric-slot relocatable (`[LibsignalPlacement]`) Arm R3a Whisper hop contract:
from `AtDispatchPlaced` (`R+0x214`) on `g.c = .recv peerV` and `g.i.stdin = 2#8 :: rest`, calls
`wrap_decrypt_signal` via `slots.decryptSignal` to reach `JoinKPlaced` or `RejectKPlaced`. -/
def RunHopRecvWPlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV} {rest : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A H →
    RunCalleesPlaced A H B slots →
    RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlaced CodeOk g me s0 s →
    g.c = .recv peerV →
    g.i.stdin = 2#8 :: rest →
    PanicK g s0 Qp →
    RejectKPlaced CodeOk H A g s0 resStack Q Qp →
    JoinKPlaced CodeOk H A g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (dispatchMemPlaced A g me s0 resStack) Q Qp
      (runOom s0)

/-- Relocatable (`[LibsignalPlacement]`) Arm R3a Whisper hop contract (`run_hop_recvW_ok`):
from `AtDispatchPlaced` (`R+0x214`) on `g.c = .recv peerV` and `g.i.stdin = 2#8 :: rest`, calls
`wrap_decrypt_signal` to reach `JoinKPlaced` or `RejectKPlaced`. -/
def RunHopRecvWPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  RunHopRecvWPlacedOf CodeOk A H B S (slotsOfPlaced A S needs) resStack

end CryptoVerification.SignalSession.Cli.RunCompose
