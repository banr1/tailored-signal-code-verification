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
# Relocatable Arm `J` Specification for `signal_session::run`

Defines `RunHopJoinPlaced` (`R+0xf8c` / `R+0x124` / `R+0x2c7c → lr`) on Block `579` under
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

/-- Relocatable Arm `J` contract from `AtJoinPlaced` (`R+0xf8c`) or `AtRejectPlaced` (`R+0x124` / `R+0x2c7c`) through store/output moves, deallocation, and stack restoration to `runPostPlaced`. -/
def RunHopJoinPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {s0 s : State} {P : SepProp} {Qp : State → SepProp → Prop},
    RunHooksPlaced A H →
    runNeed B (slotsOfPlaced A S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    ((∃ g' out, AtJoinPlaced CodeOk g g' out s0 s ∧ P = joinMem A g g' out s0 resStack) ∨
      (∃ g' rk, AtRejectPlaced CodeOk g g' rk s0 s ∧ P = rejectMem A g g' rk s0 resStack)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P
      (runPostPlaced CodeOk A g resStack s0)
      Qp
      (runOom s0)

end CryptoVerification.SignalSession.Cli.RunCompose
