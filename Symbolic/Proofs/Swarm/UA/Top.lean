/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L01InitClearLeak
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.UA.Assembly
import Symbolic.Proofs.Swarm.UA.InitW
import Symbolic.Proofs.Swarm.UA.Leak
import Symbolic.Proofs.Swarm.UA.SlotInit
import Symbolic.Proofs.Swarm.UA.SlotRecvW
import Symbolic.Proofs.Swarm.UA.SlotRpkNO
import Symbolic.Proofs.Swarm.UA.SlotRpkProm
import Symbolic.Proofs.Swarm.UA.SlotSend
import Symbolic.Proofs.Swarm.UA.XlateExcW
import Symbolic.Proofs.Swarm.UA.XlateInv
import Symbolic.Proofs.Swarm.UA.XlateMovesToCli
import Symbolic.Proofs.Swarm.UA.Xport

/-!
# Whisper-Path Excuse Transfer

Discharges `XlateExcWSpec` by combining `XlateExcW.xlate_exc_w_of_movesToCli` with the forward
acceptance bridge `XlateMovesToCli.acceptsViaCliMoves_to_acceptsViaCli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.Top

open Symbolic.Swarm.Coinsplit.Lift.L01 (init_clear_leak)
open Symbolic.Swarm.Coinsplit.Lift.L02 (outcomeFaithfulCli_of_goodExit0Cut)
open Symbolic.Proofs.Swarm.UA.Defs (XlateExcWSpec)

/-- Discharges `XlateExcWSpec` via `XlateExcW.xlate_exc_w_of_movesToCli` and
`XlateMovesToCli.acceptsViaCliMoves_to_acceptsViaCli`. -/
theorem xlate_exc_w : XlateExcWSpec :=
  Symbolic.Proofs.Swarm.UA.XlateExcW.xlate_exc_w_of_movesToCli
    Symbolic.Proofs.Swarm.UA.XlateMovesToCli.acceptsViaCliMoves_to_acceptsViaCli

end Symbolic.Proofs.Swarm.UA.Top
