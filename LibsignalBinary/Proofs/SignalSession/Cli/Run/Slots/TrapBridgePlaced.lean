/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop

/-!
# Relocatable Trap-at-RNG Program Bridge

Defines `trTrapExternsPlaced` (replacing `libsignal_session_rng_fill` with `rngTrap`) under
`[LibsignalPlacement]` and transfers `subroutine_ok` from rebased block programs under
`trTrapExternsPlaced` to `cliGhostExterns gh (cliExternsPlaced mmpl W)` via `TrapsOnly`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib ProofLib.Variant CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli.RunGlue

/-- Unmangled C ABI symbol of the libsignal RNG stub (`libsignal_session_rng_fill`). -/
abbrev lsRngFillSym : String := "libsignal_session_rng_fill"

theorem cliExternsPlaced_rngFill (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) lsRngFillSym = none := by
  rw [cliGhostExterns_other gh _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  exact cliExternsPlaced_none mmpl W (by decide +kernel) (by decide +kernel)

theorem cliExternsPlaced_rngFillName (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) rngFillName = none := by
  rw [cliGhostExterns_other gh _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  exact cliExternsPlaced_none mmpl W (by decide +kernel) (by decide +kernel)

/-- Extern hook map replacing `lsRngFillSym` with `rngTrap`. -/
def trTrapExternsPlaced (H : LibsignalHooks) : LibsignalHooks :=
  ProofLib.Variant.trapAt (· == lsRngFillSym) rngTrap H

/-- `TrapsOnly` from `trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` to `cliGhostExterns gh (cliExternsPlaced mmpl W)` on any rebased block program. -/
theorem trapsOnly_rebase_trTrapPlaced_cli (pc : Program) (b : BitVec 64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    TrapsOnly (pc.rebase b (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (pc.rebase b (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
  refine TrapsOnly.rebase pc b ?_
  intro n
  by_cases hr : n = lsRngFillSym
  · subst hr
    right
    refine ⟨rngTrap, ?_, rngTrap_isTrap⟩
    simp [trTrapExternsPlaced, ProofLib.Variant.trapAt]
  · left
    have hbeq : (n == lsRngFillSym) = false := beq_false_of_ne hr
    simp [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq]

/-- Transfers `subroutine_ok` across `trapsOnly_rebase_trTrapPlaced_cli`. -/
theorem subroutine_ok_cliPlaced_of_trTrap {α : Type} {pc : Program} {b addr : BitVec 64}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {spec : Spec α}
    (h : subroutine_ok
      (pc.rebase b (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      addr spec) :
    subroutine_ok (pc.rebase b (cliGhostExterns gh (cliExternsPlaced mmpl W))) addr spec :=
  subroutine_ok.of_trapsOnly (trapsOnly_rebase_trTrapPlaced_cli pc b mmpl gh W) h

end CryptoVerification.SignalSession.Cli.Slots
