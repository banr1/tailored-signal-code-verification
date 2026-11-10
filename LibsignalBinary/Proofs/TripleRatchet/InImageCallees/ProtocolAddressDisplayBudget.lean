/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Proofs for `<ProtocolAddress as Display>::fmt`

Proves `[LibsignalPlacement]` `RustCliAllocBudget` contracts (`addrDisplayEnvSpec` and
`addrDisplaySpec`) for `<ProtocolAddress as Display>::fmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement blkPC_215 blkPl_215 lsFmtWriteSym ls_hook_ok_of_mem lsρ
)
open CryptoVerification.LibsignalTripleRatchet.ProtocolAddressDisplay (stackAt_addrDisplay)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (fmtWriteBudgetEnvSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (addrDisplayEnvSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) parameterized by `hwrite`
against `addrDisplayEnvSpec M A lim Env`. -/
theorem addrDisplay_placed_ok_of_contract [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : String → Option (State → State)}
    (hwrite : subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (lsρ lsFmtWriteSym) (fmtWriteBudgetEnvSpec M A lim Env)) :
    subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (blkPl_215).base
      (addrDisplayEnvSpec M A lim Env) := by
  simp only [addrDisplayEnvSpec, stackAt_addrDisplay]
  simp only [fmtWriteBudgetEnvSpec] at hwrite
  cells_unfold
  wp_init x s0
  rcases x with ⟨f, v, vt, bs, st⟩
  dsimp only at *
  subst ‹s0.readReg64 .x1 = f›
  wp_steps_sync_pool (lsρ lsFmtWriteSym)
  simp only [State.setMem_setMem]
  wp_call hwrite (v, bs, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  wp_done

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) meets
`addrDisplayEnvSpec M A lim Env` (and `addrDisplaySpec M A lim` when `Env = FmtWriteEnv`). -/
theorem addrDisplay_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : String → Option (State → State)}
    (hW : HookSat H lsFmtWriteSym (fmtWriteBudgetEnvSpec M A lim Env)) :
    subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (blkPl_215).base
      (addrDisplayEnvSpec M A lim Env) :=
  addrDisplay_placed_ok_of_contract (ls_hook_ok_of_mem hW)

end LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget
