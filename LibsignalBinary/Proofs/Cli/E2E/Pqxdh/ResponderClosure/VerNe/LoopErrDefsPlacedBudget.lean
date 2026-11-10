/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrDefsPlaced

/-!
# Budget-Threaded Relocatable Version-Skip Tail Statement

Allocator-budget (`RustCliAllocBudget M`) statement `OverPrevErrCliPlacedStmt`
(`+0x1fd4 → +0x2cfc` in Block `518`) on `lsProg_518`, emitting `FreeOnlyEvs` with unreachable
panic/OOM (`Qp = fun _ _ => False`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrDefsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (pqLogLevelCellPlaced)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget
)

/-- Budget-threaded relocatable `[LibsignalPlacement]` previous-session version-skip tail
(`+8148 → +11516 in Block 518`) on `lsProg_518 ext`.
Only `drop_in_place<SessionStructure>` touches the heap (`FreeOnlyEvs`), so no `FitsEnv`
precondition is required and neither OOM nor panic is reachable (`Qp = fun _ _ => False`). -/
def OverPrevErrCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)),
    ∀ (st0 : M.σ) (s0 s : State) (prevPtr errsPtr : BitVec 64) (msgVer : BitVec 32)
      (G : SessionGhost) (st : SessionState (List (BitVec 8))),
      msgVer ≠ 4#32 →
      (lsProg_518 ext).CodeLoaded s.mem →
      s.pc = lsmpl.base 518 + 0x1fd4#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      s.readReg64 .x8 = 4#64 →
      s.readReg64 .x27 = prevPtr →
      SepWPp (lsProg_518 ext) (lsmpl.base 518 + 0x2cfc#64) s
        (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
         ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
         ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
         ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
         memRegion (errsPtr + 48#64) 144 ∗
         memRegion (s.sp + 0xa90#64) 344 ∗
         sessionStateAt A.repAlloc (s.sp + 0x930#64) G st ∗
         pqLogLevelCellPlaced ∗
         A.pool lim st0 s ∗
         stackAt s.sp growOneSpeStack)
        (fun sf P_f =>
          (P_f ⊢
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
            ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
            ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 60#64) 36 ∗
            memRegion (errsPtr + 96#64) 96 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            memRegion (s.sp + 0x930#64) 344 ∗
            pqLogLevelCellPlaced ∗
            (∃∗ evs : List AllocEvent,
              ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st0) sf) ∗
            stackAt s.sp growOneSpeStack) ∧
          sf.sp = s.sp ∧
          sf.trace = s0.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (lsProg_518 ext).CodeLoaded sf.mem)
        (fun _ _ => False)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrDefsPlacedBudget
