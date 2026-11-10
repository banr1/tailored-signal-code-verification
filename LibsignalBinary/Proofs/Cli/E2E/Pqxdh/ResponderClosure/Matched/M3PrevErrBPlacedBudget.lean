/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.HelpersBudget

/-!
# Budget-Threaded Relocatable Stage P3 Error Spatial Bundles

Threads `RustCliAllocBudget M` (`A.pool lim st s` and `A.repAlloc`) through the `[LibsignalPlacement]`
Stage P3 error spatial bundles `stageP3ErrPrePrevEmptyPlacedBudget` and
`stageP3ErrPostPrevEmptyPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SessionState SignalProtocolError)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt vecResultAt)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (recordResultAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeySavedRegsAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

def stageP3ErrPrePrevEmptyPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost)
    (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) ∗
  sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
  prevSessionsEmptyAt A.repAlloc coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x930#64) 48 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  A.pool lim st s ∗ stackAt s.sp growOneSpeStack

abbrev stageP3ErrPrePrevEmptyPlaced := @stageP3ErrPrePrevEmptyPlacedBudget

def stageP3ErrPostPrevEmptyPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (coroPtr outPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  recordResultAt A.repAlloc outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  A.pool lim st s ∗ stackAt s.sp growOneSpeStack

abbrev stageP3ErrPostPrevEmptyPlaced := @stageP3ErrPostPrevEmptyPlacedBudget

theorem stageP3ErrPrePrevEmptyPlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost)
    (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) :
    stageP3ErrPrePrevEmptyPlacedBudget A lim st s0 s coroPtr outPtr initErrsPtr g e b_2c0
      G₂ recG st₂ recSt =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyPlaced
        (A.atState lim st s) s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt :=
  rfl

theorem stageP3ErrPostPrevEmptyPlacedBudget_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (coroPtr outPtr : BitVec 64) (e : SignalProtocolError) :
    stageP3ErrPostPrevEmptyPlacedBudget A lim st s0 s coroPtr outPtr e =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyPlaced
        (A.atState lim st s) s0 s coroPtr outPtr e :=
  rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlacedBudget
