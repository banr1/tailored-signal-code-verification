/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

/-!
# Budget-Threaded Seam Decomposition for `PreKeySignalMessage::new`

`VmPreserved`-augmented `encoded_len` contract (block `119`) and budget-threaded relocatable seam
states `SeamA_placed`, `SeamB_placed`, and `PreKeyMsgSegExit_placed` on block `41` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved subroutine_ok_of_withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 lsProg_119 blkPl_119)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (PreKeyMsgEncodedLenGhost PreKeyMsgFrameGhost)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
  (preKeyMsgNewRawPrologueEvents preKeyMsgNewSpec)

def preKeyMsgEncodedLenSpec (A : RustAlloc) : Spec PreKeyMsgEncodedLenGhost :=
  withVmPreserved
    (CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.preKeyMsgEncodedLenSpec A)

abbrev PreKeyMsgEncodedLenPlacedOk [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_119 H) (blkPl_119).base (preKeyMsgEncodedLenSpec A)

theorem PreKeyMsgEncodedLenPlacedOk.toUnbudgeted [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (h : PreKeyMsgEncodedLenPlacedOk A H) :
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.PreKeyMsgEncodedLenPlacedOk
      A H :=
  subroutine_ok_of_withVmPreserved h

/-- Budget-threaded Seam (a) state on block `41`, advancing cost-model state `st` by
`preKeyMsgNewRawPrologueEvents` (no heap allocations occur after `SeamA`). -/
def SeamA_placed [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : PreKeyMsgNewCall) (st : M.σ)
    (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State) : Prop :=
  ∃ evs : List AllocEvent,
    evs = preKeyMsgNewRawPrologueEvents x.kp x.msg.serialized.length x.model.serialized.length ∧
    LsRetAddr624 (s0.readReg64 .lr) ∧
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.SeamA_placed
      (A.atState lim (M.stepEvents evs st) s) x g R s0 s

/-- Budget-threaded Seam (b) state on block `41` at `M.stepEvents evs st`. -/
def SeamB_placed [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : PreKeyMsgNewCall) (st : M.σ)
    (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State) : Prop :=
  ∃ evs : List AllocEvent,
    evs = preKeyMsgNewRawPrologueEvents x.kp x.msg.serialized.length x.model.serialized.length ∧
    LsRetAddr624 (s0.readReg64 .lr) ∧
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.SeamB_placed
      (A.atState lim (M.stepEvents evs st) s) x g R s0 s

/-- Budget-threaded segment-exit relation on `lsProg_41 H`. -/
def PreKeyMsgSegExit_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (x : PreKeyMsgNewCall) (st : M.σ) (R : SepProp) (s0 s : State) (next : State → Prop) : Prop :=
  (lsProg_41 H).CodeLoaded s.mem →
    ∃ sf, Steps (lsProg_41 H) s sf ∧
      (next sf ∨ SubroutineOutcome (preKeyMsgNewSpec M A lim) (x, st) R s0 sf)

theorem preKeyMsgSegExit_placed_chain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PreKeyMsgNewCall} {st : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : PreKeyMsgSegExit_placed A lim H x st R s0 s next)
    (h2 : ∀ s', next s' →
      reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec M A lim) (x, st) R s0 s') :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec M A lim) (x, st) R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
