/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTag8Budget
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDeallocBudget

/-!
# Budget-Threaded `PreKeySignalMessage::new` Field Encoding and Epilogue

Relocatable `[LibsignalPlacement]` composition of protobuf tag 1–8 encoding (`SeamA_placed → SeamB_placed`,
zero allocations on the pre-reserved buffer) with the `sret` write and temporary buffer deallocations
(`SeamB_placed → exit`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsBudget

open Arm64 ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded
   blkPC_10 blkPl_10 lsRustNoAllocShimSym lsRustAllocSym lsRustDeallocSym
   lsRustReallocSym lsMemcpySym lsρ)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (PreKeyMsgFrameGhost)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec framelessMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget (preKeyMsgNewSpec)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
  (SeamA_placed SeamB_placed PreKeyMsgSegExit_placed preKeyMsgSegExit_placed_chain)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget
  (encodeVarintNoGrowPlacedSpec)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTag8Budget
  (fields_encode_core_placed_ok_of_ok fields_encode_core_placed_ok
   fields_encode_core_placed_ok_sessionHooks)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDeallocBudget
  (fields_epilogue_placed_ok_aux)

theorem fields_encode_placed_ok_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (hmc : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s (SeamB_placed A lim x st g R s0) :=
  fields_encode_core_placed_ok_of_ok henc0 hmc x st g R s0 s hA

/-- Relocatable field-encoding segment (`+0x25c..+0x4c4`, `SeamA_placed → SeamB_placed`) under
`noAllocShimBudgetSpec` and `framelessMemcpyBudgetSpec` hooks. -/
theorem fields_encode_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s (SeamB_placed A lim x st g R s0) :=
  fields_encode_core_placed_ok hshim halloc hrealloc hmemcpy x st g R s0 s hA

theorem fields_encode_placed_ok_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s (SeamB_placed A lim x st g R s0) :=
  fields_encode_core_placed_ok_sessionHooks hshim halloc hrealloc hmemcpy x st g R s0 s hA

/-- Relocatable epilogue segment (`+0x4c4..+0x608`, `SeamB_placed → exit`): writes `x.ret`,
frees the four temporary heap clones, and returns under `preKeyMsgNewSpec M A lim`. -/
theorem fields_epilogue_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hB : SeamB_placed A lim x st g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec M A lim) (x, st) R s0 s :=
  fields_epilogue_placed_ok_aux hdealloc hB

theorem fields_placed_ok_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (hmc : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec M A lim) (x, st) R s0 s :=
  preKeyMsgSegExit_placed_chain
    (fields_encode_placed_ok_of_ok henc0 hmc x st g R s0 s hA)
    (fun s' hB => fields_epilogue_placed_ok hdealloc x st g R s0 s' hB)

/-- Combined relocatable field-encoding and epilogue segment (`+0x25c..+0x608`,
`SeamA_placed → exit`). -/
theorem fields_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec M A lim) (x, st) R s0 s :=
  preKeyMsgSegExit_placed_chain
    (fields_encode_placed_ok hshim halloc hrealloc hmemcpy x st g R s0 s hA)
    (fun s' hB => fields_epilogue_placed_ok hdealloc x st g R s0 s' hB)

theorem fields_placed_ok_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec M A lim) (x, st) R s0 s :=
  preKeyMsgSegExit_placed_chain
    (fields_encode_placed_ok_sessionHooks hshim halloc hrealloc hmemcpy x st g R s0 s hA)
    (fun s' hB => fields_epilogue_placed_ok hdealloc x st g R s0 s' hB)

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsBudget
