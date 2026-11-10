/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainMerge
import LibsignalBinary.Proofs.E2E.Record.L1GX.Frame
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MergeFieldX10
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MergeFieldX11
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MergeFieldX13
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MergeFieldX14
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MergeFieldX15
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MergeFieldX9P
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserCalleesX
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.B3DeserQ

/-!
# Full PQXDH-scope `SessionStructure::merge_field` contract

**Checked by Lean.** Assembles the base `DeserializeGeneral` leaves (`mergeFieldXBaseAll_ok`) and
the PQXDH extension leaves for tags 9, 10, 11, 13, 14, and 15 into the unrestricted contract
`MergeFieldXOk C ctl (fun _ => True) abs`, together with relocatable `[LibsignalPlacement]`
corollaries.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

theorem mergeFieldX_ok_of (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} (hC : DeserializeSeed.DeserializeCallees C ctl abs)
    (h14 : MergeFieldXOk C ctl (fun fl => fl.tag = 14) abs) :
    MergeFieldXOk C ctl (fun _ => True) abs := by
  have hB := mergeFieldXBaseAll_ok C ctl hC (DeserializeGeneral.chainMergeGen_ok C ctl hC)
  have h9 := Leaf.MergeFieldX9P.mergeFieldX9P_ok C ctl hC
  have h10 := Leaf.MergeFieldX10.mergeFieldX10_ok C ctl hC
  have h11 := Leaf.MergeFieldX11.mergeFieldX11_ok C ctl hC
  have h13 := Leaf.MergeFieldX13.mergeFieldX13_ok C ctl hC
  have h15 := Leaf.MergeFieldX15.mergeFieldX15_ok C ctl hC
  have hAll := mergeFieldXOk_or hB
    (mergeFieldXOk_or h9 (mergeFieldXOk_or h10 (mergeFieldXOk_or h11
      (mergeFieldXOk_or h13 (mergeFieldXOk_or h14 h15)))))
  refine mergeFieldXOk_of_imp hAll ?_
  intro fl _
  cases fl with
  | base f => exact Or.inl ⟨f, rfl⟩
  | pendingId i k => exact Or.inr (Or.inl (Or.inl ⟨i, k, rfl⟩))
  | pendingSpk o k spk => exact Or.inr (Or.inl (Or.inr ⟨o, k, spk, rfl⟩))
  | remReg r => exact Or.inr (Or.inr (Or.inl rfl))
  | locReg l => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | abk b => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | kyber i ct => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | pq b => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- Unrestricted `SessionStructure::merge_field` contract over all `GenFieldX` constructors. -/
theorem mergeFieldX_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} (hC : DeserializeSeed.DeserializeCallees C ctl abs) :
    MergeFieldXOk C ctl (fun _ => True) abs :=
  mergeFieldX_ok_of C ctl hC (Leaf.MergeFieldX14.mergeFieldX14_ok C ctl hC)

/-! ## Relocatable `SessionStructure::merge_field` corollaries -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_L1GX_Glue_Placed : True := trivial

/-- Relocatable `SessionStructure::merge_field` contract on `lsProg_15 H` assuming `DeserializeCalleesPlacedW H`. -/
theorem mergeFieldX_placed_ok_of_callees [LibsignalPlacement]
    (H : LibsignalHooks)
    (hCallees : Proofs.libsignal.Hooks2.DeserializeCalleesPlacedW H) :
    Symbolic.Swarm.TRREF.B3DeserQ.MergeFieldQPlacedOkW H (fun _ => True) :=
  Symbolic.Swarm.TRREF.B3DeserQ.mergeFieldQPlacedW_ok H hCallees

/-- Relocatable `SessionStructure::merge_field` contract from `AllocContractsPlaced A0 H` and `memcpy`. -/
theorem mergeFieldX_placed_ok_of_alloc [LibsignalPlacement]
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    Symbolic.Swarm.TRREF.B3DeserQ.MergeFieldQPlacedOkW H (fun _ => True) :=
  Symbolic.Swarm.TRREF.B3DeserQ.mergeFieldQPlacedW_ok H
    (Proofs.libsignal.Hooks2.deserializeCalleesPlacedW_of_alloc hA hMemcpy)

set_option maxRecDepth 200000 in
/-- Relocatable `SessionStructure::merge_field` contract from individual allocator, memory, shim, and panic hook hypotheses. -/
theorem mergeFieldX_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A0))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A0))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A0))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hmemcpy : HookSat H "memcpy" (sessionMemcpySpec extHookStack))
    (hmemmove : HookSat H "memmove" (sessionMemmoveSpec extHookStack))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Symbolic.Swarm.TRREF.B3DeserQ.MergeFieldQPlacedOkW H (fun _ => True) :=
  mergeFieldX_placed_ok_of_alloc
    (Proofs.libsignal.Stage1X.AllocContractsPlaced.of_hooks
      halloc hdealloc hrealloc hshim hmemmove hpan_err hpan_alloc)
    (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy))

end Placed

end CryptoVerification.E2E.Record.L1GX
