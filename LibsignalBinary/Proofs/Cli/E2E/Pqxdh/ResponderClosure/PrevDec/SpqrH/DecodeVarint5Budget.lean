/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget

/-!
# Budget-Threaded Handshake `decode_varint [local#5]` Specifications

Defines the deterministic allocator event list `decodeVarint2Events`, envelope `DecodeVarint2Env`,
and total-correctness (`onPanic = ⌜False⌝` under `FitsEnv`) specifications `decodeVarint2Spec` and
`decodeVarint2SpecX` for `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget

open Arm64 ProofLib
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
  (decodeVarint2Stack decodeVarint2StackX)
open CryptoVerification.LibsignalProtoCodec (decodeVarint)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost sliceCursorAfter sliceCursorAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)

/-- Deterministic allocator events of `decode_varint::<&mut &[u8]> [local#5]` (`[]` on `Ok`,
`rustAllocEvents 72 8` via `DecodeError::from` on `Err`). -/
abbrev decodeVarint2Events (bs : List (BitVec 8)) : List AllocEvent :=
  decodeVarintSliceEvents bs

/-- Callee-fixed allocator event envelope of `decode_varint::<&mut &[u8]> [local#5]`. -/
abbrev DecodeVarint2Env (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  DecodeVarintSliceEnv bs evs

/-- Budget-threaded contract of `prost::encoding::varint::decode_varint::<&mut &[u8]>`
at `decodeVarint2Stack`. -/
def decodeVarint2Spec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (DecodeVarint2Env x.bs)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp decodeVarint2Stack
  post := fun (x, st) s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env x.bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp decodeVarint2Stack ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `prost::encoding::varint::decode_varint::<&mut &[u8]>`
under `Stage2ContractsX` (`decodeVarint2StackX`). -/
def decodeVarint2SpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (DecodeVarint2Env x.bs)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp decodeVarint2StackX
  post := fun (x, st) s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env x.bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp decodeVarint2StackX ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget
