/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget

/-!
# Budget-Threaded Handshake `bytes::merge [local#6]` W-Mode Definitions

Defines the budget-threaded unconstrained-capacity (`x.bs.length < 2 ^ 62`, `reqCap = false`)
contract `bytesMerge3RawSpecW` at `bytesMerge3Stack` (`33120` B).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeGhost decodeErrorHookStackX sliceCursorAfter sliceCursorAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (bytesMerge3Stack)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergeEnv bytesMergeRawSpecGen
)

theorem bytesMerge3Stack_eq_gen :
    0xe0 + (0x50 + (48 + decodeErrorHookStackX)) = bytesMerge3Stack := rfl

/-- Budget-threaded `bytesMerge3RawSpec` with `x.bs.length < 2 ^ 62` at `bytesMerge3Stack`
(`33120` B) and no `BytesMergeCapOk` in `pre` or `post` (`reqCap = false`). -/
def bytesMerge3RawSpecW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62 ∧
      FitsEnv M lim st (BytesMergeEnv x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMerge3Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

theorem bytesMerge3RawSpecW_eq_gen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    bytesMerge3RawSpecW A lim =
      bytesMergeRawSpecGen A lim (48 + decodeErrorHookStackX) false := rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsBudget
