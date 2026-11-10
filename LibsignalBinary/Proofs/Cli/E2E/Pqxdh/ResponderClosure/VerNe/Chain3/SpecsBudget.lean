/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Specs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Callee Specifications for `message::merge<Chain>`

Allocator-budget (`RustCliAllocBudget M`) contracts for the `prost` helpers invoked by
`message::merge<Chain> [local#4]`: `decodeVarint2SpecX` (`decode_varint::<&mut &[u8]> [local#4]`
at 32,896 B stack) and `bytesMerge3RawSpec` (`bytes::merge::<Vec<u8>, &mut &[u8]> [local#5]` at
33,120 B stack), together with a stack-framing lift from `MergeDefsBudget.bytesMergeRawSpecX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped Proofs.libsignal.Hooks2
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (bytesMerge3Stack decodeVarint2StackX)
open CryptoVerification.LibsignalProtoCodec (decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeCapOk BytesMergeGhost DecodeVarintSlowGhost decodeErrorHookStackX decodeVarintSlowStackX sliceCursorAfter sliceCursorAt)
open CryptoVerification.RustHeap (vecU8At)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (DecodeVarintSliceEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv)

abbrev DecodeVarint2Env := DecodeVarintSliceEnv

/-- Budget-threaded contract for `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]`
at stack bound `decodeVarint2StackX` (32,896 B). -/
def decodeVarint2SpecX {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecodeVarintSlowGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (DecodeVarintSliceEnv x.bs)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp decodeVarint2StackX
  post := fun (x, st) s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent,
        ⌜DecodeVarintSliceEnv x.bs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp decodeVarint2StackX ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded raw contract for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]` at stack bound
`bytesMerge3Stack` (33,120 B). -/
def bytesMerge3RawSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length ∧ FitsEnv M lim st (BytesMergeEnv x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMerge3Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent,
        ⌜BytesMergeEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Lifts `MergeDefsBudget.bytesMergeRawSpecX` (33,072 B stack) to `bytesMerge3RawSpec`
(`bytesMerge3Stack = 33120` B). -/
theorem bytesMerge3RawSpec_ok_of_bytesMergeRawSpecX {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX A lim)) :
    subroutine_ok prog entry (bytesMerge3RawSpec A lim) := by
  let sub : Nat := 0xe0 + (0x50 + decodeErrorHookStackX)
  have hle : sub ≤ bytesMerge3Stack := by decide
  have h64 : bytesMerge3Stack ≤ 2 ^ 64 := by decide
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hal _ => ?_
  let slack := memRegion (s0.sp - BitVec.ofNat 64 bytesMerge3Stack) (bytesMerge3Stack - sub)
  have hsplit : stackAt s0.sp bytesMerge3Stack = slack ∗ stackAt s0.sp sub := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp sub (bytesMerge3Stack - sub)
      (by dsimp only [sub, bytesMerge3Stack, decodeVarint2StackX, decodeVarintSlowStackX,
            decodeErrorHookStackX] at h64 ⊢; omega)
    have htot : sub + (bytesMerge3Stack - sub) = bytesMerge3Stack := Nat.add_sub_of_le hle
    rwa [htot] at h0
  have hpre' : s0.mem ⊨
      (LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX A lim).pre
        (x, st) s0 ∗ (slack ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [SpecsBudget.bytesMerge3RawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPreBoundBudget,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec]
    rw [hsplit]
    exact Entails.of_eq (by dsimp +zetaDelta only [sub]; sep_ac_rfl)
  refine h.mono_outcome (x, st) (slack ∗ R) s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hal', hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hal', Satisfies.mono ?_ hpost⟩
    dsimp only [SpecsBudget.bytesMerge3RawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec]
    rw [hsplit]
    cases mergeBytes x.wt x.bs with
    | some vr => exact Entails.of_eq (by dsimp +zetaDelta only [sub]; sep_ac_rfl)
    | none => exact Entails.of_eq (by dsimp +zetaDelta only [sub]; sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsBudget
