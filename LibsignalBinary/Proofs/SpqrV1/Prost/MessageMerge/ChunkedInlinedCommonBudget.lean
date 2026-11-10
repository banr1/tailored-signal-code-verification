/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommon
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Specifications for Inlined `V1State.Chunked.*` `message::merge`

Lifts the Hoare contracts of the five inlined `V1State.Chunked.*::merge` subroutines (`KeysUnsampled`,
`HeaderReceived`, `NoHeaderReceived`, `HeaderSent`, and `EkReceivedCt1Sampled`) to
`RustCliAllocBudget` form (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`), providing generic `*SpecOfEnv`
combinators, `SpqrMergeLoopEnv` specializations, and panic-free `SepWPpLscro` call-frame helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeLoopEnv)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (chunkedHeaderSentPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt2SampledMergeGhost ChunkedEkReceivedCt1SampledMergeGhost
   ChunkedHeaderReceivedMergeGhost ChunkedHeaderSentMergeGhost
   ChunkedKeysSampledMergeGhost ChunkedKeysUnsampledMergeGhost
   ChunkedNoHeaderReceivedMergeGhost
   OptPolyDecoderBound OptPolyEncoderBound SepWPpLscro
   chunkedCt2SampledPBAt chunkedCt2SampledPBCapAt
   chunkedEkReceivedCt1SampledPBAt chunkedEkReceivedCt1SampledPBCapAt
   chunkedHeaderReceivedPBAt chunkedHeaderReceivedPBCapAt
   chunkedHeaderSentPBCapAt chunkedInlStack
   chunkedKeysSampledPBAt chunkedKeysSampledPBCapAt
   chunkedKeysUnsampledPBAt chunkedKeysUnsampledPBCapAt
   chunkedNoHeaderReceivedPBAt chunkedNoHeaderReceivedPBCapAt
   codecWireTypeToProto
   optPolyDecoderPtsLen optPolyEncoderPolysLen optPolyEncoderPtsLen)

/-! ## 1. `V1State.Chunked.KeysUnsampled::merge` -/

def ChunkedKeysUnsampledMergeEnv (x : ChunkedKeysUnsampledMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length 0 evs

def ChunkedKeysUnsampledMergePostEnv (x : ChunkedKeysUnsampledMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length 0 evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length 0 evs

theorem chunkedKeysUnsampledMergePostEnv_imp_pre {x : ChunkedKeysUnsampledMergeGhost}
    {evs : List AllocEvent} (h : ChunkedKeysUnsampledMergePostEnv x evs) :
    ChunkedKeysUnsampledMergeEnv x evs := by
  dsimp only [ChunkedKeysUnsampledMergePostEnv, ChunkedKeysUnsampledMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.KeysUnsampled::merge`. -/
def chunkedKeysUnsampledMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedKeysUnsampledMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedKeysUnsampledMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedKeysUnsampledPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedInlStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedInlStack ∗
      match (mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedKeysUnsampledPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.KeysUnsampled, chunkedKeysUnsampledPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.KeysUnsampled::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedKeysUnsampledMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedKeysUnsampledMergeGhost × M.σ) :=
  chunkedKeysUnsampledMergeSpecOfEnv A lim
    ChunkedKeysUnsampledMergeEnv ChunkedKeysUnsampledMergePostEnv

/-! ## 2. `V1State.Chunked.NoHeaderReceived::merge` -/

/-- `PolynomialDecoder` capacity upper bound for `Chunked.NoHeaderReceived::merge`. -/
def noHeaderReceivedPolyCapBound (x : ChunkedNoHeaderReceivedMergeGhost) : Nat :=
  optPolyDecoderPtsLen x.msg.receivingHdr + x.bs.length

def ChunkedNoHeaderReceivedMergeEnv (x : ChunkedNoHeaderReceivedMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (noHeaderReceivedPolyCapBound x) evs

def ChunkedNoHeaderReceivedMergePostEnv (x : ChunkedNoHeaderReceivedMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (noHeaderReceivedPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (noHeaderReceivedPolyCapBound x) evs

theorem chunkedNoHeaderReceivedMergePostEnv_imp_pre {x : ChunkedNoHeaderReceivedMergeGhost}
    {evs : List AllocEvent} (h : ChunkedNoHeaderReceivedMergePostEnv x evs) :
    ChunkedNoHeaderReceivedMergeEnv x evs := by
  dsimp only [ChunkedNoHeaderReceivedMergePostEnv, ChunkedNoHeaderReceivedMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.NoHeaderReceived::merge`. -/
def chunkedNoHeaderReceivedMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedNoHeaderReceivedMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedNoHeaderReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      OptPolyDecoderBound x.msg.receivingHdr x.bs.length ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedNoHeaderReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedInlStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedInlStack ∗
      match (mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedNoHeaderReceivedPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.NoHeaderReceived, chunkedNoHeaderReceivedPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.NoHeaderReceived::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedNoHeaderReceivedMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedNoHeaderReceivedMergeGhost × M.σ) :=
  chunkedNoHeaderReceivedMergeSpecOfEnv A lim
    ChunkedNoHeaderReceivedMergeEnv ChunkedNoHeaderReceivedMergePostEnv

/-! ## 3. `V1State.Chunked.Ct2Sampled::merge` -/

/-- `PolynomialEncoder` capacity upper bound for `Chunked.Ct2Sampled::merge`. -/
def ct2SampledPolyCapBound (x : ChunkedCt2SampledMergeGhost) : Nat :=
  Nat.max (optPolyEncoderPtsLen x.msg.sendingCt2) (optPolyEncoderPolysLen x.msg.sendingCt2) + x.bs.length

def ChunkedCt2SampledMergeEnv (x : ChunkedCt2SampledMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct2SampledPolyCapBound x) evs

def ChunkedCt2SampledMergePostEnv (x : ChunkedCt2SampledMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (ct2SampledPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct2SampledPolyCapBound x) evs

theorem chunkedCt2SampledMergePostEnv_imp_pre {x : ChunkedCt2SampledMergeGhost}
    {evs : List AllocEvent} (h : ChunkedCt2SampledMergePostEnv x evs) :
    ChunkedCt2SampledMergeEnv x evs := by
  dsimp only [ChunkedCt2SampledMergePostEnv, ChunkedCt2SampledMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.Ct2Sampled::merge`. -/
def chunkedCt2SampledMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedCt2SampledMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedCt2SampledMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      OptPolyEncoderBound x.msg.sendingCt2 x.bs.length ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedCt2SampledPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedInlStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedInlStack ∗
      match (mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedCt2SampledPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.Ct2Sampled, chunkedCt2SampledPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.Ct2Sampled::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedCt2SampledMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedCt2SampledMergeGhost × M.σ) :=
  chunkedCt2SampledMergeSpecOfEnv A lim
    ChunkedCt2SampledMergeEnv ChunkedCt2SampledMergePostEnv

/-! ## 4. `V1State.Chunked.HeaderReceived::merge` -/

/-- `PolynomialDecoder` capacity upper bound for `Chunked.HeaderReceived::merge`. -/
def headerReceivedPolyCapBound (x : ChunkedHeaderReceivedMergeGhost) : Nat :=
  optPolyDecoderPtsLen x.msg.receivingEk + x.bs.length

def ChunkedHeaderReceivedMergeEnv (x : ChunkedHeaderReceivedMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (headerReceivedPolyCapBound x) evs

def ChunkedHeaderReceivedMergePostEnv (x : ChunkedHeaderReceivedMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (headerReceivedPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (headerReceivedPolyCapBound x) evs

theorem chunkedHeaderReceivedMergePostEnv_imp_pre {x : ChunkedHeaderReceivedMergeGhost}
    {evs : List AllocEvent} (h : ChunkedHeaderReceivedMergePostEnv x evs) :
    ChunkedHeaderReceivedMergeEnv x evs := by
  dsimp only [ChunkedHeaderReceivedMergePostEnv, ChunkedHeaderReceivedMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.HeaderReceived::merge`. -/
def chunkedHeaderReceivedMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedHeaderReceivedMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedHeaderReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      OptPolyDecoderBound x.msg.receivingEk x.bs.length ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedHeaderReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedInlStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedInlStack ∗
      match (mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedHeaderReceivedPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.HeaderReceived, chunkedHeaderReceivedPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.HeaderReceived::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedHeaderReceivedMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedHeaderReceivedMergeGhost × M.σ) :=
  chunkedHeaderReceivedMergeSpecOfEnv A lim
    ChunkedHeaderReceivedMergeEnv ChunkedHeaderReceivedMergePostEnv

/-! ## 5. `V1State.Chunked.KeysSampled::merge` -/

/-- `PolynomialEncoder` capacity upper bound for `Chunked.KeysSampled::merge`. -/
def keysSampledPolyCapBound (x : ChunkedKeysSampledMergeGhost) : Nat :=
  Nat.max (optPolyEncoderPtsLen x.msg.sendingHdr) (optPolyEncoderPolysLen x.msg.sendingHdr) + x.bs.length

def ChunkedKeysSampledMergeEnv (x : ChunkedKeysSampledMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (keysSampledPolyCapBound x) evs

def ChunkedKeysSampledMergePostEnv (x : ChunkedKeysSampledMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.KeysSampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (keysSampledPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (keysSampledPolyCapBound x) evs

theorem chunkedKeysSampledMergePostEnv_imp_pre {x : ChunkedKeysSampledMergeGhost}
    {evs : List AllocEvent} (h : ChunkedKeysSampledMergePostEnv x evs) :
    ChunkedKeysSampledMergeEnv x evs := by
  dsimp only [ChunkedKeysSampledMergePostEnv, ChunkedKeysSampledMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.KeysSampled::merge`. -/
def chunkedKeysSampledMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedKeysSampledMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedKeysSampledMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      OptPolyEncoderBound x.msg.sendingHdr x.bs.length ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedKeysSampledPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedInlStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedInlStack ∗
      match (mergeMessage V1State.Chunked.KeysSampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedKeysSampledPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.KeysSampled, chunkedKeysSampledPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.KeysSampled::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedKeysSampledMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedKeysSampledMergeGhost × M.σ) :=
  chunkedKeysSampledMergeSpecOfEnv A lim
    ChunkedKeysSampledMergeEnv ChunkedKeysSampledMergePostEnv

/-! ## 6. `V1State.Chunked.HeaderSent::merge` -/

/-- `Polynomial{Encoder,Decoder}` capacity upper bound for `Chunked.HeaderSent::merge`. -/
def headerSentPolyCapBound (x : ChunkedHeaderSentMergeGhost) : Nat :=
  Nat.max
    (Nat.max (optPolyEncoderPtsLen x.msg.sendingEk) (optPolyEncoderPolysLen x.msg.sendingEk))
    (optPolyDecoderPtsLen x.msg.receivingCt1) + x.bs.length

def ChunkedHeaderSentMergeEnv (x : ChunkedHeaderSentMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (headerSentPolyCapBound x) evs

def ChunkedHeaderSentMergePostEnv (x : ChunkedHeaderSentMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (headerSentPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (headerSentPolyCapBound x) evs

theorem chunkedHeaderSentMergePostEnv_imp_pre {x : ChunkedHeaderSentMergeGhost}
    {evs : List AllocEvent} (h : ChunkedHeaderSentMergePostEnv x evs) :
    ChunkedHeaderSentMergeEnv x evs := by
  dsimp only [ChunkedHeaderSentMergePostEnv, ChunkedHeaderSentMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.HeaderSent::merge`. -/
def chunkedHeaderSentMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedHeaderSentMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedHeaderSentMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      OptPolyEncoderBound x.msg.sendingEk x.bs.length ∧
      OptPolyDecoderBound x.msg.receivingCt1 x.bs.length ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedInlStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedInlStack ∗
      match (mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.HeaderSent, chunkedHeaderSentPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.HeaderSent::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedHeaderSentMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedHeaderSentMergeGhost × M.σ) :=
  chunkedHeaderSentMergeSpecOfEnv A lim
    ChunkedHeaderSentMergeEnv ChunkedHeaderSentMergePostEnv

/-! ## 7. `V1State.Chunked.EkReceivedCt1Sampled::merge` -/

/-- `PolynomialEncoder` capacity upper bound for `Chunked.EkReceivedCt1Sampled::merge`. -/
def ekReceivedCt1SampledPolyCapBound (x : ChunkedEkReceivedCt1SampledMergeGhost) : Nat :=
  Nat.max (optPolyEncoderPtsLen x.msg.sendingCt1) (optPolyEncoderPolysLen x.msg.sendingCt1) + x.bs.length

def ChunkedEkReceivedCt1SampledMergeEnv (x : ChunkedEkReceivedCt1SampledMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ekReceivedCt1SampledPolyCapBound x) evs

def ChunkedEkReceivedCt1SampledMergePostEnv (x : ChunkedEkReceivedCt1SampledMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (ekReceivedCt1SampledPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ekReceivedCt1SampledPolyCapBound x) evs

theorem chunkedEkReceivedCt1SampledMergePostEnv_imp_pre {x : ChunkedEkReceivedCt1SampledMergeGhost}
    {evs : List AllocEvent} (h : ChunkedEkReceivedCt1SampledMergePostEnv x evs) :
    ChunkedEkReceivedCt1SampledMergeEnv x evs := by
  dsimp only [ChunkedEkReceivedCt1SampledMergePostEnv, ChunkedEkReceivedCt1SampledMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.EkReceivedCt1Sampled::merge`. -/
def chunkedEkReceivedCt1SampledMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedEkReceivedCt1SampledMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedEkReceivedCt1SampledMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      OptPolyEncoderBound x.msg.sendingCt1 x.bs.length ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedEkReceivedCt1SampledPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedInlStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedInlStack ∗
      match (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedEkReceivedCt1SampledPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.EkReceivedCt1Sampled, chunkedEkReceivedCt1SampledPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.EkReceivedCt1Sampled::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedEkReceivedCt1SampledMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedEkReceivedCt1SampledMergeGhost × M.σ) :=
  chunkedEkReceivedCt1SampledMergeSpecOfEnv A lim
    ChunkedEkReceivedCt1SampledMergeEnv ChunkedEkReceivedCt1SampledMergePostEnv

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
