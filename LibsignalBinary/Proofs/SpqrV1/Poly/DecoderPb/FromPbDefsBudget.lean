/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefs

/-!
# Budget-Threaded Specifications for `<spqr::encoding::polynomial::PolyDecoder>::from_pb`

Allocator event envelopes (`FromPbDecAllocEnv`, `FromPbDecEnv`) and `RustCliAllocBudget`-threaded
specifications (`fromPbDecSpec`, `fromPbDecSpecX`) for Block `376`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_376 blkPl_376)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Poly (
  polyDecoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize
  resultPolyDecoderFromPbAt
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (
  FromPbDecGhost fromPbDecName fromPbDecResult fromPbDecStack fromPbDecStackX
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget rustAllocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-! ## Allocation and Full Event Envelopes -/

/-- Deterministic `AllocEvent` list emitted when allocating one `SortedSet<Pt>` buffer from raw
    serialized bytes `pts` (when `pts.length % 4 = 0`): `[]` if empty, else
    `rustAllocEvents pts.length 2`. -/
def fromPbDecSlotEvents (pts : List (BitVec 8)) : List AllocEvent :=
  if pts.isEmpty then [] else rustAllocEvents pts.length 2

/-- Deterministic `AllocEvent` list emitted by the outer loop of `<PolyDecoder>::from_pb` on `pts`:
    allocates each valid (`bs.length % 4 == 0`) slot prefix up to the first malformed slot (or all
    slots when every `bs` has `bs.length % 4 = 0`). -/
def fromPbDecLoopAllocEvents (pts : List (List (BitVec 8))) : List AllocEvent :=
  (pts.takeWhile (fun bs => bs.length % 4 == 0)).flatMap fromPbDecSlotEvents

/-- Precondition allocation envelope of `<PolyDecoder>::from_pb` (before trailing `FreeOnlyEvs`
    deallocations of `ProtoPolynomialDecoder` and any partial `SortedSet<Pt>` buffers on error). -/
def FromPbDecAllocEnv (pb : ProtoPolynomialDecoder) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ (pb.pts.length = 16 ∧ evs = fromPbDecLoopAllocEvents pb.pts)

/-- Full postcondition event envelope of `<PolyDecoder>::from_pb`: prefix allocations
    `FromPbDecAllocEnv pb` followed by `FreeOnlyEvs` cleanup. -/
def FromPbDecEnv (pb : ProtoPolynomialDecoder) (evs : List AllocEvent) : Prop :=
  ∃ evs_alloc evs_free,
    evs = evs_alloc ++ evs_free ∧
    FromPbDecAllocEnv pb evs_alloc ∧
    FreeOnlyEvs evs_free

theorem fromPbDecAllocEnv_imp_fromPbDecEnv {pb : ProtoPolynomialDecoder} {evs : List AllocEvent}
    (h : FromPbDecAllocEnv pb evs) :
    FromPbDecEnv pb evs :=
  ⟨evs, [], (List.append_nil evs).symm, h, FreeOnlyEvs.nil⟩

theorem fitsEnv_fromPbDecAllocEnv_of_fromPbDecEnv {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {pb : ProtoPolynomialDecoder}
    (h : FitsEnv M lim st (FromPbDecEnv pb)) :
    FitsEnv M lim st (FromPbDecAllocEnv pb) :=
  FitsEnv.mono (fun _ => fromPbDecAllocEnv_imp_fromPbDecEnv) h

/-! ## Budget-Threaded Specifications and Contracts -/

/-- Unplaced base specification of `<spqr::encoding::polynomial::PolyDecoder>::from_pb`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def fromPbDecSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FromPbDecGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (FromPbDecAllocEnv x.pb)⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp fromPbDecStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv x.pb evs⌝ ∗
      resultPolyDecoderFromPbAt A.repAlloc x.out (fromPbDecResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp fromPbDecStack

/-- Unplaced extended-stack variant of `fromPbDecSpecBase` (`fromPbDecStackX = 544 + extHookStack`). -/
def fromPbDecSpecXBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FromPbDecGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (FromPbDecAllocEnv x.pb)⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp fromPbDecStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv x.pb evs⌝ ∗
      resultPolyDecoderFromPbAt A.repAlloc x.out (fromPbDecResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp fromPbDecStackX

/-- Budget-threaded specification of `<spqr::encoding::polynomial::PolyDecoder>::from_pb`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def fromPbDecSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (FromPbDecGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (FromPbDecAllocEnv x.pb) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp fromPbDecStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv x.pb evs⌝ ∗
      resultPolyDecoderFromPbAt A.repAlloc x.out (fromPbDecResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp fromPbDecStack

/-- Extended-stack variant of `fromPbDecSpec` (`fromPbDecStackX = 544 + extHookStack`). -/
def fromPbDecSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (FromPbDecGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (FromPbDecAllocEnv x.pb) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp fromPbDecStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv x.pb evs⌝ ∗
      resultPolyDecoderFromPbAt A.repAlloc x.out (fromPbDecResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp fromPbDecStackX

def FromPbDecOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName)
    (fromPbDecSpecBase M A lim)

def FromPbDecOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr fromPbDecName)
    ((fromPbDecSpecXBase M A lim).inImage img)

def FromPbDecPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
    (blkPl_376).base
    (fromPbDecSpec M A lim)

def FromPbDecPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
    (blkPl_376).base
    (fromPbDecSpecX M A lim)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
