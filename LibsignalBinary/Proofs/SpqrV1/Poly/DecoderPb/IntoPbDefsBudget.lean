/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefs

/-!
# Budget-Threaded Specifications for `<spqr::encoding::polynomial::PolyDecoder>::into_pb`

Allocator event envelopes (`DecoderIntoPbAllocEnv`, `DecoderIntoPbEnv`) and
`RustCliAllocBudget`-threaded specifications (`decoderIntoPbSpec`, `decoderIntoPbSpecX`) for
Block `377`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_377 blkPl_377)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder Pt)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Poly (
  polyDecoderAt polyDecoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (
  DecoderIntoPbGhost decoderIntoPbName decoderIntoPbStack decoderIntoPbStackX
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget rustAllocEvents
)

/-! ## Allocation and Full Event Envelopes -/

/-- Deterministic `AllocEvent` list emitted when serializing one `SortedSet<Pt>` slot in
    `<PolyDecoder>::into_pb`: `[]` if empty, else `rustAllocEvents (4 * pts.length) 1`. -/
def decoderIntoPbSlotEvents (pts : List Pt) : List AllocEvent :=
  if pts.isEmpty then [] else rustAllocEvents (4 * pts.length) 1

/-- Deterministic `AllocEvent` list for the allocation phase of `<PolyDecoder>::into_pb`:
    the `384`-byte outer `Vec<Vec<u8>>` buffer (`align = 8`) followed by per-slot `Vec<u8>`
    allocations across `dec.pts`. -/
def decoderIntoPbAllocEvents (dec : PolyDecoder) : List AllocEvent :=
  rustAllocEvents 384 8 ++ dec.pts.flatMap (fun s => decoderIntoPbSlotEvents s.vec)

/-- Precondition allocation envelope of `<PolyDecoder>::into_pb` (before the trailing
    `drop_glue::<[SortedSet<Pt>; 16]>` deallocations). -/
def DecoderIntoPbAllocEnv (dec : PolyDecoder) (evs : List AllocEvent) : Prop :=
  evs = decoderIntoPbAllocEvents dec

/-- Full postcondition event envelope of `<PolyDecoder>::into_pb`: deterministic allocations
    `decoderIntoPbAllocEvents dec` followed by `FreeOnlyEvs` from dropping the 16 `SortedSet<Pt>`
    buffers. -/
def DecoderIntoPbEnv (dec : PolyDecoder) (evs : List AllocEvent) : Prop :=
  ∃ evs_alloc evs_free,
    evs = evs_alloc ++ evs_free ∧
    DecoderIntoPbAllocEnv dec evs_alloc ∧
    FreeOnlyEvs evs_free

theorem decoderIntoPbAllocEnv_imp_decoderIntoPbEnv {dec : PolyDecoder} {evs : List AllocEvent}
    (h : DecoderIntoPbAllocEnv dec evs) :
    DecoderIntoPbEnv dec evs :=
  ⟨evs, [], (List.append_nil evs).symm, h, FreeOnlyEvs.nil⟩

theorem fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {dec : PolyDecoder}
    (h : FitsEnv M lim st (DecoderIntoPbEnv dec)) :
    FitsEnv M lim st (DecoderIntoPbAllocEnv dec) :=
  FitsEnv.mono (fun _ => decoderIntoPbAllocEnv_imp_decoderIntoPbEnv) h

/-! ## Budget-Threaded Specifications and Contracts -/

/-- Budget-threaded specification of `<spqr::encoding::polynomial::PolyDecoder>::into_pb`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def decoderIntoPbSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecoderIntoPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.decA ∧
      FitsEnv M lim st (DecoderIntoPbAllocEnv x.dec)⌝ ∗
      memRegion x.out protoPolynomialDecoderSize ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      A.pool lim st s ∗ stackAt s.sp decoderIntoPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ DecoderIntoPbEnv x.dec evs⌝ ∗
      protoPolynomialDecoderAt A.repAlloc x.out x.dec.intoPb ∗
      memRegion x.decA polyDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decoderIntoPbStack

/-- Extended-stack variant of `decoderIntoPbSpec` (`decoderIntoPbStackX = 160 + extHookStack`). -/
def decoderIntoPbSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecoderIntoPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.decA ∧
      FitsEnv M lim st (DecoderIntoPbAllocEnv x.dec)⌝ ∗
      memRegion x.out protoPolynomialDecoderSize ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      A.pool lim st s ∗ stackAt s.sp decoderIntoPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ DecoderIntoPbEnv x.dec evs⌝ ∗
      protoPolynomialDecoderAt A.repAlloc x.out x.dec.intoPb ∗
      memRegion x.decA polyDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decoderIntoPbStackX

def DecoderIntoPbOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName)
    (decoderIntoPbSpec M A lim)

def DecoderIntoPbOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr decoderIntoPbName)
    ((decoderIntoPbSpecX M A lim).inImage img)

def DecoderIntoPbPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
    (blkPl_377).base
    (decoderIntoPbSpec M A lim)

def DecoderIntoPbPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
    (blkPl_377).base
    (decoderIntoPbSpecX M A lim)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
