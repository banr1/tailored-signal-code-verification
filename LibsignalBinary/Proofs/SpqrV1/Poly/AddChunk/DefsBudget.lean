/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs

/-!
# Budget-Threaded Specifications for `<PolyDecoder as Decoder>::add_chunk`

Threads `RustCliAllocBudget M`, `BudgetLimits`, and `AddChunkEnv` through `addChunkBsearchSpec`,
`addChunkSpec`, and `addChunkSpecX` for Block `419`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_419 blkPl_419)
open CryptoVerification.LibsignalSpqrV1 (SortedSetPt)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (
  AddChunkGhost PolyDecoderStrictSorted addChunkBsearch addChunkName addChunkStack
  addChunkStackX addChunkTotal
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv
  RustCliAllocBudget SeqEnv rustAllocEvents rustReallocEvents
)

/-! ## Slot and Loop Allocation Envelopes -/

/-- Deterministic `AllocEvent` list emitted by `<RawVec<Pt>>::grow_one` (`stride = 4, align = 2`)
    when triggered at full buffer `cap = len`:
    `rustAllocEvents 16 2` when `len = 0`, else
    `rustReallocEvents (4 * len) (4 * max (2 * len) 4) 2`. -/
def growOnePtEvents (len : Nat) : List AllocEvent :=
  if len = 0 then
    rustAllocEvents 16 2
  else
    rustReallocEvents (4 * len) (4 * max (2 * len) 4) 2

/-- Per-slot allocation envelope for inserting/replacing one point in `s : SortedSetPt`:
    either `[]` (in-place overwrite or spare capacity `s.vec.length < cap`) or
    `growOnePtEvents s.vec.length` (when `s.vec.length = cap`). -/
def AddChunkSlotEnv (s : SortedSetPt) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = growOnePtEvents s.vec.length

/-- Sequential allocation envelope across a list of `SortedSetPt` slots in `add_chunk`. -/
def AddChunkSlotsEnv : List SortedSetPt → List AllocEvent → Prop
  | [], evs => evs = []
  | s :: rest, evs => SeqEnv (AddChunkSlotEnv s) (AddChunkSlotsEnv rest) evs

/-- Allocation envelope of `<PolyDecoder as Decoder>::add_chunk` on `x : AddChunkGhost`. -/
def AddChunkEnv (x : AddChunkGhost) (evs : List AllocEvent) : Prop :=
  AddChunkSlotsEnv x.dec.pts evs

theorem addChunkSlotsEnv_nil : ∀ (pts : List SortedSetPt), AddChunkSlotsEnv pts []
  | [] => rfl
  | _ :: _ => SeqEnv.inl (Or.inl rfl)

theorem addChunkEnv_nil (x : AddChunkGhost) : AddChunkEnv x [] :=
  addChunkSlotsEnv_nil x.dec.pts

/-! ## Budget-Threaded Specifications and Contracts -/

/-- Budget-threaded hardware specification of `<PolyDecoder as Decoder>::add_chunk`
    without requiring `PolyDecoderStrictSorted` in the precondition (outputs `addChunkBsearch`). -/
def addChunkBsearchSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AddChunkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.decA ∧ s.readReg64 .x1 = x.chunkA ∧
      (∀ s ∈ x.dec.pts, s.vec.length ≤ 65536) ∧
      FitsEnv M lim st (AddChunkEnv x)⌝ ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim st s ∗ stackAt s.sp addChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ AddChunkEnv x evs⌝ ∗
      polyDecoderAt A.repAlloc x.decA (addChunkBsearch x.dec x.chunk) ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp addChunkStack

/-- Budget-threaded specification of `<PolyDecoder as Decoder>::add_chunk` on a strictly sorted
    `PolyDecoder` (`PolyDecoderStrictSorted x.dec`), outputting `addChunkTotal x.dec x.chunk`
    and preserving `PolyDecoderStrictSorted`. -/
def addChunkSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AddChunkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.decA ∧ s.readReg64 .x1 = x.chunkA ∧
      PolyDecoderStrictSorted x.dec ∧
      FitsEnv M lim st (AddChunkEnv x)⌝ ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim st s ∗ stackAt s.sp addChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ AddChunkEnv x evs ∧
        PolyDecoderStrictSorted (addChunkTotal x.dec x.chunk)⌝ ∗
      polyDecoderAt A.repAlloc x.decA (addChunkTotal x.dec x.chunk) ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp addChunkStack

/-- Extended-stack variant of `addChunkSpec` (`addChunkStackX = 96 + extHookStack`). -/
def addChunkSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AddChunkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.decA ∧ s.readReg64 .x1 = x.chunkA ∧
      PolyDecoderStrictSorted x.dec ∧
      FitsEnv M lim st (AddChunkEnv x)⌝ ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim st s ∗ stackAt s.sp addChunkStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ AddChunkEnv x evs ∧
        PolyDecoderStrictSorted (addChunkTotal x.dec x.chunk)⌝ ∗
      polyDecoderAt A.repAlloc x.decA (addChunkTotal x.dec x.chunk) ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp addChunkStackX

def AddChunkOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr addChunkName)
    (addChunkSpec M A lim)

def AddChunkOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr addChunkName)
    ((addChunkSpecX M A lim).inImage img)

def AddChunkPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
    (blkPl_419).base
    (addChunkSpec M A lim)

def AddChunkPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
    (blkPl_419).base
    (addChunkSpecX M A lim)

end LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
