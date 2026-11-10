/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs

/-!
# Budget-Threaded Specifications for `<PolyDecoder as Decoder>::decoded_message`

Allocator event envelopes (`LagrangeInterpolateInlinedEnv`, `DecodedMessageLoopEnv`,
`DecodedMessageEnv`) and `RustCliAllocBudget`-threaded specifications (`decodedMessageSpec`,
`decodedMessagePlacedSpec`) for Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418 lsmpl)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly PolyDecoder Pt SortedSetPt)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt vecHeaderBytes)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  DecodedMessageGhost collectPointsVecsTotal collectedSlices decodedMessageName
  decodedMessageStack decodedMessageTotal lagrangeInterpolateTotal optVecU8Of
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents
)

/-! ## Allocation and Event Envelopes for `decoded_message` -/

/-- Deterministic allocation events emitted by `<Poly>::compute_at` on a polynomial with `len`
    coefficients (before its epilogue `__rust_dealloc`):
    - `len = 0`: `grow_one` from `0 → 4` `GF16`s (`8` bytes, align `2`);
    - `len = 1`: `with_capacity(1)` (`2` bytes, align `2`) then `grow_one` (`2 → 8` bytes, align `2`);
    - `2 ≤ len`: `with_capacity(len)` (`2 * len` bytes, align `2`). -/
def computeAtAllocEvents (len : Nat) : List AllocEvent :=
  if len = 0 then
    rustAllocEvents 8 2
  else if len = 1 then
    rustAllocEvents 2 2 ++ rustReallocEvents 2 8 2
  else
    rustAllocEvents (2 * len) 2

/-- Event envelope of one `<Poly>::compute_at` call on `len` coefficients:
    `computeAtAllocEvents len` followed by `FreeOnlyEvs` (`__rust_dealloc` of the scratch powers
    buffer). -/
def ComputeAtCallEnv (len : Nat) : List AllocEvent → Prop :=
  SeqEnv (· = computeAtAllocEvents len) FreeOnlyEvs

theorem computeAtCallEnv_of_dealloc (len cap : Nat) :
    ComputeAtCallEnv len (computeAtAllocEvents len ++ rustDeallocEvents (2 * cap) 2) :=
  SeqEnv.append rfl (FreeOnlyEvs.singleton 2 (2 * cap))

theorem computeAtCallEnv_nonempty (len : Nat) :
    ∃ evs, ComputeAtCallEnv len evs :=
  ⟨computeAtAllocEvents len, Or.inl rfl⟩

/-- Event envelope of the cache-miss branch of inlined `Poly::lagrange_interpolate` on `k` points:
    `__rust_alloc(2 * k, 2)` for the accumulator polynomial, `__rust_alloc(2 * (k + 1), 2)` inside
    `lagrange_interpolate_prepare`, `__rust_alloc(2 * (k + 1), 2)` for the working copy `ptr_l`, and
    `FreeOnlyEvs` (`__rust_dealloc` of `ptr_l` and `ptr_b`). -/
def LagrangeInterpolateMissEnv (k : Nat) : List AllocEvent → Prop :=
  SeqEnv
    (· = rustAllocEvents (2 * k) 2 ++ rustAllocEvents (2 * (k + 1)) 2 ++ rustAllocEvents (2 * (k + 1)) 2)
    FreeOnlyEvs

theorem lagrangeInterpolateMissEnv_nonempty (k : Nat) :
    ∃ evs, LagrangeInterpolateMissEnv k evs :=
  ⟨rustAllocEvents (2 * k) 2 ++ rustAllocEvents (2 * (k + 1)) 2 ++ rustAllocEvents (2 * (k + 1)) 2,
    Or.inl rfl⟩

/-- Event envelope of inlined `Poly::lagrange_interpolate` given cache slot `optPoly` and slice
    length `k`: `[]` on a cache hit (`some _`), `LagrangeInterpolateMissEnv k` on `none`. -/
def LagrangeInterpolateInlinedEnv : Option Poly → Nat → List AllocEvent → Prop
  | some _, _, evs => evs = []
  | none, k, evs => LagrangeInterpolateMissEnv k evs

theorem lagrangeInterpolateInlinedEnv_nonempty (optPoly : Option Poly) (k : Nat) :
    ∃ evs, LagrangeInterpolateInlinedEnv optPoly k evs := by
  cases optPoly with
  | some _ => exact ⟨[], rfl⟩
  | none => exact lagrangeInterpolateMissEnv_nonempty k

/-- Sequential `AllocEvent` envelope of `PolyDecoder.decodedMessageLoop` (`rem` iterations starting
    at `i` with cache `polys`), mirroring the control flow of `decodedMessageLoopTotal`. -/
def DecodedMessageLoopEnv (self : PolyDecoder) (pointsVecs : List (List Pt)) :
    Nat → Nat → List (Option Poly) → List AllocEvent → Prop
  | _, 0, _, evs => evs = []
  | i, rem + 1, polys, evs =>
    let poly := i % 16
    let polyIdx := i / 16
    let pt : Pt := { x := GF16.new (BitVec.ofNat 16 polyIdx), y := GF16.ZERO }
    let polyPts := self.pts[poly]?.getD SortedSetPt.new
    match polyPts.binarySearch pt with
    | .ok _ =>
      DecodedMessageLoopEnv self pointsVecs (i + 1) rem polys evs
    | .error _ =>
      let optPoly := polys[poly]?.getD none
      match optPoly with
      | some p =>
        SeqEnv (ComputeAtCallEnv p.coefficients.length)
          (DecodedMessageLoopEnv self pointsVecs (i + 1) rem polys) evs
      | none =>
        let ptsSlice := pointsVecs[poly]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        SeqEnv (LagrangeInterpolateMissEnv ptsSlice.length)
          (SeqEnv (ComputeAtCallEnv interp.coefficients.length)
            (DecodedMessageLoopEnv self pointsVecs (i + 1) rem (polys.set poly (some interp)))) evs

theorem decodedMessageLoopEnv_nonempty (self : PolyDecoder) (pointsVecs : List (List Pt)) :
    ∀ (rem i : Nat) (polys : List (Option Poly)),
      ∃ evs, DecodedMessageLoopEnv self pointsVecs i rem polys evs
  | 0, _, _ => ⟨[], rfl⟩
  | rem + 1, i, polys => by
    unfold DecodedMessageLoopEnv
    dsimp only
    split
    · exact decodedMessageLoopEnv_nonempty self pointsVecs rem (i + 1) polys
    · split
      · rename_i p _
        rcases computeAtCallEnv_nonempty p.coefficients.length with ⟨e1, he1⟩
        rcases decodedMessageLoopEnv_nonempty self pointsVecs rem (i + 1) polys with ⟨e2, he2⟩
        exact ⟨e1 ++ e2, SeqEnv.append he1 he2⟩
      · let ptsSlice := pointsVecs[i % 16]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        rcases lagrangeInterpolateMissEnv_nonempty ptsSlice.length with ⟨e1, he1⟩
        rcases computeAtCallEnv_nonempty interp.coefficients.length with ⟨e2, he2⟩
        rcases decodedMessageLoopEnv_nonempty self pointsVecs rem (i + 1)
          (polys.set (i % 16) (some interp)) with ⟨e3, he3⟩
        exact ⟨e1 ++ (e2 ++ e3), SeqEnv.append he1 (SeqEnv.append he2 he3)⟩

/-- Top-level `AllocEvent` envelope of `<PolyDecoder as Decoder>::decoded_message`:
    - `dec.isComplete = true`: `[]`;
    - `dec.isComplete = false` with incomplete points or `dec.ptsNeeded = 0`:
      `rustAllocEvents 256 8` (`points_vecs` array) followed by `FreeOnlyEvs`;
    - `dec.isComplete = false` with complete points and `1 ≤ dec.ptsNeeded`:
      `rustAllocEvents 256 8 ++ rustAllocEvents (2 * dec.ptsNeeded) 1`, followed by
      `DecodedMessageLoopEnv`, followed by `FreeOnlyEvs` (`polys` cache + `points_vecs` drops). -/
def DecodedMessageEnv (dec : PolyDecoder) (evs : List AllocEvent) : Prop :=
  if dec.isComplete then
    evs = []
  else if (collectPointsVecsTotal dec 0 16 false []).1 || decide (dec.ptsNeeded = 0) then
    SeqEnv (· = rustAllocEvents 256 8) FreeOnlyEvs evs
  else
    SeqEnv (· = rustAllocEvents 256 8 ++ rustAllocEvents (2 * dec.ptsNeeded) 1)
      (SeqEnv
        (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none))
        FreeOnlyEvs)
      evs

theorem decodedMessageEnv_nonempty (dec : PolyDecoder) :
    ∃ evs, DecodedMessageEnv dec evs := by
  unfold DecodedMessageEnv
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨rustAllocEvents 256 8, Or.inl rfl⟩
    · rcases decodedMessageLoopEnv_nonempty dec (collectedSlices dec 0 16)
        dec.ptsNeeded 0 (List.replicate 16 none) with ⟨el, hel⟩
      exact ⟨(rustAllocEvents 256 8 ++ rustAllocEvents (2 * dec.ptsNeeded) 1) ++ el,
        SeqEnv.append (E₁ := fun x => x = rustAllocEvents 256 8 ++ rustAllocEvents (2 * dec.ptsNeeded) 1)
          rfl (Or.inl hel)⟩

/-! ## Budget-Threaded Specifications and Contracts -/

/-- Budget-threaded fixed-base specification of
    `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def decodedMessageSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) : Spec (DecodedMessageGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧ s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec ∧
      FitsEnv M lim st (DecodedMessageEnv x.dec)⌝ ∗
      memRegion x.out vecHeaderBytes ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp decodedMessageStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜DecodedMessageEnv x.dec evs ∧ sf.trace = s0.trace⌝ ∗
      optVecU8Of A.repAlloc x.out (decodedMessageTotal x.dec) ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decodedMessageStack

def DecodedMessageOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodedMessageName)
    (decodedMessageSpec M A lim b)

/-- Budget-threaded relocatable (`[LibsignalPlacement]`) specification of
    `<PolyDecoder as Decoder>::decoded_message` (Block `418`). -/
def decodedMessagePlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodedMessageGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec ∧
      FitsEnv M lim st (DecodedMessageEnv x.dec)⌝ ∗
      memRegion x.out vecHeaderBytes ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp decodedMessageStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜DecodedMessageEnv x.dec evs ∧ sf.trace = s0.trace⌝ ∗
      optVecU8Of A.repAlloc x.out (decodedMessageTotal x.dec) ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decodedMessageStack

def DecodedMessagePlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (lsmpl.base 418)
    (decodedMessagePlacedSpec M A lim)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
