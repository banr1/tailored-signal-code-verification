/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs

/-!
# Budget-Threaded Specifications for `<spqr::encoding::polynomial::PolyEncoder>::from_pb`

Allocator event envelopes (`EncoderFromPbAllocEnv`, `EncoderFromPbEnv`) and
`RustCliAllocBudget`-threaded specifications (`encoderFromPbSpec`, `encoderFromPbSpecX`) for
Block `374`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_374 blkPl_374)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchet (contractProg)
open CryptoVerification.SpqrV1.Poly (
  polyEncoderSize protoPolynomialEncoderAt protoPolynomialEncoderSize
  resultPolyEncoderFromPbAt
)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (
  EncoderFromPbGhost encoderFromPbName encoderFromPbStack encoderFromPbStackX
  fromPbResult
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-! ## Allocation and Full Event Envelopes -/

/-- Deterministic `AllocEvent` list emitted for one valid (`bs.length % 2 = 0`) `.points` slot in
    `<PolyEncoder>::from_pb`: `[]` if empty, else `rustAllocEvents (2 * bs.length) 2`
    (`Vec<GF16>::with_capacity(bs.len())`). -/
def encoderFromPbPtsSlotEvents (bs : List (BitVec 8)) : List AllocEvent :=
  if bs.isEmpty then [] else rustAllocEvents (2 * bs.length) 2

/-- Deterministic `AllocEvent` list emitted by the `.points` outer loop of `<PolyEncoder>::from_pb`
    across valid (`bs.length % 2 == 0`) slots up to the first odd-length slot. -/
def encoderFromPbPtsLoopEvents (pts : List (List (BitVec 8))) : List AllocEvent :=
  (pts.takeWhile (fun bs => bs.length % 2 == 0)).flatMap encoderFromPbPtsSlotEvents

/-- Deterministic `AllocEvent` list emitted by the 16-slot `Poly::zero()` initialization in the
    `.polys` branch of `<PolyEncoder>::from_pb`: 16 allocations of `(size = 2, align = 2)`. -/
def encoderFromPbPolysInitEvents : List AllocEvent :=
  (List.replicate 16 (rustAllocEvents 2 2)).flatten

/-- Deterministic `AllocEvent` list emitted for one valid (`!bs.isEmpty && bs.length % 2 == 0`)
    `.polys` slot in `<PolyEncoder>::from_pb`: allocates the new `bs.length`-byte `Vec<GF16>` buffer
    (`align = 2`) and deallocates the initial 2-byte `Poly::zero()` buffer (`align = 2`). -/
def encoderFromPbPolysSlotEvents (bs : List (BitVec 8)) : List AllocEvent :=
  rustAllocEvents bs.length 2 ++ rustDeallocEvents 2 2

/-- Deterministic `AllocEvent` list emitted by the `.polys` outer loop of `<PolyEncoder>::from_pb`
    across valid (`!bs.isEmpty && bs.length % 2 == 0`) slots up to the first malformed slot. -/
def encoderFromPbPolysLoopEvents (polys : List (List (BitVec 8))) : List AllocEvent :=
  (polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))).flatMap
    encoderFromPbPolysSlotEvents

/-- Precondition body event envelope of `<PolyEncoder>::from_pb` (before trailing `FreeOnlyEvs`
    deallocations of `ProtoPolynomialEncoder` and any partial `[Poly; 16]` / `[Point; 16]` buffers
    on error). -/
def EncoderFromPbAllocEnv (pb : ProtoPolynomialEncoder) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
    (pb.pts.length = 16 ∧ pb.polys.length = 0 ∧ evs = encoderFromPbPtsLoopEvents pb.pts) ∨
    (pb.pts.length = 0 ∧ pb.polys.length = 16 ∧
      evs = encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys)

/-- Full postcondition event envelope of `<PolyEncoder>::from_pb`: body events
    `EncoderFromPbAllocEnv pb` followed by `FreeOnlyEvs` cleanup. -/
def EncoderFromPbEnv (pb : ProtoPolynomialEncoder) (evs : List AllocEvent) : Prop :=
  ∃ evs_alloc evs_free,
    evs = evs_alloc ++ evs_free ∧
    EncoderFromPbAllocEnv pb evs_alloc ∧
    FreeOnlyEvs evs_free

theorem encoderFromPbAllocEnv_imp_encoderFromPbEnv {pb : ProtoPolynomialEncoder}
    {evs : List AllocEvent} (h : EncoderFromPbAllocEnv pb evs) :
    EncoderFromPbEnv pb evs :=
  ⟨evs, [], (List.append_nil evs).symm, h, FreeOnlyEvs.nil⟩

theorem fitsEnv_encoderFromPbAllocEnv_of_encoderFromPbEnv {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {pb : ProtoPolynomialEncoder}
    (h : FitsEnv M lim st (EncoderFromPbEnv pb)) :
    FitsEnv M lim st (EncoderFromPbAllocEnv pb) :=
  FitsEnv.mono (fun _ => encoderFromPbAllocEnv_imp_encoderFromPbEnv) h

/-! ## Budget-Threaded Specifications and Contracts -/

/-- Unplaced base specification of `<spqr::encoding::polynomial::PolyEncoder>::from_pb`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encoderFromPbSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncoderFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      (∀ bs ∈ x.pb.pts, bs.length ≤ 2 * 0x0555555555555555) ∧
      FitsEnv M lim st (EncoderFromPbAllocEnv x.pb)⌝ ∗
      memRegion x.out polyEncoderSize ∗
      protoPolynomialEncoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp encoderFromPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ EncoderFromPbEnv x.pb evs⌝ ∗
      resultPolyEncoderFromPbAt A.repAlloc x.out (fromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialEncoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack

/-- Budget-threaded specification of `<spqr::encoding::polynomial::PolyEncoder>::from_pb`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encoderFromPbSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncoderFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      (∀ bs ∈ x.pb.pts, bs.length ≤ 2 * 0x0555555555555555) ∧
      FitsEnv M lim st (EncoderFromPbAllocEnv x.pb) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out polyEncoderSize ∗
      protoPolynomialEncoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp encoderFromPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ EncoderFromPbEnv x.pb evs⌝ ∗
      resultPolyEncoderFromPbAt A.repAlloc x.out (fromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialEncoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack

/-- Unplaced extended-stack variant of `encoderFromPbSpecBase` (`encoderFromPbStackX = 1024 + extHookStack`). -/
def encoderFromPbSpecXBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncoderFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      (∀ bs ∈ x.pb.pts, bs.length ≤ 2 * 0x0555555555555555) ∧
      FitsEnv M lim st (EncoderFromPbAllocEnv x.pb)⌝ ∗
      memRegion x.out polyEncoderSize ∗
      protoPolynomialEncoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp encoderFromPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ EncoderFromPbEnv x.pb evs⌝ ∗
      resultPolyEncoderFromPbAt A.repAlloc x.out (fromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialEncoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStackX

/-- Extended-stack variant of `encoderFromPbSpec` (`encoderFromPbStackX = 1024 + extHookStack`). -/
def encoderFromPbSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncoderFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      (∀ bs ∈ x.pb.pts, bs.length ≤ 2 * 0x0555555555555555) ∧
      FitsEnv M lim st (EncoderFromPbAllocEnv x.pb) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out polyEncoderSize ∗
      protoPolynomialEncoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp encoderFromPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ EncoderFromPbEnv x.pb evs⌝ ∗
      resultPolyEncoderFromPbAt A.repAlloc x.out (fromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialEncoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStackX

/-- `encoderFromPbSpecBase M A lim` entails `encoderFromPbSpecXBase M A lim` by framing the unused bottom
    stack region. -/
theorem encoderFromPbSpecXBaseBase_of_encoderFromPbSpecBase {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (encoderFromPbSpecBase M A lim)) :
    subroutine_ok P addr (encoderFromPbSpecXBase M A lim) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : encoderFromPbStack ≤ encoderFromPbStackX := by decide
  have hsplit : stackAt s0.sp encoderFromPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encoderFromPbStackX)
        (encoderFromPbStackX - encoderFromPbStack) ∗
        stackAt s0.sp encoderFromPbStack := by
    have h1 := stackAt_split_bottom s0.sp encoderFromPbStack
      (encoderFromPbStackX - encoderFromPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encoderFromPbStackX)
      (encoderFromPbStackX - encoderFromPbStack) ∗ R
  have hpre' : s0.mem ⊨ (encoderFromPbSpecBase M A lim).pre (x, st) s0 ∗ R' := by
    dsimp only [encoderFromPbSpecXBase, encoderFromPbSpecBase, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encoderFromPbSpecXBase, encoderFromPbSpecBase, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `encoderFromPbSpec M A lim` entails `encoderFromPbSpecX M A lim` by framing the unused bottom
    stack region. -/
theorem encoderFromPbSpecX_of_encoderFromPbSpec [LibsignalPlacement] {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (encoderFromPbSpec M A lim)) :
    subroutine_ok P addr (encoderFromPbSpecX M A lim) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : encoderFromPbStack ≤ encoderFromPbStackX := by decide
  have hsplit : stackAt s0.sp encoderFromPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encoderFromPbStackX)
        (encoderFromPbStackX - encoderFromPbStack) ∗
        stackAt s0.sp encoderFromPbStack := by
    have h1 := stackAt_split_bottom s0.sp encoderFromPbStack
      (encoderFromPbStackX - encoderFromPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encoderFromPbStackX)
      (encoderFromPbStackX - encoderFromPbStack) ∗ R
  have hpre' : s0.mem ⊨ (encoderFromPbSpec M A lim).pre (x, st) s0 ∗ R' := by
    dsimp only [encoderFromPbSpecX, encoderFromPbSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encoderFromPbSpecX, encoderFromPbSpec, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

def EncoderFromPbOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg b ext)
    ((contractProg b ext).fnAddr encoderFromPbName)
    (encoderFromPbSpecBase M A lim)

def EncoderFromPbOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr encoderFromPbName)
    ((encoderFromPbSpecXBase M A lim).inImage img)

def EncoderFromPbPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
    (blkPl_374).base
    (encoderFromPbSpec M A lim)

def EncoderFromPbPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
    (blkPl_374).base
    (encoderFromPbSpecX M A lim)

end LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
