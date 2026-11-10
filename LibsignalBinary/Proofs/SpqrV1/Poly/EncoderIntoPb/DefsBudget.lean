/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs

/-!
# `<PolyEncoder>::into_pb`: Budget-Threaded Specifications

Allocator-budget specifications (`RustCliAllocBudget M`, `BudgetLimits`) and deterministic
`AllocEvent` envelopes (`EncoderIntoPbAllocEnv`, `EncoderIntoPbEnv`) for
`<spqr::encoding::polynomial::PolyEncoder>::into_pb` (Block `375`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_375 blkPl_375)
open CryptoVerification.LibsignalSpqrV1 (GF16 Point Poly PolyEncoder)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Poly (
  polyEncoderAt polyEncoderSize protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (
  EncoderIntoPbGhost encoderIntoPbName encoderIntoPbStack encoderIntoPbStackX
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget rustAllocEvents
)

/-! ## Allocation and Event Envelopes -/

/-- Deterministic `AllocEvent` list emitted when serializing one `Point` or `Poly` (`List GF16`)
    slot in `<PolyEncoder>::into_pb`: `[]` if empty, else `rustAllocEvents (2 * cs.length) 1`. -/
def encoderIntoPbSlotEvents (cs : List GF16) : List AllocEvent :=
  if cs.isEmpty then [] else rustAllocEvents (2 * cs.length) 1

/-- Underlying 16 `List GF16` element vectors of `enc : PolyEncoder` in serialization order. -/
def encoderIntoPbVecs (enc : PolyEncoder) : List (List GF16) :=
  match enc.s with
  | .points pts => pts.map Point.value
  | .polys polys => polys.map Poly.coefficients

/-- Deterministic `AllocEvent` list for the allocation phase of `<PolyEncoder>::into_pb`:
    two `384`-byte outer `Vec<Vec<u8>>` buffers (`pts` and `polys`, each `align = 8`) followed by
    per-slot `Vec<u8>` allocations across `encoderIntoPbVecs enc`. -/
def encoderIntoPbAllocEvents (enc : PolyEncoder) : List AllocEvent :=
  rustAllocEvents 384 8 ++ rustAllocEvents 384 8 ++
    (encoderIntoPbVecs enc).flatMap encoderIntoPbSlotEvents

/-- Precondition allocation envelope of `<PolyEncoder>::into_pb` (before the trailing
    `drop_glue::<[Poly; 16]>` deallocations). -/
def EncoderIntoPbAllocEnv (enc : PolyEncoder) (evs : List AllocEvent) : Prop :=
  evs = encoderIntoPbAllocEvents enc

/-- Full postcondition event envelope of `<PolyEncoder>::into_pb`: deterministic allocations
    `encoderIntoPbAllocEvents enc` followed by `FreeOnlyEvs` from dropping the 16 `Vec<GF16>`
    buffers. -/
def EncoderIntoPbEnv (enc : PolyEncoder) (evs : List AllocEvent) : Prop :=
  ∃ evs_alloc evs_free,
    evs = evs_alloc ++ evs_free ∧
    EncoderIntoPbAllocEnv enc evs_alloc ∧
    FreeOnlyEvs evs_free

theorem encoderIntoPbAllocEnv_imp_encoderIntoPbEnv {enc : PolyEncoder} {evs : List AllocEvent}
    (h : EncoderIntoPbAllocEnv enc evs) :
    EncoderIntoPbEnv enc evs :=
  ⟨evs, [], (List.append_nil evs).symm, h, FreeOnlyEvs.nil⟩

theorem fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {enc : PolyEncoder}
    (h : FitsEnv M lim st (EncoderIntoPbEnv enc)) :
    FitsEnv M lim st (EncoderIntoPbAllocEnv enc) :=
  FitsEnv.mono (fun _ => encoderIntoPbAllocEnv_imp_encoderIntoPbEnv) h

/-! ## Budget-Threaded Specifications -/

/-- Budget-threaded specification of `<spqr::encoding::polynomial::PolyEncoder>::into_pb`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encoderIntoPbSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncoderIntoPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.encA ∧
      FitsEnv M lim st (EncoderIntoPbAllocEnv x.enc)⌝ ∗
      memRegion x.out protoPolynomialEncoderSize ∗
      polyEncoderAt A.repAlloc x.encA x.enc ∗
      A.pool lim st s ∗ stackAt s.sp encoderIntoPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ EncoderIntoPbEnv x.enc evs⌝ ∗
      protoPolynomialEncoderAt A.repAlloc x.out x.enc.intoPb ∗
      memRegion x.encA polyEncoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderIntoPbStack

def encoderIntoPbSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncoderIntoPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.encA ∧
      FitsEnv M lim st (EncoderIntoPbAllocEnv x.enc)⌝ ∗
      memRegion x.out protoPolynomialEncoderSize ∗
      polyEncoderAt A.repAlloc x.encA x.enc ∗
      A.pool lim st s ∗ stackAt s.sp encoderIntoPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ EncoderIntoPbEnv x.enc evs⌝ ∗
      protoPolynomialEncoderAt A.repAlloc x.out x.enc.intoPb ∗
      memRegion x.encA polyEncoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderIntoPbStackX

/-- `encoderIntoPbSpec M A lim` entails `encoderIntoPbSpecX M A lim` by framing the unused bottom
    stack region. -/
theorem encoderIntoPbSpecX_of_encoderIntoPbSpec {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (encoderIntoPbSpec M A lim)) :
    subroutine_ok P addr (encoderIntoPbSpecX M A lim) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : encoderIntoPbStack ≤ encoderIntoPbStackX := by decide
  have hsplit : stackAt s0.sp encoderIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encoderIntoPbStackX)
        (encoderIntoPbStackX - encoderIntoPbStack) ∗
        stackAt s0.sp encoderIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp encoderIntoPbStack
      (encoderIntoPbStackX - encoderIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encoderIntoPbStackX)
      (encoderIntoPbStackX - encoderIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨ (encoderIntoPbSpec M A lim).pre (x, st) s0 ∗ R' := by
    dsimp only [encoderIntoPbSpecX, encoderIntoPbSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encoderIntoPbSpecX, encoderIntoPbSpec, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `<PolyEncoder>::into_pb` meets `encoderIntoPbSpec M A lim` on `tripleRatchetProgAtExt b ext`. -/
def EncoderIntoPbOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName)
    (encoderIntoPbSpec M A lim)

/-- `<PolyEncoder>::into_pb` meets `(encoderIntoPbSpecX M A lim).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def EncoderIntoPbOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encoderIntoPbName)
    ((encoderIntoPbSpecX M A lim).inImage img)

/-- `<PolyEncoder>::into_pb` (Block `375`) meets `encoderIntoPbSpec M A lim` under
    `[LibsignalPlacement]`. -/
def EncoderIntoPbPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
    (blkPl_375).base
    (encoderIntoPbSpec M A lim)

/-- `<PolyEncoder>::into_pb` (Block `375`) meets `encoderIntoPbSpecX M A lim` under
    `[LibsignalPlacement]`. -/
def EncoderIntoPbPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
    (blkPl_375).base
    (encoderIntoPbSpecX M A lim)

end LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
