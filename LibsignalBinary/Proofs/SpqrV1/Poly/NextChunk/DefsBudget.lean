/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlaced

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Budget-Threaded Specifications

Deterministic `AllocEvent` envelopes (`PolyNextChunkEnv` and per-phase sub-envelopes) and
allocator-budget specifications (`RustCliAllocBudget M`, `BudgetLimits`) for fixed-base and
relocatable (`[LibsignalPlacement]`, Block `416`) `<PolyEncoder as Encoder>::next_chunk`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget

open Arm64 ProofLib
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk (
  PolyNextChunkGhost completePointsPolysAt completePointsPolysPlacedAt
  polyNextChunkName polyNextChunkStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  ComputeAtCallEnv computeAtAllocEvents computeAtCallEnv_nonempty computeAtCallEnv_of_dealloc
)

/-! ## 1. Deterministic Allocation and Event Envelopes for `PolyEncoder::next_chunk` -/

/-- Prologue allocation event of `<PolyEncoder as Encoder>::next_chunk`:
    `__rust_alloc(32, 1)` for the 32-byte `Vec<u8>` chunk buffer (`out_ptr`). -/
def nextChunkPrologueEvents : List AllocEvent :=
  rustAllocEvents 32 1

def NextChunkPrologueEnv : List AllocEvent → Prop :=
  (· = nextChunkPrologueEvents)

theorem nextChunkPrologueEnv_nonempty : ∃ evs, NextChunkPrologueEnv evs :=
  ⟨nextChunkPrologueEvents, rfl⟩

/-- Epilogue deallocation event of `<PolyEncoder as Encoder>::next_chunk`:
    `__rust_dealloc(32, 1)` for `out_ptr`. -/
def nextChunkEpilogueEvents : List AllocEvent :=
  rustDeallocEvents 32 1

def NextChunkEpilogueEnv : List AllocEvent → Prop :=
  (· = nextChunkEpilogueEvents)

theorem nextChunkEpilogueEnv_nonempty : ∃ evs, NextChunkEpilogueEnv evs :=
  ⟨nextChunkEpilogueEvents, rfl⟩

theorem nextChunkEpilogueEvents_freeOnly : FreeOnlyEvs nextChunkEpilogueEvents :=
  FreeOnlyEvs.singleton 1 32

/-- Final scratch capacity freed by `<Poly>::compute_at` on `len` coefficients. -/
def computeAtScratchCap (len : Nat) : Nat :=
  if len ≤ 1 then 4 else len

/-- Exact event list of `<Poly>::compute_at` on `len` coefficients (`alloc/realloc` + `dealloc`). -/
def computeAtEvents (len : Nat) : List AllocEvent :=
  computeAtAllocEvents len ++ rustDeallocEvents (2 * computeAtScratchCap len) 2

theorem computeAtEvents_satisfies_callEnv (len : Nat) :
    ComputeAtCallEnv len (computeAtEvents len) :=
  computeAtCallEnv_of_dealloc len (computeAtScratchCap len)

/-- Sequential `ComputeAtCallEnv` envelope across a list of `Poly`s (`PolysLoop`). -/
def NextChunkPolysLoopEnv : List Poly → List AllocEvent → Prop
  | [], evs => evs = []
  | p :: ps, evs =>
    SeqEnv (ComputeAtCallEnv p.coefficients.length) (NextChunkPolysLoopEnv ps) evs

theorem nextChunkPolysLoopEnv_nonempty :
    ∀ polys : List Poly, ∃ evs, NextChunkPolysLoopEnv polys evs
  | [] => ⟨[], rfl⟩
  | p :: ps => by
    rcases computeAtCallEnv_nonempty p.coefficients.length with ⟨e1, he1⟩
    rcases nextChunkPolysLoopEnv_nonempty ps with ⟨e2, he2⟩
    exact ⟨e1 ++ e2, SeqEnv.append he1 he2⟩

/-- Sequential `ComputeAtCallEnv` envelope parameterized by coefficient lengths (`PolysTail` after
    `points_to_polys`, where `(pointToPolyPure pt).coefficients.length = pt.value.length`). -/
def NextChunkPolysTailByLenEnv : List Nat → List AllocEvent → Prop
  | [], evs => evs = []
  | k :: ks, evs =>
    SeqEnv (ComputeAtCallEnv k) (NextChunkPolysTailByLenEnv ks) evs

theorem nextChunkPolysTailByLenEnv_nonempty :
    ∀ ks : List Nat, ∃ evs, NextChunkPolysTailByLenEnv ks evs
  | [] => ⟨[], rfl⟩
  | k :: ks => by
    rcases computeAtCallEnv_nonempty k with ⟨e1, he1⟩
    rcases nextChunkPolysTailByLenEnv_nonempty ks with ⟨e2, he2⟩
    exact ⟨e1 ++ e2, SeqEnv.append he1 he2⟩

/-- First index `j ∈ [i, i + rem)` with `(pts[j]).value.length ≤ idxNat`, or `i + rem` when every
    point has `idxNat < (pts[j]).value.length` (matching `PointsFast.firstSlowIdxAux`). -/
def nextChunkFirstSlowIdx (idxNat : Nat) (pts : List Point) : Nat → Nat → Nat
  | 0, i => i
  | rem + 1, i =>
    if (pts[i]?.map (·.value.length)).getD 0 ≤ idxNat then
      i
    else
      nextChunkFirstSlowIdx idxNat pts rem (i + 1)

/-- Whether `k` uses one of the precomputed Lagrange basis tables `COMPLETE_POINTS_POLYS_{1,3,5,30,34,36}`. -/
def isPrecomputedBasisLen (k : Nat) : Bool :=
  k == 1 || k == 3 || k == 5 || k == 30 || k == 34 || k == 36

/-- Repeated `SeqEnv` composition of `n` identical step envelopes `E`. -/
def RepeatSeqEnv : Nat → (List AllocEvent → Prop) → List AllocEvent → Prop
  | 0, _, evs => evs = []
  | n + 1, E, evs => SeqEnv E (RepeatSeqEnv n E) evs

theorem repeatSeqEnv_nonempty {E : List AllocEvent → Prop} (hE : ∃ evs, E evs) :
    ∀ n : Nat, ∃ evs, RepeatSeqEnv n E evs
  | 0 => ⟨[], rfl⟩
  | n + 1 => by
    rcases hE with ⟨e1, he1⟩
    rcases repeatSeqEnv_nonempty ⟨e1, he1⟩ n with ⟨e2, he2⟩
    exact ⟨e1 ++ e2, SeqEnv.append he1 he2⟩

/-- Block A initialization allocations before `points_to_polys`: `16` stack slots initialized with
    `Poly::zero()` (`__rust_alloc(2, 2)` each). -/
def nextChunkBlockAEvents : List AllocEvent :=
  (List.replicate 16 (rustAllocEvents 2 2)).flatten

/-- Event envelope of one `lagrange_sum` iteration on degree `k`: clones `basis[m]` (`2 * k` bytes,
    align `2`) and frees the temporary clone (`FreeOnlyEvs`). -/
def LagrangeSumStepEnv (k : Nat) : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents (2 * k) 2) FreeOnlyEvs

theorem lagrangeSumStepEnv_nonempty (k : Nat) : ∃ evs, LagrangeSumStepEnv k evs :=
  ⟨rustAllocEvents (2 * k) 2, Or.inl rfl⟩

/-- Event envelope of one fallback basis-construction iteration on `k` points:
    `lagrange_interpolate_prepare` (`2 * (k + 1)` bytes, align `2`), output polynomial allocation
    (`2 * k` bytes, align `2`), and `FreeOnlyEvs` (`__rust_dealloc` of `prepPtr`). -/
def FallbackBasisStepEnv (k : Nat) : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents (2 * (k + 1)) 2 ++ rustAllocEvents (2 * k) 2) FreeOnlyEvs

theorem fallbackBasisStepEnv_nonempty (k : Nat) : ∃ evs, FallbackBasisStepEnv k evs :=
  ⟨rustAllocEvents (2 * (k + 1)) 2 ++ rustAllocEvents (2 * k) 2, Or.inl rfl⟩

/-- Event envelope of one `points_to_polys` iteration on a `Point` with `k = pt.value.length`
    samples (`+976 .. +4088`):
    - `k = 0`: only `cleanupIter` (`FreeOnlyEvs`);
    - `k ∈ {1, 3, 5, 30, 34, 36}`: `ptVec` (`4 * k`, align `2`), `basisVec` (`24 * k`, align `8`),
      `k` basis clones + `acc` (`(k + 1)` allocations of `(2 * k, 2)`), `k` `LagrangeSumStepEnv k`
      steps, and `FreeOnlyEvs` (`basis` + old slot + `ptVec` deallocations);
    - fallback `k > 0`: `ptVec` (`4 * k`, align `2`), `ones` (`4 * k`, align `2`), `basisVec`
      (`24 * k`, align `8`), `k` `FallbackBasisStepEnv k` steps, `acc` (`2 * k`, align `2`) +
      `ones` dealloc, `k` `LagrangeSumStepEnv k` steps, and `FreeOnlyEvs`. -/
def PointsToPolysIterEnv (k : Nat) (evs : List AllocEvent) : Prop :=
  if k = 0 then
    FreeOnlyEvs evs
  else if isPrecomputedBasisLen k then
    SeqEnv
      (· = rustAllocEvents (4 * k) 2 ++
            rustAllocEvents (24 * k) 8 ++
            (List.replicate (k + 1) (rustAllocEvents (2 * k) 2)).flatten)
      (SeqEnv (RepeatSeqEnv k (LagrangeSumStepEnv k)) FreeOnlyEvs)
      evs
  else
    SeqEnv
      (· = rustAllocEvents (4 * k) 2 ++
            rustAllocEvents (4 * k) 2 ++
            rustAllocEvents (24 * k) 8)
      (SeqEnv (RepeatSeqEnv k (FallbackBasisStepEnv k))
        (SeqEnv (SeqEnv (· = rustAllocEvents (2 * k) 2) FreeOnlyEvs)
          (SeqEnv (RepeatSeqEnv k (LagrangeSumStepEnv k)) FreeOnlyEvs)))
      evs

theorem pointsToPolysIterEnv_nonempty (k : Nat) :
    ∃ evs, PointsToPolysIterEnv k evs := by
  unfold PointsToPolysIterEnv
  split
  · exact ⟨[], FreeOnlyEvs.nil⟩
  · split
    · rcases repeatSeqEnv_nonempty (lagrangeSumStepEnv_nonempty k) k with ⟨es, hes⟩
      refine ⟨(rustAllocEvents (4 * k) 2 ++ rustAllocEvents (24 * k) 8 ++
        (List.replicate (k + 1) (rustAllocEvents (2 * k) 2)).flatten) ++ es, ?_⟩
      exact SeqEnv.append rfl (Or.inl hes)
    · rcases repeatSeqEnv_nonempty (fallbackBasisStepEnv_nonempty k) k with ⟨ef, hef⟩
      rcases repeatSeqEnv_nonempty (lagrangeSumStepEnv_nonempty k) k with ⟨es, hes⟩
      refine ⟨(rustAllocEvents (4 * k) 2 ++ rustAllocEvents (4 * k) 2 ++
        rustAllocEvents (24 * k) 8) ++ (ef ++ (rustAllocEvents (2 * k) 2 ++ es)), ?_⟩
      exact SeqEnv.append rfl
        (SeqEnv.append hef
          (SeqEnv.append (Or.inl rfl) (Or.inl hes)))

/-- Sequential `PointsToPolysIterEnv` envelope across `pts` (`points_to_polys` loop). -/
def PointsToPolysLoopEnv : List Point → List AllocEvent → Prop
  | [], evs => evs = []
  | pt :: pts, evs =>
    SeqEnv (PointsToPolysIterEnv pt.value.length) (PointsToPolysLoopEnv pts) evs

theorem pointsToPolysLoopEnv_nonempty :
    ∀ pts : List Point, ∃ evs, PointsToPolysLoopEnv pts evs
  | [] => ⟨[], rfl⟩
  | pt :: pts => by
    rcases pointsToPolysIterEnv_nonempty pt.value.length with ⟨e1, he1⟩
    rcases pointsToPolysLoopEnv_nonempty pts with ⟨e2, he2⟩
    exact ⟨e1 ++ e2, SeqEnv.append he1 he2⟩

/-- Exact path-disjunctive `AllocEvent` envelope of
    `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (`0x6a384`,
    Block `416`):
    - `.polys polys`: `NextChunkPrologueEnv`, `NextChunkPolysLoopEnv polys`, `NextChunkEpilogueEnv`;
    - `.points pts` fast path (`firstSlowIdx = 16`): `nextChunkPrologueEvents ++ nextChunkEpilogueEvents`;
    - `.points pts` slow path (`i0 = firstSlowIdx < 16`): `NextChunkPrologueEnv`,
      `nextChunkBlockAEvents`, `PointsToPolysLoopEnv pts`, Block C `FreeOnlyEvs`,
      `NextChunkPolysTailByLenEnv ((pts.drop i0).map (·.value.length))`, `NextChunkEpilogueEnv`. -/
def PolyNextChunkEnv (x : PolyNextChunkGhost) (evs : List AllocEvent) : Prop :=
  match x.enc.s with
  | .polys polys =>
    SeqEnv NextChunkPrologueEnv
      (SeqEnv (NextChunkPolysLoopEnv polys) NextChunkEpilogueEnv) evs
  | .points pts =>
    let i0 := nextChunkFirstSlowIdx (x.enc.idx.setWidth 16).toNat pts 16 0
    if i0 < 16 then
      SeqEnv NextChunkPrologueEnv
        (SeqEnv (· = nextChunkBlockAEvents)
          (SeqEnv (PointsToPolysLoopEnv pts)
            (SeqEnv FreeOnlyEvs
              (SeqEnv (NextChunkPolysTailByLenEnv ((pts.drop i0).map (·.value.length)))
                NextChunkEpilogueEnv)))) evs
    else
      evs = nextChunkPrologueEvents ++ nextChunkEpilogueEvents

theorem polyNextChunkEnv_nonempty (x : PolyNextChunkGhost) :
    ∃ evs, PolyNextChunkEnv x evs := by
  unfold PolyNextChunkEnv
  cases x.enc.s with
  | polys polys =>
    rcases nextChunkPolysLoopEnv_nonempty polys with ⟨em, hem⟩
    exact ⟨nextChunkPrologueEvents ++ (em ++ nextChunkEpilogueEvents),
      SeqEnv.append rfl (SeqEnv.append hem rfl)⟩
  | points pts =>
    dsimp only
    split
    · rename_i hi0
      rcases pointsToPolysLoopEnv_nonempty pts with ⟨ep, hep⟩
      rcases nextChunkPolysTailByLenEnv_nonempty
        ((pts.drop (nextChunkFirstSlowIdx (x.enc.idx.setWidth 16).toNat pts 16 0)).map
          (·.value.length)) with ⟨et, het⟩
      refine ⟨nextChunkPrologueEvents ++
        (nextChunkBlockAEvents ++ (ep ++ ([] ++ (et ++ nextChunkEpilogueEvents)))), ?_⟩
      exact SeqEnv.append rfl
        (SeqEnv.append rfl
          (SeqEnv.append hep
            (SeqEnv.append FreeOnlyEvs.nil
              (SeqEnv.append het rfl))))
    · exact ⟨nextChunkPrologueEvents ++ nextChunkEpilogueEvents, rfl⟩

/-! ## 2. Fixed-Base Budget-Threaded Specifications and Contracts (`b : BitVec 64`) -/

/-- Parametric-envelope fixed-base budget specification of
    `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (`0x6a384`,
    `onPanic = ⌜False⌝`). -/
def polyNextChunkSpecOfEnv
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) : Spec (PolyNextChunkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.encA ∧
      x.enc.nextChunk = .ok (x.enc', x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA chunkSize ∗
      polyEncoderAt A.repAlloc x.encA x.enc ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp polyNextChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜Env x evs ∧ sf.trace = s0.trace⌝ ∗
      chunkAt x.outA x.chunk ∗
      polyEncoderAt A.repAlloc x.encA x.enc' ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp polyNextChunkStack

/-- Canonical fixed-base budget specification of `<PolyEncoder as Encoder>::next_chunk` (`0x6a384`)
    instantiated at `PolyNextChunkEnv`. -/
abbrev polyNextChunkSpec
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) : Spec (PolyNextChunkGhost × M.σ) :=
  polyNextChunkSpecOfEnv PolyNextChunkEnv M A lim b

/-- Parametric-envelope fixed-base budget specification extended with `completePointsPolysAt b` in
    `pre` (`Proof.lean` entry form before `.rodata` extraction). -/
def polyNextChunkRodataSpecOfEnv
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) : Spec (PolyNextChunkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.encA ∧
      x.enc.nextChunk = .ok (x.enc', x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA chunkSize ∗
      polyEncoderAt A.repAlloc x.encA x.enc ∗
      completePointsPolysAt b ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp polyNextChunkStack
  post := (polyNextChunkSpecOfEnv Env M A lim b).post

/-- Canonical fixed-base rodata budget specification of `<PolyEncoder as Encoder>::next_chunk`. -/
abbrev polyNextChunkRodataSpec
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) : Spec (PolyNextChunkGhost × M.σ) :=
  polyNextChunkRodataSpecOfEnv PolyNextChunkEnv M A lim b

/-- Fixed-base rodata contract abbreviation for `<PolyEncoder as Encoder>::next_chunk`. -/
def PolyNextChunkRodataOkExt
    (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr polyNextChunkName)
    (polyNextChunkRodataSpec M A lim b)

/-- Fixed-base `.inImage img` contract abbreviation for `<PolyEncoder as Encoder>::next_chunk`. -/
def PolyNextChunkOkX
    (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyNextChunkName)
      ((polyNextChunkSpec M A lim img.base).inImage img)

/-! ## 3. Relocatable `[LibsignalPlacement]` Budget-Threaded Specifications (Block `416`) -/

/-- Parametric-envelope relocatable `[LibsignalPlacement]` budget specification of
    `<PolyEncoder as Encoder>::next_chunk` (Block `416`, `onPanic = ⌜False⌝`). -/
def polyNextChunkPlacedSpecOfEnv [LibsignalPlacement]
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PolyNextChunkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.encA ∧
      x.enc.nextChunk = .ok (x.enc', x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA chunkSize ∗
      polyEncoderAt A.repAlloc x.encA x.enc ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp polyNextChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜Env x evs ∧ sf.trace = s0.trace⌝ ∗
      chunkAt x.outA x.chunk ∗
      polyEncoderAt A.repAlloc x.encA x.enc' ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp polyNextChunkStack

/-- Canonical relocatable `[LibsignalPlacement]` budget specification of
    `<PolyEncoder as Encoder>::next_chunk` (Block `416`) instantiated at `PolyNextChunkEnv`. -/
abbrev polyNextChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PolyNextChunkGhost × M.σ) :=
  polyNextChunkPlacedSpecOfEnv PolyNextChunkEnv M A lim

/-- Parametric-envelope relocatable `[LibsignalPlacement]` budget specification extended with
    `completePointsPolysPlacedAt` in `pre`. -/
def polyNextChunkRodataPlacedSpecOfEnv [LibsignalPlacement]
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PolyNextChunkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.encA ∧
      x.enc.nextChunk = .ok (x.enc', x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA chunkSize ∗
      polyEncoderAt A.repAlloc x.encA x.enc ∗
      completePointsPolysPlacedAt ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp polyNextChunkStack
  post := (polyNextChunkPlacedSpecOfEnv Env M A lim).post

/-- Canonical relocatable rodata budget specification of `<PolyEncoder as Encoder>::next_chunk`. -/
abbrev polyNextChunkRodataPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PolyNextChunkGhost × M.σ) :=
  polyNextChunkRodataPlacedSpecOfEnv PolyNextChunkEnv M A lim

/-- Parametric-envelope relocatable `[LibsignalPlacement]` contract for
    `<PolyEncoder as Encoder>::next_chunk` (Block `416`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
def PolyNextChunkPlacedOkExtOfEnv [LibsignalPlacement]
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
    (blkPl_416).base
    (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpecOfEnv Env M A lim))

/-- Canonical relocatable `[LibsignalPlacement]` contract for
    `<PolyEncoder as Encoder>::next_chunk` (Block `416`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
abbrev PolyNextChunkPlacedOkExt [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyNextChunkPlacedOkExtOfEnv PolyNextChunkEnv M A lim ext

/-- Parametric-envelope relocatable rodata `[LibsignalPlacement]` contract for Block `416`. -/
def PolyNextChunkRodataPlacedOkExtOfEnv [LibsignalPlacement]
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
    (blkPl_416).base
    (withLsCodeRoLoaded lsmpl (polyNextChunkRodataPlacedSpecOfEnv Env M A lim))

/-- Canonical relocatable rodata `[LibsignalPlacement]` contract for Block `416`. -/
abbrev PolyNextChunkRodataPlacedOkExt [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyNextChunkRodataPlacedOkExtOfEnv PolyNextChunkEnv M A lim ext

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
