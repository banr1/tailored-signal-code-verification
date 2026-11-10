/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBase
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Shared Specifications for `PolynomialEncoder::encode`

Defines `VmPreserved`-strengthened `polynomialEncoderEncodedLenElemsOutSpec`, the deterministic
allocator event list `encodePolyEncoderEvents` and envelope `EncodePolyEncoderEnv`, and
budget-threaded pinned/unpinned contracts for `PolynomialEncoder::encode` (`[local#1, 2]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeUint32Field)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Poly (ProtoPolynomialEncoderGhost)
open CryptoVerification.SpqrV1.Varint (encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyEncoderGhost EncodePolyEncoderPinnedGhost
   PolynomialEncoderEncodedLenPinnedGhost
   encodePolyEncoderMsg encodePolyEncoderMsg_len_split msgEnc48RepeatedStackOf
   polyEncodedLenStack polyEncoderElemsAt polyEncoderHeaderBytes polyEncoderRestAt
   polynomialEncoderPBEncodedLen protoPolynomialEncoderAt_eq_exists_pinned
   satisfies_protoPolynomialEncoderPinnedAt_iff)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (encodeRepeatedStep encodeRepeatedStep_of_spare pushBytesStep pushBytesStep_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget
  (polynomialEncoderEncodedLenPinnedSpec)

/-! ## 1. `VmPreserved`-Strengthened `polynomialEncoderEncodedLenElemsOutSpec` -/

/-- `VmPreserved`-strengthened variant of `polynomialEncoderEncodedLenPinnedSpec` whose
    postcondition exposes `polyEncoderElemsAt` and `polyEncoderRestAt` for field encoding. -/
def polynomialEncoderEncodedLenElemsOutSpec (A : RustAlloc) :
    Spec PolynomialEncoderEncodedLenPinnedGhost where
  pre := (polynomialEncoderEncodedLenPinnedSpec A).pre
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf⌝ ∗
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen x.m) ∧
          sf.trace = s0.trace⌝ ∗
        (∃∗ ptsElems : List (BitVec 64 × List (BitVec 8)),
         ∃∗ polysElems : List (BitVec 64 × List (BitVec 8)),
          ⌜ptsElems.map Prod.snd = x.m.pts ∧ x.m.pts.length * 24 < 2 ^ 63 ∧
            polysElems.map Prod.snd = x.m.polys ∧ x.m.polys.length * 24 < 2 ^ 63⌝ ∗
          polyEncoderElemsAt x.a x.g x.m ptsElems polysElems ∗
          polyEncoderRestAt A x.a x.g ptsElems polysElems) ∗
        stackAt s0.sp polyEncodedLenStack)

theorem subroutine_ok_polyEncLenElemsOut_of_pinned {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (hok : subroutine_ok prog entry (polynomialEncoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialEncoderEncodedLenElemsOutSpec A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (hok.to_outcome x R s0 hpc hrun hpre hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [polynomialEncoderEncodedLenPinnedSpec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialEncoderEncodedLenPinnedSpec] at hq
    dsimp only [polynomialEncoderEncodedLenElemsOutSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨hvm, hq⟩ := hq
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨hpure, hq_mem⟩ := hq
    refine ⟨hpure, ?_⟩
    have hq_mem' : sf.mem ⊨ CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderPinnedAt A x.g x.a x.m ∗
        (stackAt s0.sp polyEncodedLenStack ∗ R) := by
      convert hq_mem using 1; sep_ac_rfl
    obtain ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm_unp⟩ :=
      (satisfies_protoPolynomialEncoderPinnedAt_iff A x.g x.a x.m _ sf.mem).mp hq_mem'
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ptsElems, polysElems, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hpts_eq, hpts_lt, hpolys_eq, hpolys_lt⟩, ?_⟩
    convert hm_unp using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## 2. Deterministic Allocator Events & Budget Contracts for `PolynomialEncoder::encode` -/

def encodePolyEncoderPinnedToUnpinned (x : EncodePolyEncoderPinnedGhost) :
    EncodePolyEncoderGhost :=
  ⟨x.encA, x.enc, x.v, x.cap, x.ptr, x.bs⟩

/-- Deterministic `AllocEvent` list emitted by `PolynomialEncoder::encode` on `x`. -/
def encodePolyEncoderEvents (x : EncodePolyEncoderGhost) : List AllocEvent :=
  let hdrLen := (polyEncoderHeaderBytes x.enc).length
  let s1 := pushBytesStep hdrLen x.cap.toNat x.bs.length
  let idxLen := (encodeUint32Field 1#32 x.enc.idx).length
  let s2 := pushBytesStep idxLen s1.1 (x.bs.length + hdrLen)
  let ptsLen := (encodeRepeatedBytes 2 x.enc.pts).length
  let s3 := encodeRepeatedStep 2 s2.1 (x.bs.length + hdrLen + idxLen) x.enc.pts
  let s4 := encodeRepeatedStep 3 s3.1 (x.bs.length + hdrLen + idxLen + ptsLen) x.enc.polys
  s1.2 ++ s2.2 ++ s3.2 ++ s4.2

/-- Callee-fixed allocator event envelope of `PolynomialEncoder::encode`. -/
def EncodePolyEncoderEnv (x : EncodePolyEncoderGhost) (evs : List AllocEvent) : Prop :=
  evs = encodePolyEncoderEvents x

theorem encodePolyEncoderEvents_of_spare {x : EncodePolyEncoderGhost}
    (h : x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat) :
    encodePolyEncoderEvents x = [] := by
  rw [encodePolyEncoderMsg_len_split] at h
  dsimp only [encodePolyEncoderEvents]
  have hs1 : pushBytesStep (polyEncoderHeaderBytes x.enc).length x.cap.toNat x.bs.length =
      (x.cap.toNat, []) :=
    pushBytesStep_of_spare _ _ _ (by omega)
  rw [hs1]
  have hs2 : pushBytesStep (encodeUint32Field 1#32 x.enc.idx).length x.cap.toNat
      (x.bs.length + (polyEncoderHeaderBytes x.enc).length) = (x.cap.toNat, []) :=
    pushBytesStep_of_spare _ _ _ (by omega)
  rw [hs2]
  have hs3 : encodeRepeatedStep 2 x.cap.toNat
      (x.bs.length + (polyEncoderHeaderBytes x.enc).length +
        (encodeUint32Field 1#32 x.enc.idx).length) x.enc.pts = (x.cap.toNat, []) :=
    encodeRepeatedStep_of_spare 2 _ _ _ (by omega)
  rw [hs3]
  have hs4 : encodeRepeatedStep 3 x.cap.toNat
      (x.bs.length + (polyEncoderHeaderBytes x.enc).length +
        (encodeUint32Field 1#32 x.enc.idx).length +
        (encodeRepeatedBytes 2 x.enc.pts).length) x.enc.polys = (x.cap.toNat, []) :=
    encodeRepeatedStep_of_spare 3 _ _ _ (by omega)
  rw [hs4]
  rfl

/-- Pinned budget specification of `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`
    parameterized by `resStack` and `Env`. -/
def encodePolyEncoderPinnedSpecOfEnv (resStack : Nat)
    (Env : EncodePolyEncoderGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.enc.pts.length < 2 ^ 58 ∧
      x.enc.polys.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyEncoderMsg x.enc).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env (encodePolyEncoderPinnedToUnpinned x))⌝ ∗
      CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
      (∃∗ evs : List AllocEvent, ⌜Env (encodePolyEncoderPinnedToUnpinned x) evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-- Unpinned budget specification of `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`
    parameterized by `resStack` and `Env`. -/
def encodePolyEncoderSpecOfEnv (resStack : Nat)
    (Env : EncodePolyEncoderGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.enc.pts.length < 2 ^ 58 ∧
      x.enc.polys.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyEncoderMsg x.enc).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderAt A.repAlloc x.encA x.enc ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderAt A.repAlloc x.encA x.enc ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
      (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-- Pinned budget specification of `PolynomialEncoder::encode` at `EncodePolyEncoderEnv`. -/
abbrev encodePolyEncoderPinnedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderPinnedGhost × M.σ) :=
  encodePolyEncoderPinnedSpecOfEnv resStack EncodePolyEncoderEnv A lim

/-- Unpinned budget specification of `PolynomialEncoder::encode` at `EncodePolyEncoderEnv`. -/
abbrev encodePolyEncoderSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderGhost × M.σ) :=
  encodePolyEncoderSpecOfEnv resStack EncodePolyEncoderEnv A lim

abbrev encodePolyEncoderPinnedSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderPinnedGhost × M.σ) :=
  encodePolyEncoderPinnedSpecOf doReserveStack A lim

abbrev encodePolyEncoderSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderGhost × M.σ) :=
  encodePolyEncoderSpecOf doReserveStack A lim

abbrev encodePolyEncoderPinnedSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderPinnedGhost × M.σ) :=
  encodePolyEncoderPinnedSpecOf doReserveStackX A lim

abbrev encodePolyEncoderSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderGhost × M.σ) :=
  encodePolyEncoderSpecOf doReserveStackX A lim

theorem polyEncoder_post_unpinned_of_pinned_env {resStack : Nat}
    {Env : EncodePolyEncoderGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : EncodePolyEncoderGhost} {st : M.σ} {g : ProtoPolynomialEncoderGhost}
    {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (encodePolyEncoderPinnedSpecOfEnv resStack Env A lim).post
      (⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩, st) s0 sf ∗ R) :
    sf.mem ⊨ (encodePolyEncoderSpecOfEnv resStack Env A lim).post (x, st) s0 sf ∗ R := by
  dsimp only [encodePolyEncoderPinnedSpecOfEnv, encodePolyEncoderPinnedToUnpinned] at hq
  dsimp only [encodePolyEncoderSpecOfEnv]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
    (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗
      A.pool lim (M.stepEvents evs st) sf) ∗
    stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderPinnedAt
      A.repAlloc g x.encA x.enc ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; sep_ac_rfl
  have hgoal : sf.mem ⊨ CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderAt
      A.repAlloc x.encA x.enc ∗ Rest := by
    rw [protoPolynomialEncoderAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; sep_ac_rfl

theorem polyEncoder_unpinned_of_pinned_env {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {Env : EncodePolyEncoderGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry (encodePolyEncoderPinnedSpecOfEnv resStack Env A lim)) :
    subroutine_ok prog entry (encodePolyEncoderSpecOfEnv resStack Env A lim) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [encodePolyEncoderSpecOfEnv] at hpre
  rw [protoPolynomialEncoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome (⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩, st)
    R s0 hpc hrun hpre hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, polyEncoder_post_unpinned_of_pinned_env hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem polyEncoder_post_unpinned_of_pinned {resStack : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : EncodePolyEncoderGhost} {st : M.σ} {g : ProtoPolynomialEncoderGhost}
    {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (encodePolyEncoderPinnedSpecOf resStack A lim).post
      (⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩, st) s0 sf ∗ R) :
    sf.mem ⊨ (encodePolyEncoderSpecOf resStack A lim).post (x, st) s0 sf ∗ R :=
  polyEncoder_post_unpinned_of_pinned_env hq

theorem polyEncoder_unpinned_of_pinned {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry (encodePolyEncoderPinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry (encodePolyEncoderSpecOf resStack A lim) :=
  polyEncoder_unpinned_of_pinned_env hpinned

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
