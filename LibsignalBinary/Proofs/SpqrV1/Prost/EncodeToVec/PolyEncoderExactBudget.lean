/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExact
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Exact-Capacity Specifications for `encode_repeated` (`< 2 ^ 59`) & `PolynomialEncoder::encode`

Defines the allocator event envelope `EncodeRepeatedEnv` and budget-threaded contracts
`encodeRepeated59SpecOfEnv`, `encodeRepeated59SpecOf`, `encodeRepeated59ExactSpecOf`, and
`encodePolyEncoderExactSpecOf`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedBytes encodeRepeatedStackOf repeatedBytesSliceAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyEncoderPinnedGhost encodePolyEncoderMsg msgEnc48RepeatedStackOf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (encodeRepeatedStep encodeRepeatedStep_of_spare)

/-! ## 1. Budget-Threaded `encodeRepeated59SpecOf` (`elems.length < 2 ^ 59`) -/

/-- Deterministic `AllocEvent` list emitted by `prost::encoding::bytes::encode_repeated` on `x`. -/
def encodeRepeatedEvents (x : EncodeRepeatedGhost) : List AllocEvent :=
  (encodeRepeatedStep x.tag x.cap.toNat x.bs.length (x.elems.map Prod.snd)).2

/-- Callee-fixed allocator event envelope of `encode_repeated`. -/
def EncodeRepeatedEnv (x : EncodeRepeatedGhost) (evs : List AllocEvent) : Prop :=
  evs = encodeRepeatedEvents x

theorem encodeRepeatedEvents_of_spare {x : EncodeRepeatedGhost}
    (h : x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat) :
    encodeRepeatedEvents x = [] := by
  dsimp only [encodeRepeatedEvents]
  rw [encodeRepeatedStep_of_spare x.tag x.cap.toNat x.bs.length (x.elems.map Prod.snd) h]

/-- Envelope-parameterized budget contract of `encode_repeated` with `elems.length < 2 ^ 59`. -/
def encodeRepeated59SpecOfEnv (resStack : Nat)
    (Env : EncodeRepeatedGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeRepeatedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = BitVec.ofNat 32 x.tag ∧
      s.readReg64 .x1 = x.base ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.elems.length ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag ∧ x.tag < 2 ^ 29 ∧
      x.elems.length < 2 ^ 59 ∧
      (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeRepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr'
            (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd))) ∗
      (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (encodeRepeatedStackOf resStack)

/-- Budget contract of `encode_repeated` (`elems.length < 2 ^ 59`) at `EncodeRepeatedEnv`. -/
abbrev encodeRepeated59SpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeRepeatedGhost × M.σ) :=
  encodeRepeated59SpecOfEnv resStack EncodeRepeatedEnv A lim

/-- Exact-capacity (`0`-allocation) specialization of `encodeRepeated59SpecOf`:
    when `x.bs.length + (encodeRepeatedBytes ...).length ≤ x.cap.toNat`, no allocations occur
    and `A.pool lim st` is preserved unchanged. -/
def encodeRepeated59ExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeRepeatedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = BitVec.ofNat 32 x.tag ∧
      s.readReg64 .x1 = x.base ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.elems.length ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag ∧ x.tag < 2 ^ 29 ∧
      x.elems.length < 2 ^ 59 ∧
      x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeRepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A.repAlloc x.v x.cap x.ptr
        (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd)) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (encodeRepeatedStackOf resStack)

theorem subroutine_ok_encodeRepeated59Exact_of_59 {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry (encodeRepeated59SpecOf resStack A lim)) :
    subroutine_ok prog entry (encodeRepeated59ExactSpecOf resStack A lim) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [encodeRepeated59ExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, hmem⟩ := hpre
  have hevs0 : encodeRepeatedEvents x = [] := encodeRepeatedEvents_of_spare hfit
  have hfits : FitsEnv M lim st (EncodeRepeatedEnv x) := by
    unfold EncodeRepeatedEnv
    rw [FitsEnv.eq_iff, hevs0]
    trivial
  have hpre' : s0.mem ⊨ (encodeRepeated59SpecOf resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, Or.inl hfit, hfits⟩, hmem⟩
  refine (hok.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv] at hq
    dsimp only [encodeRepeated59ExactSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨htr, hq⟩ := hq
    refine ⟨htr, ?_⟩
    rw [sepConj_assoc] at hq ⊢
    have hq' : sf.mem ⊨
        (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr'
            (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd))) ∗
        ((∃∗ evs : List AllocEvent, ⌜EncodeRepeatedEnv x evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
        (repeatedBytesSliceAt x.base x.elems ∗
          stackAt s0.sp (encodeRepeatedStackOf resStack) ∗ R)) := by
      convert hq using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq'
    obtain ⟨cap', hq'⟩ := hq'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq'
    obtain ⟨ptr', hq'⟩ := hq'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    obtain ⟨⟨_, hpres⟩, hq'⟩ := hq'
    obtain ⟨rfl, rfl⟩ := hpres hfit
    have hq'' : sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜EncodeRepeatedEnv x evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
        (repeatedBytesSliceAt x.base x.elems ∗
          vecU8At A.repAlloc x.v x.cap x.ptr
            (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd)) ∗
          stackAt s0.sp (encodeRepeatedStackOf resStack) ∗ R) := by
      convert hq' using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq''
    obtain ⟨evs, hq''⟩ := hq''
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq''
    obtain ⟨hevs, hq''⟩ := hq''
    dsimp only [EncodeRepeatedEnv] at hevs
    rw [hevs, hevs0] at hq''
    dsimp only [AllocCostModel.stepEvents] at hq''
    convert hq'' using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## 2. Budget-Threaded Exact-Capacity `encodePolyEncoderExactSpecOf` -/

/-- Exact-capacity budget specification of `PolynomialEncoder::encode`:
    when `x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat`, zero allocations
    occur and `A.pool lim st` is preserved unchanged (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encodePolyEncoderExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyEncoderPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat⌝ ∗
      CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
