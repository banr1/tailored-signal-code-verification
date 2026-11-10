/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExact
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Exact-Capacity Specifications for `PolynomialDecoder::encode` (`[local#2]`)

Defines `encodePolyDecoderExactSpecOf` under `RustCliAllocBudget M`, the pool-free `0`-allocation
(`VmPreserved`) contracts `encodePolyDecoderExactVmSpecOf`, `encodePolyEncoderExactVmSpecOf`,
`encodeRepeated59ExactVmSpecOf`, and `encodeVarintExactVmSpecOf`, and framing lemmas lifting
them to `A.pool lim st`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedBytes encodeRepeatedStackOf repeatedBytesSliceAt)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialDecoderPinnedAt protoPolynomialEncoderPinnedAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyDecoderPinnedGhost EncodePolyEncoderPinnedGhost
   encodePolyDecoderMsg encodePolyEncoderMsg msgEnc48RepeatedStackOf)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodePolyEncoderExactSpecOf encodeRepeated59ExactSpecOf)

/-! ## 1. Budget-Threaded Exact-Capacity `encodePolyDecoderExactSpecOf` -/

/-- Exact-capacity budget specification of `PolynomialDecoder::encode`:
    when `x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat`, zero allocations
    occur and `A.pool lim st` is preserved unchanged (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encodePolyDecoderExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyDecoderPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
      protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-! ## 2. Pool-Free `0`-Allocation (`VmPreserved`) Exact-Capacity Contracts -/

/-- Pool-free `0`-allocation (`VmPreserved`) contract for `encode_varint` under exact capacity
    (`x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat`). -/
def encodeVarintExactVmSpecOf (resStack : Nat) (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (0x30 + resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
      stackAt s0.sp (0x30 + resStack)

/-- Pool-free `0`-allocation (`VmPreserved`) contract for `encode_repeated` (`elems.length < 2 ^ 59`)
    under exact capacity (`x.bs.length + (encodeRepeatedBytes ...).length ≤ x.cap.toNat`). -/
def encodeRepeated59ExactVmSpecOf (resStack : Nat) (A : RustAlloc) : Spec EncodeRepeatedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = BitVec.ofNat 32 x.tag ∧
      s.readReg64 .x1 = x.base ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.elems.length ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag ∧ x.tag < 2 ^ 29 ∧
      x.elems.length < 2 ^ 59 ∧
      x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt s.sp (encodeRepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A x.v x.cap x.ptr
        (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd)) ∗
      stackAt s0.sp (encodeRepeatedStackOf resStack)

/-- Pool-free `0`-allocation (`VmPreserved`) contract for `PolynomialDecoder::encode` under exact
    capacity (`x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat`). -/
def encodePolyDecoderExactVmSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyDecoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
      protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-- Pool-free `0`-allocation (`VmPreserved`) contract for `PolynomialEncoder::encode` under exact
    capacity (`x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat`). -/
def encodePolyEncoderExactVmSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyEncoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat⌝ ∗
      protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-! ## 3. Pool-Framing Bridges (`VmPreserved` → `A.pool lim st`) -/

theorem subroutine_ok_encodePolyDecoderExact_of_vm {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (encodePolyDecoderExactVmSpecOf resStack A.repAlloc)) :
    subroutine_ok prog entry (encodePolyDecoderExactSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodePolyDecoderExactSpecOf] at hpre
  have hpre' : s0.mem ⊨
      (encodePolyDecoderExactVmSpecOf resStack A.repAlloc).pre x s0 ∗ (A.pool lim st s0 ∗ R) := by
    dsimp only [encodePolyDecoderExactVmSpecOf]
    convert hpre using 1; sep_ac_rfl
  refine (h.to_outcome x (A.pool lim st s0 ∗ R) s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodePolyDecoderExactVmSpecOf] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hvm, htr⟩, hq⟩
    rw [← A.pool_of_vmPreserved hvm] at hq
    dsimp only [encodePolyDecoderExactSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, by convert hq using 1; sep_ac_rfl⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem subroutine_ok_encodePolyEncoderExact_of_vm {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (encodePolyEncoderExactVmSpecOf resStack A.repAlloc)) :
    subroutine_ok prog entry (encodePolyEncoderExactSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodePolyEncoderExactSpecOf] at hpre
  have hpre' : s0.mem ⊨
      (encodePolyEncoderExactVmSpecOf resStack A.repAlloc).pre x s0 ∗ (A.pool lim st s0 ∗ R) := by
    dsimp only [encodePolyEncoderExactVmSpecOf]
    convert hpre using 1; sep_ac_rfl
  refine (h.to_outcome x (A.pool lim st s0 ∗ R) s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodePolyEncoderExactVmSpecOf] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hvm, htr⟩, hq⟩
    rw [← A.pool_of_vmPreserved hvm] at hq
    dsimp only [encodePolyEncoderExactSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, by convert hq using 1; sep_ac_rfl⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem subroutine_ok_encodeRepeated59Exact_of_vm {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (encodeRepeated59ExactVmSpecOf resStack A.repAlloc)) :
    subroutine_ok prog entry (encodeRepeated59ExactSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodeRepeated59ExactSpecOf] at hpre
  have hpre' : s0.mem ⊨
      (encodeRepeated59ExactVmSpecOf resStack A.repAlloc).pre x s0 ∗ (A.pool lim st s0 ∗ R) := by
    dsimp only [encodeRepeated59ExactVmSpecOf]
    convert hpre using 1; sep_ac_rfl
  refine (h.to_outcome x (A.pool lim st s0 ∗ R) s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeRepeated59ExactVmSpecOf] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hvm, htr⟩, hq⟩
    rw [← A.pool_of_vmPreserved hvm] at hq
    dsimp only [encodeRepeated59ExactSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, by convert hq using 1; sep_ac_rfl⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm [LibsignalPlacement]
    {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf resStack A.repAlloc))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded, encodePolyDecoderExactSpecOf] at hpre
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf resStack A.repAlloc)).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [withLsCodeLoaded, encodePolyDecoderExactVmSpecOf]
    convert hpre using 1; sep_ac_rfl
  refine (h.to_outcome x (A.pool lim st s0 ∗ R) s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodePolyDecoderExactVmSpecOf] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hvm, htr⟩, hq⟩
    rw [← A.pool_of_vmPreserved hvm] at hq
    dsimp only [withLsCodeLoaded, encodePolyDecoderExactSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, by convert hq using 1; sep_ac_rfl⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm [LibsignalPlacement]
    {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf resStack A.repAlloc))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded, encodePolyEncoderExactSpecOf] at hpre
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf resStack A.repAlloc)).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [withLsCodeLoaded, encodePolyEncoderExactVmSpecOf]
    convert hpre using 1; sep_ac_rfl
  refine (h.to_outcome x (A.pool lim st s0 ∗ R) s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodePolyEncoderExactVmSpecOf] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hvm, htr⟩, hq⟩
    rw [← A.pool_of_vmPreserved hvm] at hq
    dsimp only [withLsCodeLoaded, encodePolyEncoderExactSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, by convert hq using 1; sep_ac_rfl⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget

