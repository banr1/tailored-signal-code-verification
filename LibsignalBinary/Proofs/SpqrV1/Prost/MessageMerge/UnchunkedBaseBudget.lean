/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBase
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Own-Stack Specs & Bridges for `Unchunked.{Ct1Sent,EkSentCt1Received}::merge`

Defines `RustCliAllocBudget`-threaded own-stack contracts
`unchunked{Ct1Sent,EkSentCt1Received}MergeOwnSpec{OfEnv,}` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`)
and proves their frame-lifting bridges to `ChunkedDefsBudget.unchunked{Ct1Sent,EkSentCt1Received}MergeSpec{OfEnv,}`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (UnchunkedCt1SentMergeEnv UnchunkedCt1SentMergePostEnv
   unchunkedCt1SentMergeSpecOfEnv unchunkedCt1SentMergeSpec
   UnchunkedEkSentCt1ReceivedMergeEnv UnchunkedEkSentCt1ReceivedMergePostEnv
   unchunkedEkSentCt1ReceivedMergeSpecOfEnv unchunkedEkSentCt1ReceivedMergeSpec)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Drop
  (optProtoAuthenticatorAt protoUnchunkedCt1SentAt protoUnchunkedEkSentCt1ReceivedAt)
open CryptoVerification.SpqrV1.ProtoRepr
  (ct1SentPBAt ekSentCt1ReceivedPBAt optAuthenticatorPBAt rustBytesVecAt unchunked4At unchunked5At)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost UnchunkedEkSentCt1ReceivedMergeGhost unchunkedMergeStack)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (codecWireTypeToProto optAuthenticatorPBCapAt optProtoAuthenticatorCapAt
   protoUnchunkedCt1SentCapAt protoUnchunkedEkSentCt1ReceivedCapAt
   stackAt_unchunkedMergeStack_eq_own unchunkedCt1SentPBCapAt
   unchunkedEkSentCt1ReceivedPBCapAt unchunkedOwnStack vecU8CapAt)

/-! ## 1. 112-Byte Own-Stack Budget Contracts -/

/-- Envelope-parameterized 112-byte-frame contract of `Unchunked.Ct1Sent::merge`. -/
def unchunkedCt1SentMergeOwnSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : UnchunkedCt1SentMergeGhost → List AllocEvent → Prop) :
    Spec (UnchunkedCt1SentMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedOwnStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp unchunkedOwnStack ∗
      match (mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Unchunked.Ct1Sent, protoUnchunkedCt1SentAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded 112-byte-frame contract of `Unchunked.Ct1Sent::merge`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def unchunkedCt1SentMergeOwnSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (UnchunkedCt1SentMergeGhost × M.σ) :=
  unchunkedCt1SentMergeOwnSpecOfEnv A lim
    UnchunkedCt1SentMergeEnv UnchunkedCt1SentMergePostEnv

/-- Envelope-parameterized 112-byte-frame contract of `Unchunked.EkSentCt1Received::merge`. -/
def unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : UnchunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop) :
    Spec (UnchunkedEkSentCt1ReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedOwnStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp unchunkedOwnStack ∗
      match (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Unchunked.EkSentCt1Received, protoUnchunkedEkSentCt1ReceivedAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded 112-byte-frame contract of `Unchunked.EkSentCt1Received::merge`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def unchunkedEkSentCt1ReceivedMergeOwnSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (UnchunkedEkSentCt1ReceivedMergeGhost × M.σ) :=
  unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv A lim
    UnchunkedEkSentCt1ReceivedMergeEnv UnchunkedEkSentCt1ReceivedMergePostEnv

/-! ## 2. Frame-Lifting Bridges to `ChunkedDefsBudget` (`unchunkedMergeStack`) -/

theorem subroutine_ok_unchunkedCt1SentMergeOfEnv_of_own {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : UnchunkedCt1SentMergeGhost → List AllocEvent → Prop} {img : Obj.Image}
    (h : subroutine_ok prog entry ((unchunkedCt1SentMergeOwnSpecOfEnv A lim PreEnv PostEnv).inImage img)) :
    subroutine_ok prog entry ((unchunkedCt1SentMergeSpecOfEnv A lim PreEnv PostEnv).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
  have hpre_eq : ((unchunkedCt1SentMergeSpecOfEnv A lim PreEnv PostEnv).inImage img).pre x s0 ∗ R =
      ((unchunkedCt1SentMergeOwnSpecOfEnv A lim PreEnv PostEnv).inImage img).pre x s0 ∗ (R_extra ∗ R) := by
    dsimp only [Spec.inImage, unchunkedCt1SentMergeSpecOfEnv, unchunkedCt1SentMergeOwnSpecOfEnv,
      R_extra, unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedCt1SentCapAt,
      vecU8CapAt, optProtoAuthenticatorCapAt]
    rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
    sep_ac_rfl
  rw [hpre_eq] at hpre
  refine h.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpost_eq : ((unchunkedCt1SentMergeSpecOfEnv A lim PreEnv PostEnv).inImage img).post x s0 sf ∗ R =
        ((unchunkedCt1SentMergeOwnSpecOfEnv A lim PreEnv PostEnv).inImage img).post x s0 sf ∗ (R_extra ∗ R) := by
      dsimp only [Spec.inImage, unchunkedCt1SentMergeSpecOfEnv, unchunkedCt1SentMergeOwnSpecOfEnv,
        R_extra, unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedCt1SentCapAt,
        vecU8CapAt, optProtoAuthenticatorCapAt, ct1SentPBAt, unchunked5At,
        rustBytesVecAt, optAuthenticatorPBAt, protoUnchunkedCt1SentAt, optProtoAuthenticatorAt]
      rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
      sep_ac_rfl
    rw [hpost_eq]
    exact hq
  · dsimp only [Spec.inImage, unchunkedCt1SentMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [Spec.inImage, unchunkedCt1SentMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [Spec.inImage, unchunkedCt1SentMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem subroutine_ok_unchunkedCt1SentMerge_of_own {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {img : Obj.Image}
    (h : subroutine_ok prog entry ((unchunkedCt1SentMergeOwnSpec A lim).inImage img)) :
    subroutine_ok prog entry ((unchunkedCt1SentMergeSpec A lim).inImage img) :=
  subroutine_ok_unchunkedCt1SentMergeOfEnv_of_own h

theorem subroutine_ok_unchunkedEkSentCt1ReceivedMergeOfEnv_of_own {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : UnchunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop} {img : Obj.Image}
    (h : subroutine_ok prog entry ((unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv A lim PreEnv PostEnv).inImage img)) :
    subroutine_ok prog entry ((unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim PreEnv PostEnv).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
  have hpre_eq : ((unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim PreEnv PostEnv).inImage img).pre x s0 ∗ R =
      ((unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv A lim PreEnv PostEnv).inImage img).pre x s0 ∗ (R_extra ∗ R) := by
    dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeSpecOfEnv,
      unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv, R_extra,
      unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt,
      protoUnchunkedEkSentCt1ReceivedCapAt, vecU8CapAt, optProtoAuthenticatorCapAt]
    rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
    sep_ac_rfl
  rw [hpre_eq] at hpre
  refine h.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpost_eq : ((unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim PreEnv PostEnv).inImage img).post x s0 sf ∗ R =
        ((unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv A lim PreEnv PostEnv).inImage img).post x s0 sf ∗ (R_extra ∗ R) := by
      dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeSpecOfEnv,
        unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv, R_extra,
        unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt,
        protoUnchunkedEkSentCt1ReceivedCapAt, vecU8CapAt, optProtoAuthenticatorCapAt,
        ekSentCt1ReceivedPBAt, unchunked4At, rustBytesVecAt, optAuthenticatorPBAt,
        protoUnchunkedEkSentCt1ReceivedAt, optProtoAuthenticatorAt]
      rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
      sep_ac_rfl
    rw [hpost_eq]
    exact hq
  · dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem subroutine_ok_unchunkedEkSentCt1ReceivedMerge_of_own {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {img : Obj.Image}
    (h : subroutine_ok prog entry ((unchunkedEkSentCt1ReceivedMergeOwnSpec A lim).inImage img)) :
    subroutine_ok prog entry ((unchunkedEkSentCt1ReceivedMergeSpec A lim).inImage img) :=
  subroutine_ok_unchunkedEkSentCt1ReceivedMergeOfEnv_of_own h

theorem subroutine_ok_unchunkedCt1SentMergeOfEnv_of_own_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : UnchunkedCt1SentMergeGhost → List AllocEvent → Prop}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeOwnSpecOfEnv A lim PreEnv PostEnv))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpecOfEnv A lim PreEnv PostEnv)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
  have hpre_eq : (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpecOfEnv A lim PreEnv PostEnv)).pre x s0 ∗ R =
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeOwnSpecOfEnv A lim PreEnv PostEnv)).pre x s0 ∗ (R_extra ∗ R) := by
    dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeSpecOfEnv, unchunkedCt1SentMergeOwnSpecOfEnv,
      R_extra, unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedCt1SentCapAt,
      vecU8CapAt, optProtoAuthenticatorCapAt]
    rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
    sep_ac_rfl
  rw [hpre_eq] at hpre
  refine h.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpost_eq : (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpecOfEnv A lim PreEnv PostEnv)).post x s0 sf ∗ R =
        (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeOwnSpecOfEnv A lim PreEnv PostEnv)).post x s0 sf ∗ (R_extra ∗ R) := by
      dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeSpecOfEnv, unchunkedCt1SentMergeOwnSpecOfEnv,
        R_extra, unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedCt1SentCapAt,
        vecU8CapAt, optProtoAuthenticatorCapAt, ct1SentPBAt, unchunked5At,
        rustBytesVecAt, optAuthenticatorPBAt, protoUnchunkedCt1SentAt, optProtoAuthenticatorAt]
      rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
      sep_ac_rfl
    rw [hpost_eq]
    exact hq
  · dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem subroutine_ok_unchunkedCt1SentMerge_of_own_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeOwnSpec A lim))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) :=
  subroutine_ok_unchunkedCt1SentMergeOfEnv_of_own_placed h

theorem subroutine_ok_unchunkedEkSentCt1ReceivedMergeOfEnv_of_own_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : UnchunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv A lim PreEnv PostEnv))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim PreEnv PostEnv)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
  have hpre_eq : (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim PreEnv PostEnv)).pre x s0 ∗ R =
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv A lim PreEnv PostEnv)).pre x s0 ∗ (R_extra ∗ R) := by
    dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeSpecOfEnv,
      unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv, R_extra,
      unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt,
      protoUnchunkedEkSentCt1ReceivedCapAt, vecU8CapAt, optProtoAuthenticatorCapAt]
    rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
    sep_ac_rfl
  rw [hpre_eq] at hpre
  refine h.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpost_eq : (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim PreEnv PostEnv)).post x s0 sf ∗ R =
        (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv A lim PreEnv PostEnv)).post x s0 sf ∗ (R_extra ∗ R) := by
      dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeSpecOfEnv,
        unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv, R_extra,
        unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt,
        protoUnchunkedEkSentCt1ReceivedCapAt, vecU8CapAt, optProtoAuthenticatorCapAt,
        ekSentCt1ReceivedPBAt, unchunked4At, rustBytesVecAt, optAuthenticatorPBAt,
        protoUnchunkedEkSentCt1ReceivedAt, optProtoAuthenticatorAt]
      rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
      sep_ac_rfl
    rw [hpost_eq]
    exact hq
  · dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem subroutine_ok_unchunkedEkSentCt1ReceivedMerge_of_own_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) :=
  subroutine_ok_unchunkedEkSentCt1ReceivedMergeOfEnv_of_own_placed h

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
