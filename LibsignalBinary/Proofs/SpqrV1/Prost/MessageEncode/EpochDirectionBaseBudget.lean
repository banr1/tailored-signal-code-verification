/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBase
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Shared Base for `prost::encoding::message::encode::<EpochDirection, Vec<u8>>`

Defines allocator event envelopes (`EncodeEpochDirection{Pinned,}Env`), envelope-parameterized
and concrete `RustCliAllocBudget` specifications, exact-capacity `VmPreserved` contracts, and
pinned-to-unpinned bridges for `encode<EpochDirection>` (`[local#1, 2]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8EncodeEnv fitsEnv_vecU8EncodeEnv_of_spare)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStack doReserveStackX tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Auth (authEncodeStackOf)
open CryptoVerification.SpqrV1.ProtoRepr
  (EpochDirectionPBGhost epochDirectionPBAt epochDirectionPBAt_eq_exists_pinned
   epochDirectionPBPinnedAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodeEpochDirectionGhost EncodeEpochDirectionPinnedGhost encodeEpochDirection1Name
   encodeEpochDirection2Name encodeEpochDirectionMsg)

/-! ## 1. Allocator Event Envelopes for `encode<EpochDirection>` -/

/-- Concrete allocator event envelope of `encode<EpochDirection>` (pinned ghost). -/
def EncodeEpochDirectionPinnedEnv (x : EncodeEpochDirectionPinnedGhost)
    (evs : List AllocEvent) : Prop :=
  VecU8EncodeEnv x.cap.toNat (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length) evs

/-- Concrete allocator event envelope of `encode<EpochDirection>` (unpinned ghost). -/
def EncodeEpochDirectionEnv (x : EncodeEpochDirectionGhost)
    (evs : List AllocEvent) : Prop :=
  VecU8EncodeEnv x.cap.toNat (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length) evs

theorem encodeEpochDirectionPinnedEnv_eq_nil_of_spare
    {x : EncodeEpochDirectionPinnedGhost} {evs : List AllocEvent}
    (hle : x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat)
    (h : EncodeEpochDirectionPinnedEnv x evs) : evs = [] :=
  VecU8EncodeEnv.eq_nil_of_le hle h

theorem encodeEpochDirectionEnv_eq_nil_of_spare
    {x : EncodeEpochDirectionGhost} {evs : List AllocEvent}
    (hle : x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat)
    (h : EncodeEpochDirectionEnv x evs) : evs = [] :=
  VecU8EncodeEnv.eq_nil_of_le hle h

/-! ## 2. Budget-Threaded Pinned & Unpinned Specifications (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) -/

/-- Envelope-parameterized pinned budget specification of `encode<EpochDirection>`. -/
def encodeEpochDirectionPinnedSpecOfEnv (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv : EncodeEpochDirectionPinnedGhost → (List AllocEvent → Prop) → Prop)
    (PostEnv : EncodeEpochDirectionPinnedGhost → List AllocEvent → Prop) :
    Spec (EncodeEpochDirectionPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.dirA ∧
      s.readReg64 .x2 = x.v ∧
      (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length + 10 < 2 ^ 62) ∧
      (∀ Env, PreEnv x Env → FitsEnv M lim st Env)⌝ ∗
      epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (authEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜PostEnv x evs ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

/-- Envelope-parameterized unpinned budget specification of `encode<EpochDirection>`. -/
def encodeEpochDirectionSpecOfEnv (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv : EncodeEpochDirectionGhost → (List AllocEvent → Prop) → Prop)
    (PostEnv : EncodeEpochDirectionGhost → List AllocEvent → Prop) :
    Spec (EncodeEpochDirectionGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.dirA ∧
      s.readReg64 .x2 = x.v ∧
      (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length + 10 < 2 ^ 62) ∧
      (∀ Env, PreEnv x Env → FitsEnv M lim st Env)⌝ ∗
      epochDirectionPBAt A.repAlloc x.dirA x.dir ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (authEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBAt A.repAlloc x.dirA x.dir ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜PostEnv x evs ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

/-- Concrete pinned budget specification of `encode<EpochDirection>`. -/
def encodeEpochDirectionPinnedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeEpochDirectionPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.dirA ∧
      s.readReg64 .x2 = x.v ∧
      (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeEpochDirectionPinnedEnv x)⌝ ∗
      epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (authEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜EncodeEpochDirectionPinnedEnv x evs ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

/-- Concrete unpinned budget specification of `encode<EpochDirection>`. -/
def encodeEpochDirectionSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeEpochDirectionGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.dirA ∧
      s.readReg64 .x2 = x.v ∧
      (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeEpochDirectionEnv x)⌝ ∗
      epochDirectionPBAt A.repAlloc x.dirA x.dir ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (authEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBAt A.repAlloc x.dirA x.dir ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜EncodeEpochDirectionEnv x evs ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

/-- Exact-capacity 0-allocation (`VmPreserved`) pinned contract of `encode<EpochDirection>`. -/
def encodeEpochDirectionPinnedExactVmSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodeEpochDirectionPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.dirA ∧
      s.readReg64 .x2 = x.v ∧
      x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat⌝ ∗
      epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (authEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

abbrev encodeEpochDirectionPinnedSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeEpochDirectionPinnedGhost × M.σ) :=
  encodeEpochDirectionPinnedSpecOf doReserveStack A lim

abbrev encodeEpochDirectionPinnedSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeEpochDirectionPinnedGhost × M.σ) :=
  encodeEpochDirectionPinnedSpecOf doReserveStackX A lim

abbrev encodeEpochDirectionSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeEpochDirectionGhost × M.σ) :=
  encodeEpochDirectionSpecOf doReserveStack A lim

abbrev encodeEpochDirectionSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeEpochDirectionGhost × M.σ) :=
  encodeEpochDirectionSpecOf doReserveStackX A lim

/-! ## 3. Pinned-to-Unpinned & Envelope Bridges -/

theorem subroutine_ok_encodeEpochDirectionPinned_of_env {resStack : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (encodeEpochDirectionPinnedSpecOfEnv resStack A lim
        (fun x Env => Env = EncodeEpochDirectionPinnedEnv x) EncodeEpochDirectionPinnedEnv)) :
    subroutine_ok prog entry (encodeEpochDirectionPinnedSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodeEpochDirectionPinnedSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hfit, hEnv⟩, hrest⟩
  have hpreE : s0.mem ⊨
      (encodeEpochDirectionPinnedSpecOfEnv resStack A lim
        (fun x Env => Env = EncodeEpochDirectionPinnedEnv x) EncodeEpochDirectionPinnedEnv).pre
        (x, st) s0 ∗ R := by
    dsimp only [encodeEpochDirectionPinnedSpecOfEnv]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hw0, hx1, hx2, hfit, fun _ h => h ▸ hEnv⟩, hrest⟩
  exact h.mono_outcome (x, st) R s0 hpc hrun hpreE hsp fun _ hout => hout

theorem epochDirection_post_unpinned_of_pinned_env {resStack : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PostP : EncodeEpochDirectionPinnedGhost → List AllocEvent → Prop}
    {PostU : EncodeEpochDirectionGhost → List AllocEvent → Prop}
    {x : EncodeEpochDirectionGhost} {g : EpochDirectionPBGhost} {st : M.σ}
    {s0 sf : State} {R : SepProp}
    (hpost : ∀ evs,
      PostP ⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ evs → PostU x evs)
    {PreP PreU}
    (hq : sf.mem ⊨ (encodeEpochDirectionPinnedSpecOfEnv resStack A lim PreP PostP).post
      (⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st) s0 sf ∗ R) :
    sf.mem ⊨ (encodeEpochDirectionSpecOfEnv resStack A lim PreU PostU).post (x, st) s0 sf ∗ R := by
  refine Satisfies.mono (sepConj_mono_left ?_) hq
  dsimp only [encodeEpochDirectionPinnedSpecOfEnv, encodeEpochDirectionSpecOfEnv]
  refine sepConj_mono (Entails.refl _)
    (sepConj_mono ?_
      (sepConj_mono (Entails.refl _)
        (sepConj_mono ?_ (Entails.refl _))))
  · rw [epochDirectionPBAt_eq_exists_pinned]
    exact Entails.sepExists_right g (Entails.refl _)
  · exact Entails.sepExists_elim fun evs => Entails.sepExists_right evs
      (Entails.pure_left fun ⟨hp1, hp2⟩ => Entails.pure_right ⟨hpost evs hp1, hp2⟩ (Entails.refl _))

theorem epochDirection_unpinned_of_pinned {resStack : Nat} {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry (encodeEpochDirectionPinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry (encodeEpochDirectionSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodeEpochDirectionSpecOf] at hpre
  rw [epochDirectionPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome (⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st)
      R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    exact epochDirection_post_unpinned_of_pinned_env
      (PreP := fun y Env => Env = EncodeEpochDirectionPinnedEnv y)
      (PreU := fun y Env => Env = EncodeEpochDirectionEnv y)
      (fun _ h => h)
      (by
        dsimp only [encodeEpochDirectionPinnedSpecOf] at hq
        dsimp only [encodeEpochDirectionPinnedSpecOfEnv]
        exact hq)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem epochDirection_unpinned_of_pinned_x {resStack : Nat} {M : AllocCostModel}
    {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry ((encodeEpochDirectionPinnedSpecOf resStack A lim).inImage img)) :
    subroutine_ok prog entry ((encodeEpochDirectionSpecOf resStack A lim).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodeEpochDirectionSpecOf] at hpre
  rw [epochDirectionPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ ((encodeEpochDirectionPinnedSpecOf resStack A lim).inImage img).pre
      (⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, hpre⟩
  refine hpinned.mono_outcome (⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st)
      R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    exact epochDirection_post_unpinned_of_pinned_env
      (PreP := fun y Env => Env = EncodeEpochDirectionPinnedEnv y)
      (PreU := fun y Env => Env = EncodeEpochDirectionEnv y)
      (fun _ h => h)
      (by
        dsimp only [Spec.inImage, encodeEpochDirectionPinnedSpecOf] at hq
        dsimp only [encodeEpochDirectionPinnedSpecOfEnv]
        exact hq)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

def EncodeEpochDirection1PinnedOkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name)
    (encodeEpochDirectionPinnedSpec A lim)

def EncodeEpochDirection1OkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name)
    (encodeEpochDirectionSpec A lim)

def EncodeEpochDirection1PinnedOkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeEpochDirection1Name)
    ((encodeEpochDirectionPinnedSpecX A lim).inImage img)

def EncodeEpochDirection1OkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeEpochDirection1Name)
    ((encodeEpochDirectionSpecX A lim).inImage img)

def EncodeEpochDirection2PinnedOkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection2Name)
    (encodeEpochDirectionPinnedSpec A lim)

def EncodeEpochDirection2OkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection2Name)
    (encodeEpochDirectionSpec A lim)

def EncodeEpochDirection2PinnedOkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeEpochDirection2Name)
    ((encodeEpochDirectionPinnedSpecX A lim).inImage img)

def EncodeEpochDirection2OkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeEpochDirection2Name)
    ((encodeEpochDirectionSpecX A lim).inImage img)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
