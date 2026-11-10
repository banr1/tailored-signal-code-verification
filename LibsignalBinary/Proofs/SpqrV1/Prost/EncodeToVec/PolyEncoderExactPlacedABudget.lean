/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedA
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` `encode_repeated [local#2]` (`< 2 ^ 59`) and Call Wrappers

Bridges `EncodeRepeated2Budget.encode_repeated_2_59_det_placed_ok` to `encodeRepeated59SpecOf`
and `encodeRepeated59ExactSpecOf` under `[LibsignalPlacement]` (`Block 289`), and provides
generic `Program` call and tailcall steppers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl lsρ withLsCodeLoaded blkPC_289 blkPl_289 lsProg_289)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost (sp_sub_48_aligned)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustNoAllocShimSym spqrRustAllocSym spqrRustReallocSym spqrMemcpySym)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedBytes encodeRepeatedStackOf repeatedBytesSliceAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (MsgEnc48CalleeSavedPlaced msgEnc48RepeatedStackOf msgEnc48SavedFrame
   stackAt_msgEnc48_repeated_eq_bottom stackAt_msgEnc48_repeated_recombine
   withMsgEnc48CSPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec noAllocShimSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeRepeated59DetSpecOf encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2Budget
  (encode_repeated_2_59_det_placed_ok encode_repeated_2_59_det_placed_ok_of_callees
   encode_repeated_2_59_det_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget (sepWPp_call_cs_placed_noPanic)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (EncodeRepeatedEnv encodeRepeated59ExactSpecOf encodeRepeated59SpecOf
   encodeRepeated59SpecOfEnv encodeRepeatedEvents encodeRepeatedEvents_of_spare)

/-! ## 1. Bridges from `encodeRepeated59DetSpecOf` to `encodeRepeated59SpecOf` & `encodeRepeated59ExactSpecOf` -/

theorem encodeRepeated59SpecOf_post_of_det {resStack : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : EncodeRepeatedGhost} {st : M.σ} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (encodeRepeated59DetSpecOf resStack A lim).post (x, st) s0 sf ∗ R) :
    sf.mem ⊨ (encodeRepeated59SpecOf resStack A lim).post (x, st) s0 sf ∗ R := by
  dsimp only [encodeRepeated59DetSpecOf,
    LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget.encodeRepeatedSpecOf] at hq
  dsimp only [encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  obtain ⟨htr, hq⟩ := hq
  refine ⟨htr, ?_⟩
  have hq1 : sf.mem ⊨
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr) ∧
          cap'.toNat =
            (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget.encodeRepeatedStep
              x.tag x.cap.toNat x.bs.length (x.elems.map Prod.snd)).1⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr'
          (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd))) ∗
      ((∃∗ evs : List AllocEvent, ⌜EncodeRepeatedEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
        repeatedBytesSliceAt x.base x.elems ∗
        stackAt s0.sp (encodeRepeatedStackOf resStack) ∗ R) := by
    convert hq using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hq1
  obtain ⟨cap', hq1⟩ := hq1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hq1
  obtain ⟨ptr', hq1⟩ := hq1
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq1
  obtain ⟨⟨hge, hpres, _⟩, hq1⟩ := hq1
  have hq2 : sf.mem ⊨
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr'
          (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd))) ∗
      ((∃∗ evs : List AllocEvent, ⌜EncodeRepeatedEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
        repeatedBytesSliceAt x.base x.elems ∗
        stackAt s0.sp (encodeRepeatedStackOf resStack) ∗ R) := by
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨cap', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ptr', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hge, hpres⟩, hq1⟩
  convert hq2 using 1; sep_ac_rfl

theorem encodeRepeated59SpecOf_of_det {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hdet : subroutine_ok prog entry (encodeRepeated59DetSpecOf resStack A lim)) :
    subroutine_ok prog entry (encodeRepeated59SpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (encodeRepeated59DetSpecOf resStack A lim).pre (x, st) s0 ∗ R := hpre
  refine (hdet.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, encodeRepeated59SpecOf_post_of_det hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem encodeRepeated59SpecOf_of_det_placed [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hdet : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf resStack A lim)).pre (x, st) s0 ∗ R := hpre
  refine (hdet.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, encodeRepeated59SpecOf_post_of_det hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem subroutine_ok_encodeRepeated59Exact_of_59_placed [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodeRepeated59ExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  dsimp only [encodeRepeated59ExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, hmem⟩ := hpre
  have hevs0 : encodeRepeatedEvents x = [] := encodeRepeatedEvents_of_spare hfit
  have hfits : FitsEnv M lim st (EncodeRepeatedEnv x) := by
    unfold EncodeRepeatedEnv
    rw [FitsEnv.eq_iff, hevs0]
    trivial
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf resStack A lim)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, Or.inl hfit, hfits⟩, hmem⟩
  refine (hok.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv] at hq
    dsimp only [withLsCodeLoaded, encodeRepeated59ExactSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨htr, hq⟩ := hq
    refine ⟨htr, ?_⟩
    have hq1 : sf.mem ⊨
        (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr'
            (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd))) ∗
        ((∃∗ evs : List AllocEvent, ⌜EncodeRepeatedEnv x evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
          repeatedBytesSliceAt x.base x.elems ∗
          stackAt s0.sp (encodeRepeatedStackOf resStack) ∗ R) := by
      convert hq using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq1
    obtain ⟨cap', hq1⟩ := hq1
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq1
    obtain ⟨ptr', hq1⟩ := hq1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq1
    obtain ⟨⟨_, hpres⟩, hq1⟩ := hq1
    obtain ⟨rfl, rfl⟩ := hpres hfit
    have hq2 : sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜EncodeRepeatedEnv x evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
        (repeatedBytesSliceAt x.base x.elems ∗
          vecU8At A.repAlloc x.v x.cap x.ptr
            (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd)) ∗
          stackAt s0.sp (encodeRepeatedStackOf resStack) ∗ R) := by
      convert hq1 using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq2
    obtain ⟨evs, hq2⟩ := hq2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq2
    obtain ⟨hevs, hq2⟩ := hq2
    dsimp only [EncodeRepeatedEnv] at hevs
    rw [hevs, hevs0] at hq2
    dsimp only [AllocCostModel.stepEvents] at hq2
    convert hq2 using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## 2. Placed `[LibsignalPlacement]` `encode_repeated [local#2]` (`Block 289`, `< 2 ^ 59`) -/

theorem encode_repeated_2_59_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_289 H) (lsmpl.base 292)
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_289 H) (lsmpl.base 320)
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_289 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_289 H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf resStack A lim)) :=
  encodeRepeated59SpecOf_of_det_placed
    (encode_repeated_2_59_det_placed_ok_of_callees hres henc0 hdoReserve0 hmemcpy)

theorem encode_repeated_2_59_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_289).rebase (blkPl_289).base H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf doReserveStack A lim)) :=
  encodeRepeated59SpecOf_of_det_placed
    (encode_repeated_2_59_det_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_repeated_2_59_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_289).rebase (blkPl_289).base H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf doReserveStackX A lim)) :=
  encodeRepeated59SpecOf_of_det_placed
    (encode_repeated_2_59_det_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem encode_repeated_2_59_exact_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_289).rebase (blkPl_289).base H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59ExactSpecOf doReserveStack A lim)) :=
  subroutine_ok_encodeRepeated59Exact_of_59_placed
    (encode_repeated_2_59_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_repeated_2_59_exact_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_289).rebase (blkPl_289).base H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59ExactSpecOf doReserveStackX A lim)) :=
  subroutine_ok_encodeRepeated59Exact_of_59_placed
    (encode_repeated_2_59_placed_ok_x h_panic hshim halloc hrealloc hmc)

/-! ## 3. Generic `Program` Call & Tailcall Steppers for `encodeRepeated59SpecOf` & `encodeRepeated59ExactSpecOf` -/

theorem step_msg48_encode_repeated59_call_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeRepeated59SpecOf resStack A lim)))
    (tag : Nat) (base v curCap curPtr sp ret_pc : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 59)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((repeatedBytesSliceAt base elems ∗
          vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool lim (M.stepEvents (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs, curSt)) (F := F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withMsgEnc48CSPlaced, encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
        hge hpres)

theorem step_msg48_encode_repeated59_tailcall_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeRepeated59SpecOf resStack A lim)))
    (tag : Nat) (base v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 59)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((repeatedBytesSliceAt base elems ∗
        vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
        A.pool lim (M.stepEvents (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)) curSt) sf ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs, curSt))
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗ F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; sep_ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48RepeatedStackOf resStack) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') :=
      Satisfies.mono (sepConj_mono_left (stackAt_msgEnc48_repeated_recombine hres sp fp lr r21 v3 r20 r19)) hm0
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CSPlaced, encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm1 using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeated59SpecOf, encodeRepeated59SpecOfEnv]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) := hev
    subst hev_eq
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28,
        hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
          hge hpres))
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48_encode_repeated59_exact_call_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack A lim)))
    (tag : Nat) (base v curCap curPtr sp ret_pc : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 59)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((repeatedBytesSliceAt base elems ∗
          vecU8At A.repAlloc v curCap curPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool lim curSt sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs, curSt)) (F := F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withMsgEnc48CSPlaced, encodeRepeated59ExactSpecOf, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeated59ExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))

theorem step_msg48_encode_repeated59_exact_tailcall_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack A lim)))
    (tag : Nat) (base v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 59)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((repeatedBytesSliceAt base elems ∗
        vecU8At A.repAlloc v curCap curPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
        A.pool lim curSt sf ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs, curSt))
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗ F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; sep_ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48RepeatedStackOf resStack) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ F ∗ R') :=
      Satisfies.mono (sepConj_mono_left (stackAt_msgEnc48_repeated_recombine hres sp fp lr r21 v3 r20 r19)) hm0
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CSPlaced, encodeRepeated59ExactSpecOf, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, ?_⟩
    convert hm1 using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeated59ExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28,
        hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))))
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
