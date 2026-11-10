/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Handshake `finish_grow [local#9]` and `do_reserve_and_handle [local#8]` Specifications

Defines allocator event lists, envelopes, and total-correctness (`onPanic = ⌜False⌝`,
`onOom = ⌜False⌝` under `FitsEnv`) contracts and program-generic representation combinators for
1-byte-element `finish_grow` and 3-argument `do_reserve_and_handle` under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget

open Arm64 ProofLib SepProp
open CryptoVerification (withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall doReserveStackX reserveCap)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  FG24Ghost FinishGrow1Call doReserve10Name doReserve32Stack finishGrow11Name finishGrow32Stack
  memRegion_24
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents doReserveRawSpecX doReserveSpecX finishGrowEvents
)

/-! ## 1. Allocator Event Lists & Envelopes for 1-Byte-Element `finish_grow` -/

/-- Exact allocator event list of 1-byte-element (`stride = 1, align = 1`) `finish_grow`. -/
def finishGrow1Events (cap new : Nat) : List AllocEvent :=
  finishGrowEvents cap new 1 1

/-- Allocator event envelope of 1-byte-element `finish_grow`. -/
def FinishGrow1Env (x : FinishGrow1Call) (evs : List AllocEvent) : Prop :=
  evs = finishGrow1Events x.cap.toNat x.new.toNat

theorem fitsEnv_finishGrow1_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : FinishGrow1Call) :
    FitsEnv M lim st (FinishGrow1Env x) ↔
      FitsEvents M lim st (finishGrow1Events x.cap.toNat x.new.toNat) :=
  FitsEnv.eq_iff

theorem finishGrow1Events_doReserve_eq (x : DoReserveCall)
    (hbound : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64) :
    finishGrow1Events x.cap.toNat
        (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
      doReserveEvents x := by
  have hnew :
      (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  unfold finishGrow1Events finishGrowEvents doReserveEvents
  rw [hnew, Nat.mul_one, Nat.mul_one]
  by_cases hcap : x.cap = 0#64
  · rw [hcap]; rfl
  · have hcap_nat : x.cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    simp only [hcap, hcap_nat, ↓reduceIte]

/-! ## 2. Budget-Threaded `finishGrow1*` Contracts & Combinators -/

/-- Total-correctness (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) contract of 1-byte-element
`finish_grow` (`stride = 1, align = 1`, 32-byte frame) under `FitsEnv M lim st (FinishGrow1Env x)`. -/
def finishGrow1Spec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrow1Call × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (FinishGrow1Env x)⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp finishGrow32Stack
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ x.new) ∗
      A.live p' x.new.toNat 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (x.new.toNat - x.bs.length) ∗
      A.pool lim (M.stepEvents (finishGrow1Events x.cap.toNat x.new.toNat) st) sf ∗
      stackAt s0.sp finishGrow32Stack

def finishGrow1AllocSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrow1Call × M.σ) :=
  { finishGrow1Spec M A lim with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (FinishGrow1Env x)⌝ ∗
      memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp finishGrow32Stack }

def finishGrow1ReallocSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrow1Call × M.σ) :=
  { finishGrow1Spec M A lim with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (FinishGrow1Env x)⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool lim st s ∗ stackAt s.sp finishGrow32Stack }

theorem finish_grow_11_of_zero_ne {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h0 : subroutine_ok P addr (finishGrow1AllocSpec M A lim))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpec M A lim)) :
    subroutine_ok P addr (finishGrow1Spec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine h0.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [finishGrow1Spec, finishGrow1AllocSpec, FinishGrow1Call.oldBuf,
      hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay, hfits⟩, hmem⟩
  · refine hne.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [finishGrow1Spec, finishGrow1ReallocSpec, FinishGrow1Call.oldBuf,
      hcap0, ite_false, RustCliAllocBudget.repAlloc_live_norm,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay, hfits⟩, hmem⟩

def finishGrow24ZeroCellsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG24Ghost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (finishGrow1Events 0 new.toNat)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp finishGrow32Stack
  post := fun ((out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ new) ∗
      A.live p' new.toNat 1 ∗ memRegion p' new.toNat ∗
      A.pool lim (M.stepEvents (finishGrow1Events 0 new.toNat) st) sf ∗
      stackAt fsp finishGrow32Stack

def finishGrow24NeCellsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG24Ghost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (finishGrow1Events cap.toNat new.toNat)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp finishGrow32Stack
  post := fun ((out, cap, _ptr, new, bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ new) ∗
      A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗
      A.pool lim (M.stepEvents (finishGrow1Events cap.toNat new.toNat) st) sf ∗
      stackAt fsp finishGrow32Stack

theorem finish_grow_24_zero_cells_of_spec {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrow1Spec M A lim)) :
    subroutine_ok P addr (finishGrow24ZeroCellsSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow24ZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap0, hbs, hle, hpos, hbound, hfits⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrow1Call := ⟨out, 0#64, ptr, new, []⟩
  have hfits_env : FitsEnv M lim st (FinishGrow1Env hcall) :=
    (fitsEnv_finishGrow1_iff hcall).mpr hfits
  have hpre' : s0.mem ⊨ (finishGrow1Spec M A lim).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow1Spec, hcall, FinishGrow1Call.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, fun _ => trivial, Nat.zero_le _, hle, hpos, hbound, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow1Spec, finishGrow24ZeroCellsSpec, hcall,
      BitVec.toNat_zero, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepExists_sepConj_left,
      satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    exact ⟨p', by simpa only [sepConj_assoc] using hq⟩
  · exact Or.inr hfail

theorem finish_grow_24_ne_cells_of_spec {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrow1Spec M A lim)) :
    subroutine_ok P addr (finishGrow24NeCellsSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow24NeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap, hbs, hle, hpos, hbound, hfits⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrow1Call := ⟨out, cap, ptr, new, bs⟩
  have hfits_env : FitsEnv M lim st (FinishGrow1Env hcall) :=
    (fitsEnv_finishGrow1_iff hcall).mpr hfits
  have hpre' : s0.mem ⊨ (finishGrow1Spec M A lim).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow1Spec, hcall, FinishGrow1Call.oldBuf, hcap, ite_false,
      RustCliAllocBudget.repAlloc_live_norm, memRegion_24,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, False.elim, hbs, hle, hpos, hbound, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow1Spec, finishGrow24NeCellsSpec, hcall,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    exact ⟨p', by simpa only [sepConj_assoc] using hq⟩
  · exact Or.inr hfail

/-! ## 3. Budget-Threaded `doReserve1*` Contracts & Combinators -/

def doReserve1Raw32Spec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp doReserve32Stack
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0.sp doReserve32Stack

def doReserve1RawSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp doReserveStackX
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0.sp doReserveStackX

/-- Vec wrapper around `doReserve1RawSpec`: contract of 3-argument `do_reserve_and_handle`
(`stride = 1, align = 1` hardcoded, so `x3` and `x4` are unconstrained) at `doReserveStackX`. -/
def doReserve1VecSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      newCap + 1 ≤ 2 ^ 63 ∧ FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp doReserveStackX
  post := (doReserveSpecX M A lim).post

private theorem stackAt_doReserve_eq_32 (sp : BitVec 64) :
    stackAt sp doReserveStackX =
      memRegion (sp - 16496#64) 16 ∗ stackAt sp doReserve32Stack :=
  ProofLib.stackAt_split_bottom sp 16480 16 (by decide)

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  sep_ac_rfl

theorem do_reserve_raw1_of_raw32 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h32 : subroutine_ok P addr (doReserve1Raw32Spec M A lim)) :
    subroutine_ok P addr (doReserve1RawSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1RawSpec, stackAt_doReserve_eq_32, sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - 16496#64) 16
  have hpre' : s0.mem ⊨ (doReserve1Raw32Spec M A lim).pre (x, st) s0 ∗ (btm ∗ R) := by
    simp only [doReserve1Raw32Spec, btm, sepConj_assoc]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h32.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserve1Raw32Spec, doReserve1RawSpec, stackAt_doReserve_eq_32,
      btm, sepConj_assoc] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem do_reserve_raw1_of_raw32_lscl {M : AllocCostModel} {pl : Obj.MultiPlacement}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h32 : subroutine_ok P addr (withLsCodeLoaded pl (doReserve1Raw32Spec M A lim))) :
    subroutine_ok P addr (withLsCodeLoaded pl (doReserve1RawSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1RawSpec, stackAt_doReserve_eq_32, sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - 16496#64) 16
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl (doReserve1Raw32Spec M A lim)).pre (x, st) s0 ∗
      (btm ∗ R) := by
    simp only [doReserve1Raw32Spec, btm, sepConj_assoc]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h32.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserve1Raw32Spec, doReserve1RawSpec,
      stackAt_doReserve_eq_32, btm, sepConj_assoc] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem do_reserve_raw_of_raw1 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h1 : subroutine_ok P addr (doReserve1RawSpec M A lim)) :
    subroutine_ok P addr (doReserveRawSpecX M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecX,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨ (doReserve1RawSpec M A lim).pre (x, st) s0 ∗ R := by
    simp only [doReserve1RawSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound, hfits⟩, hmem⟩
  exact h1.mono_outcome (x, st) R s0 hpc hrun hpre' hsp (fun _ ho => ho)

theorem do_reserve_raw_of_raw1_lscl {M : AllocCostModel} {pl : Obj.MultiPlacement}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h1 : subroutine_ok P addr (withLsCodeLoaded pl (doReserve1RawSpec M A lim))) :
    subroutine_ok P addr (withLsCodeLoaded pl (doReserveRawSpecX M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecX,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl (doReserve1RawSpec M A lim)).pre (x, st) s0 ∗ R := by
    simp only [doReserve1RawSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound, hfits⟩, hmem⟩
  exact h1.mono_outcome (x, st) R s0 hpc hrun hpre' hsp (fun _ ho => ho)

theorem do_reserve_vec_of_raw {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (hraw : subroutine_ok P addr (doReserveRawSpecX M A lim)) :
    subroutine_ok P addr (doReserveSpecX M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveSpecX,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (doReserveRawSpecX M A lim).pre (x, st) s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hraw.mono_outcome (x, st)
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserveRawSpecX, doReserveSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      dsimp [reserveCap, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap] at hbound ⊢
      omega
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem do_reserve_vec_of_raw_lscl {M : AllocCostModel} {pl : Obj.MultiPlacement}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (hraw : subroutine_ok P addr (withLsCodeLoaded pl (doReserveRawSpecX M A lim))) :
    subroutine_ok P addr (withLsCodeLoaded pl (doReserveSpecX M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveSpecX,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl (doReserveRawSpecX M A lim)).pre (x, st) s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hraw.mono_outcome (x, st)
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserveRawSpecX, doReserveSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      dsimp [reserveCap, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap] at hbound ⊢
      omega
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem do_reserve_vec1_of_raw1 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (hraw : subroutine_ok P addr (doReserve1RawSpec M A lim)) :
    subroutine_ok P addr (doReserve1VecSpecX M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1VecSpecX, vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (doReserve1RawSpec M A lim).pre (x, st) s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserve1RawSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound, hfits⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hraw.mono_outcome (x, st)
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserve1RawSpec, doReserve1VecSpecX, doReserveSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      dsimp [reserveCap, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap] at hbound ⊢
      omega
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem do_reserve_vec1_of_raw1_lscl {M : AllocCostModel} {pl : Obj.MultiPlacement}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (hraw : subroutine_ok P addr (withLsCodeLoaded pl (doReserve1RawSpec M A lim))) :
    subroutine_ok P addr (withLsCodeLoaded pl (doReserve1VecSpecX M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1VecSpecX, vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl (doReserve1RawSpec M A lim)).pre (x, st) s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserve1RawSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound, hfits⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hraw.mono_outcome (x, st)
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserve1RawSpec, doReserve1VecSpecX, doReserveSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      dsimp [reserveCap, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap] at hbound ⊢
      omega
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget
