/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Core
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Fetch
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Budget-Threaded Relocatable Contracts for `RawVec<MessageKey>::grow_one` (Blocks 43 and 45)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.CoreBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_24 blkPC_43 blkPC_45 blkPl_24 blkPl_43 blkPl_45
  lsNoAllocShimSym lsRustAllocSym lsRustNoAllocShimSym lsRustReallocSym
  ls_subroutine_ok_of_block lsmpl sepWP_seq_lscl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalSession.RawVecGrowOne (
  grow_new_cap_eq stackAt_grow_one
)
open CryptoVerification.LibsignalSession.RawVecGrowOne.GrowOneStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.LibsignalTripleRatchet (FinishGrowCall)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents rawVecNewCap)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpec fitsEnv_finishGrow_iff
  noAllocShimBudgetSpec noAllocShim_hookOk vmPreserved_hookNoop
)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (
  GrowOneEnv GrowOnePlacedOk growOneEnv_events growOneEvents growOneSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks cmkShimSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

theorem hookSat_noAllocShim_of_cmkShim {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym cmkShimSpec) :
    HookSat H sym noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun (by simpa [cmkShimSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.cmkShimSpec, noAllocShimBudgetSpec] using hpre) hsp with
    ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [cmkShimSpec, withVmPreserved, CryptoVerification.LibsignalSession.cmkShimSpec,
      noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

theorem hookSat_cmkShim_of_noop {H : String → Option (State → State)} {sym : String}
    (h : H sym = some hookNoop) :
    HookSat H sym cmkShimSpec :=
  hookSat_withVmPreserved
    ⟨hookNoop, h, CryptoVerification.LibsignalSession.RawVecGrowOne.sessionShim_hookOk⟩
    fun f hf s => by cases h.symm.trans hf; exact vmPreserved_hookNoop s

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) := by
  have ha1 : a + 8#64 + 8#64 = a + 16#64 := by rw [BitVec.add_assoc]; rfl
  rw [show (24 : Nat) = 8 * 3 from rfl, memRegion_cells a 3 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right, ha1]

private theorem stackAt_4144_split (fsp : BitVec 64) :
    stackAt (fsp - 48#64) allocHookStack ∗ cells (fsp - 48#64) 6 =
      stackAt fsp (allocHookStack + 48) := by
  have h := stackAt_split_cells fsp allocHookStack 6 (by decide)
  change stackAt fsp (allocHookStack + 48) =
    stackAt (fsp - 48#64) allocHookStack ∗ cells (fsp - 48#64) 6 at h
  exact h.symm

private theorem finishGrowEvents_104_eq (cap : BitVec 64) :
    finishGrowEvents cap.toNat (max (2 * cap.toNat) 4) 8 104 = growOneEvents cap := by
  unfold finishGrowEvents growOneEvents rawVecGrowEvents rawVecNewCap
  by_cases h0 : cap = 0#64
  · subst h0; rfl
  · have hnat : cap.toNat ≠ 0 := fun hc => h0 (BitVec.eq_of_toNat_eq hc)
    simp only [h0, hnat, ↓reduceIte]

private abbrev FG104BudgetGhost (M : AllocCostModel) :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × M.σ

private def finishGrow104ZeroSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG104BudgetGhost M) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents (new.toNat * 104) 8)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt (fsp - 48#64) allocHookStack ∗ cells (fsp - 48#64) 6
  post := fun (out, _cap, _, new, bs, _, _, _, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗
      A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
      A.pool lim (M.stepEvents (rustAllocEvents (new.toNat * 104) 8) st) sf ∗
      stackAt (fsp - 48#64) allocHookStack ∗ cells (fsp - 48#64) 6

private def finishGrow104NeSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG104BudgetGhost M) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 104 ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustReallocEvents (cap.toNat * 104) (new.toNat * 104) 8)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
    A.pool lim st s ∗ stackAt (fsp - 48#64) allocHookStack ∗ cells (fsp - 48#64) 6
  post := fun (out, cap, _, new, bs, _, _, _, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗
      A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
      A.pool lim (M.stepEvents (rustReallocEvents (cap.toNat * 104) (new.toNat * 104) 8) st) sf ∗
      stackAt (fsp - 48#64) allocHookStack ∗ cells (fsp - 48#64) 6

private theorem finish_grow_104_zero_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowSpec M A lim)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrow104ZeroSpec M A lim) := by
  refine subroutine_ok_map hfg
    (fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpre => ?_)
  simp only [finishGrow104ZeroSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 104#64, []⟩
  have hlay : RustLayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat :=
    ⟨⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, by change new.toNat * 104 + 8 ≤ 2 ^ 63; omega⟩,
      by decide⟩
  have hfits_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    exact hfit
  refine ⟨(hcall, st), R, ?_, fun sf hq => ?_⟩
  · simp only [finishGrowSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, ite_true, memRegion_24_cells, emp_sepConj,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o0, o1, o2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos,
      by decide, hlay, hfits_env⟩, ?_⟩
    rw [← stackAt_4144_split s0.sp]
    simpa only [sepConj_assoc] using hmem
  · simp only [finishGrowSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow104ZeroSpec, hcall, finishGrowEvents, BitVec.toNat_zero, ↓reduceIte,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero,
      Nat.sub_zero, emp_sepConj, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', ?_⟩
    rw [← stackAt_4144_split s0.sp] at hq
    simpa only [BitVec.toNat_ofNat, sepConj_assoc] using hq

private theorem finish_grow_104_ne_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowSpec M A lim)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrow104NeSpec M A lim) := by
  refine subroutine_ok_map hfg
    (fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpre => ?_)
  simp only [finishGrow104NeSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 104#64, bs⟩
  have hlay : RustLayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat :=
    ⟨⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, by change new.toNat * 104 + 8 ≤ 2 ^ 63; omega⟩,
      by decide⟩
  have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hcap_nat : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  have hfits_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    simpa only [finishGrowEvents, hcall, hcap_nat, ↓reduceIte, hm104, ha8] using hfit
  refine ⟨(hcall, st), R, ?_, fun sf hq => ?_⟩
  · simp only [finishGrowSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, RustCliAllocBudget.repAlloc_live_norm,
      hcap, ite_false, memRegion_24_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o0, o1, o2, ?_⟩
    rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp,
      ← stackAt_4144_split s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun hc => False.elim hc, Nat.le_refl _, hle, hpos,
      by decide, hlay, hfits_env⟩, ?_⟩
    simpa only [sepConj_assoc] using hmem
  · simp only [finishGrowSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow104NeSpec, hcall, finishGrowEvents, hcap_nat, ↓reduceIte,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', ?_⟩
    rw [← stackAt_4144_split s0.sp] at hq
    simpa only [BitVec.toNat_ofNat, sepConj_assoc] using hq

theorem finish_grow_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym cmkShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowSpec M A lim) :=
  LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget.finish_grow_placed_ok
    (hookSat_noAllocShim_of_cmkShim h_shim) h_alloc h_realloc

theorem finish_grow_placed_ok_of_noop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowSpec M A lim) :=
  finish_grow_placed_ok (hookSat_cmkShim_of_noop h_shim) h_alloc h_realloc

private def growOneRawSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowGhost × M.σ) where
  pre := (growOneSpec M A lim).pre
  post := fun ((v, cap, _, bs), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap - cap.toNat) * 104)) ∗
    A.pool lim (M.stepEvents (growOneEvents cap) st) sf ∗
    stackAt s0.sp 4608

set_option maxHeartbeats 600000 in
private theorem grow_one_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym cmkShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneRawSpec M A lim)) := by
  unfold withLsCodeLoaded growOneRawSpec growOneSpec
  simp only [stackAt_grow_one, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfg := finish_grow_placed_ok h_shim h_alloc h_realloc
  have hfg0 := ls_subroutine_ok_of_block (callerProg := (blkPC_43).rebase (blkPl_43).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_104_zero_placed_ok hfg))
  have hfg1 := ls_subroutine_ok_of_block (callerProg := (blkPC_43).rebase (blkPl_43).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_104_ne_placed_ok hfg))
  change subroutine_ok _ (lsmpl.base 45) _ at hfg0 hfg1
  dsimp only [withLsCodeLoaded, finishGrow104ZeroSpec, finishGrow104NeSpec] at hfg0 hfg1
  clear hfg
  wp_init xst s0
  obtain ⟨⟨v, cap, ptr, bs⟩, st⟩ := xst
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_eq : (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := grow_new_cap_eq (by omega)
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  have hfits_ev : FitsEvents M lim st (finishGrowEvents cap.toNat new.toNat 8 104) := by
    rw [hnew_toNat, finishGrowEvents_104_eq]
    exact ‹FitsEnv M lim st (GrowOneEnv cap)› (growOneEvents cap) (growOneEnv_events cap)
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 104›
    subst hbs
    have hfit_ev : FitsEvents M lim st (rustAllocEvents (new.toNat * 104) 8) := by
      simpa only [finishGrowEvents, BitVec.toNat_zero, ↓reduceIte] using hfits_ev
    have hfit_416 : FitsEvents M lim st [.alloc 416] := hfit_ev
    rcases hfit_416 with ⟨⟨_hwma, _henf, _hram, _hva⟩, -⟩
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
    wp_steps_sync_pool (lsmpl.base 45)
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    have hev0 : rustAllocEvents (new.toNat * 104) 8 = growOneEvents 0#64 := by
      simpa only [finishGrowEvents, BitVec.toNat_zero, ↓reduceIte, hnew_toNat] using
        finishGrowEvents_104_eq 0#64
    have hn4 : new.toNat = 4 := rfl
    have hm4 : max 0 4 = 4 := rfl
    rw [hev0, hn4, hm4]
    simp only [List.length_nil, Nat.sub_zero]
    wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    have hcap_nat : cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    have hfit_ev : FitsEvents M lim st (rustReallocEvents (cap.toNat * 104) (new.toNat * 104) 8) := by
      simpa only [finishGrowEvents, hcap_nat, ↓reduceIte] using hfits_ev
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 104›]
    rw [hsub_mul]
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
    wp_steps_sync_pool (lsmpl.base 45)
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    have hev1 : rustReallocEvents (cap.toNat * 104) (new.toNat * 104) 8 = growOneEvents cap := by
      simpa only [finishGrowEvents, hcap_nat, ↓reduceIte, hnew_toNat] using
        finishGrowEvents_104_eq cap
    rw [hev1, ← hnew_toNat]
    wp_done

theorem grow_one_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym cmkShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneSpec M A lim)) := by
  refine subroutine_ok_map (grow_one_raw_placed_ok h_shim h_alloc h_realloc)
    (fun ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 hpre => ⟨((v, cap, ptr, bs), st), R, hpre, fun sf hpost => ?_⟩)
  dsimp only [withLsCodeLoaded, growOneRawSpec, growOneSpec] at hpost ⊢
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨growOneEvents cap, ?_⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, growOneEnv_events cap⟩, hpost.2⟩

theorem grow_one_placed_ok_of_noop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneSpec M A lim)) :=
  grow_one_placed_ok (hookSat_cmkShim_of_noop h_shim) h_alloc h_realloc

theorem grow_one_placed_ok_at_cmk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    GrowOnePlacedOk H A lim :=
  ls_subroutine_ok_of_block (callerProg := (blkPC_24).rebase (blkPl_24).base H)
    (grow_one_placed_ok hA.2.2.1 hA.1 h_realloc)

end LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.CoreBudget
