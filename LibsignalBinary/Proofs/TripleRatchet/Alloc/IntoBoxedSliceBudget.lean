/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSlice
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public meta import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Contract for `<alloc::vec::Vec<u8>>::into_boxed_slice` (Block `56`)

Verifies `<alloc::vec::Vec<u8>>::into_boxed_slice` against `intoBoxedSliceSpec M A lim` on
`tripleRatchetProgAt{,Ext}` and under `[LibsignalPlacement]` (Block `56`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSliceBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalPlacement blkPC_56 blkPl_56 libsignalSessionCode lsRustDeallocSym lsRustReallocSym
  ls_hook_ok_of_mem lsρ
)
open CryptoVerification.RustHeap (LayoutOk allocHookStack vecHeader vecU8At)
open CryptoVerification.InImageLift (OptCallInv)
open CryptoVerification.LibsignalTripleRatchet (
  VecArg boxU8Buf extHookStack specWithOptInv
  subroutine_ok_kit_of_trTrap subroutine_ok_of_optNone trTrapProgAt
  tripleRatchetProgAt tripleRatchetProgAtExt ule_eq_false_of_lt
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
  rustCliDeallocBudgetSpec rustCliReallocBudgetSpec rustCliReallocNoOomSpec
  subroutine_ok_reallocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliDeallocBudget_externWithStack
  subroutine_ok_rustCliReallocNoOom_externWithStack
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  AllocContractsBudget AllocContractsXBudget fitsEnv_intoBoxedSlice_iff intoBoxedSliceEvents
  intoBoxedSliceName intoBoxedSliceSpec intoBoxedSliceSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  dealloc_opt_of_base dealloc_opt_of_x intoBoxedSliceSpecWithStack rebase_trapHooks_fnAddr
  reallocNoOom_opt_of_base reallocNoOom_opt_of_x rustDeallocExternSpecWithStack
  rustDeallocExternSpecWithStackBase rustReallocNoOomExternSpecWithStack
  rustReallocNoOomExternSpecWithStackBase sepWP_optImage_rebase_vm
)

private theorem fetch_rebase_withSvc_noSyscalls (P : Program) (b : BitVec 64)
    (Hk : String → Option (State → State)) (pc : BitVec 64) :
    ((P.rebase b Hk).withSvc noSyscalls).fetch pc = (P.rebase b Hk).fetch pc := rfl

local macro "wp_steps_opt_vm " mid:term:max hinv:term:max : tactic => `(tactic| (
  apply sepWP_optImage_rebase_vm (mid := $mid) $hinv
  wp_steps
  refine ProofLib.SepWP.done
    (by first | rfl | wp_norm_lhs | simp only [wp_norm, arm64_norm])
    (by first | assumption | wp_norm_lhs)
    ⟨by first | rfl | simp only [wp_norm, arm64_norm], fun hinv_next hvm_next => ?_⟩
  refine ProofLib.SepWP.transport_budgetPool hvm_next (hnext := ?_)
))

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_intoBoxedSlice_opt {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp hookStack 4 hstack

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

private theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

private theorem optCallInv_none (s : State) : OptCallInv none s := trivial

section FixedBaseSteps

attribute [local irreducible] Program.fnOff

theorem into_boxed_slice_ok_of_hooks_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))
      (specWithOptInv oimg (rustDeallocExternSpecWithStackBase M A lim hookStack)))
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))
      (specWithOptInv oimg (rustReallocNoOomExternSpecWithStackBase M A lim hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName)
      (specWithOptInv oimg (intoBoxedSliceSpecWithStack M A lim hookStack)) := by
  unfold specWithOptInv tripleRatchetProgAtExt at hdealloc hrealloc ⊢
  unfold intoBoxedSliceSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.intoBoxedSliceSpecWithStack
  simp only [fitsEnv_intoBoxedSlice_iff, intoBoxedSliceEvents,
    VecArg.at, vecU8At, vecHeader, boxU8Buf, stackAt_intoBoxedSlice_opt hstack]
  cells_unfold
  dsimp only [rustDeallocExternSpecWithStackBase,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStackBase,
    RustLayoutOk, LayoutOk] at hdealloc
  dsimp only [rustReallocNoOomExternSpecWithStackBase,
    LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStackBase,
    RustLayoutOk, LayoutOk] at hrealloc
  have hfn : libsignalSessionCode.fnOff intoBoxedSliceName =
      num% (ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice") :=
    (ls_lemma% fnOff "<alloc::vec::Vec<u8>>::into_boxed_slice")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    trapHooks hfn (num% (ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")) 124
  rw [← rebase_trapHooks_fnAddr libsignalSessionCode b (Rust.withPanics ext) intoBoxedSliceName]
    at hdealloc hrealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr intoBoxedSliceName = entry
  simp (config := { singlePass := true }) only [← fetch_rebase_withSvc_noSyscalls] at *
  examples_hide_fetches
  wp_init g s0
  rcases g with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hlen_lt63 : bs.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  rcases Nat.eq_or_lt_of_le hbs_le_cap with hcap_eq | hcap_lt
  · have hcap_bv : BitVec.ofNat 64 bs.length = cap := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen_toNat, hcap_eq]
    rw [hcap_bv]
    have hule : cap.ule cap = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_iff]
    by_cases hcap0 : cap = 0
    · subst hcap0
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero hcap_eq
      subst hbs
      simp only [ite_true, sepConj_emp]
      wp_steps_opt_vm (s0.readReg64 (Reg.gpr 30#5)) (optCallInv_none _)
      wp_done
    · have hbs_ne : bs ≠ [] := by
        intro hnil
        apply hcap0
        apply BitVec.eq_of_toNat_eq
        rw [← hcap_eq, hnil]
        rfl
      simp only [hcap0, hbs_ne, ← hcap_eq, Nat.sub_self, memRegion_zero,
        ite_false, sepConj_emp]
      wp_steps_opt_vm (s0.readReg64 (Reg.gpr 30#5)) (optCallInv_none _)
      wp_done
  · have hnot_le : ¬ cap.toNat ≤ bs.length := Nat.not_le.mpr hcap_lt
    have hcap0 : cap ≠ 0 := by
      intro heq
      subst heq
      change bs.length < 0 at hcap_lt
      omega
    have hpos_cap : 0 < cap.toNat := by omega
    have hbound_cap : cap.toNat + 1 ≤ 2 ^ 63 := by omega
    have hlay_cap : LayoutOk cap.toNat 1 := ⟨hpos_cap, hpow2, hbound_cap⟩
    have hule : cap.ule (BitVec.ofNat 64 bs.length) = false :=
      ule_eq_false_of_lt hcap_lt
    by_cases hbs : bs = []
    · subst hbs
      have hule0 : cap.ule 0#64 = false := hule
      have hnot_le0 : ¬ cap.toNat ≤ 0 := by omega
      simp only [hnot_le0, hcap0, ite_false, List.length_nil,
        pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero, ite_true, emp_sepConj, sepConj_emp]
      wp_steps_opt_vm
        (entry + bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice"))
        hinv0
      wp_call hdealloc (ptr, cap.toNat, 1, st)
      wp_steps_opt_vm (s0.readReg64 (Reg.gpr 30#5)) (optCallInv_none _)
      wp_done
    · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
      have hbound_bs : bs.length + 1 ≤ 2 ^ 63 := by omega
      have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hlay_new : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound_bs⟩
      simp only [hnot_le, hcap0, hbs, ite_false, sepConj_assoc] at *
      wp_steps_opt_vm
        (entry + bv% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice"))
        hinv0
      wp_call hrealloc (ptr, cap.toNat, 1, bs.length, bs, st)
      have hne : sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by tauto
      have hbeq : (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
      simp only [Nat.sub_self, memRegion_zero]
      wp_steps_opt_vm (s0.readReg64 (Reg.gpr 30#5)) (optCallInv_none _)
      wp_done

end FixedBaseSteps

theorem into_boxed_slice_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName)
      (intoBoxedSliceSpec M A lim) :=
  subroutine_ok_of_optNone <|
    into_boxed_slice_ok_of_hooks_opt (by decide)
      (dealloc_opt_of_base hA (name := intoBoxedSliceName)
        (k := num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))
      (reallocNoOom_opt_of_base hA (name := intoBoxedSliceName)
        (k := num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))

theorem into_boxed_slice_ok_trap {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr intoBoxedSliceName)
      (intoBoxedSliceSpec M A lim) :=
  into_boxed_slice_ok_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA)

/-- `<alloc::vec::Vec<u8>>::into_boxed_slice` meets `intoBoxedSliceSpec M A lim` on
`tripleRatchetProgAt`. -/
theorem into_boxed_slice_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr intoBoxedSliceName)
      (intoBoxedSliceSpec M A lim) :=
  subroutine_ok_kit_of_trTrap (into_boxed_slice_ok_trap hA)

theorem into_boxed_slice_ok_ext_x {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr intoBoxedSliceName)
      ((intoBoxedSliceSpecX M A lim).inImage img) :=
  into_boxed_slice_ok_of_hooks_opt (oimg := some img) (by decide)
    (dealloc_opt_of_x hA (name := intoBoxedSliceName)
      (k := num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))
    (reallocNoOom_opt_of_x hA (name := intoBoxedSliceName)
      (k := num% (ls_off% "__rustc::__rust_realloc" -
        ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `56`) -/

theorem into_boxed_slice_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_56).rebase (blkPl_56).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim hookStack))
    (hrealloc : subroutine_ok ((blkPC_56).rebase (blkPl_56).base H)
      (lsρ lsRustReallocSym) (rustReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_56).rebase (blkPl_56).base H) (blkPl_56).base
      (intoBoxedSliceSpecWithStack M A lim hookStack) := by
  unfold intoBoxedSliceSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.intoBoxedSliceSpecWithStack
  simp only [fitsEnv_intoBoxedSlice_iff, intoBoxedSliceEvents,
    VecArg.at, vecU8At, vecHeader, boxU8Buf, stackAt_intoBoxedSlice_opt hstack]
  cells_unfold
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
    RustLayoutOk, LayoutOk] at hdealloc
  dsimp only [rustReallocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack,
    RustLayoutOk, LayoutOk] at hrealloc
  wp_init g s0
  rcases g with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hlen_lt63 : bs.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  rcases Nat.eq_or_lt_of_le hbs_le_cap with hcap_eq | hcap_lt
  · have hcap_bv : BitVec.ofNat 64 bs.length = cap := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen_toNat, hcap_eq]
    rw [hcap_bv]
    have hule : cap.ule cap = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_iff]
    by_cases hcap0 : cap = 0
    · subst hcap0
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero hcap_eq
      subst hbs
      simp only [ite_true, sepConj_emp]
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      wp_done
    · have hbs_ne : bs ≠ [] := by
        intro hnil
        apply hcap0
        apply BitVec.eq_of_toNat_eq
        rw [← hcap_eq, hnil]
        rfl
      simp only [hcap0, hbs_ne, ← hcap_eq, Nat.sub_self, memRegion_zero,
        ite_false, sepConj_emp]
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      wp_done
  · have hnot_le : ¬ cap.toNat ≤ bs.length := Nat.not_le.mpr hcap_lt
    have hcap0 : cap ≠ 0 := by
      intro heq
      subst heq
      change bs.length < 0 at hcap_lt
      omega
    have hpos_cap : 0 < cap.toNat := by omega
    have hbound_cap : cap.toNat + 1 ≤ 2 ^ 63 := by omega
    have hlay_cap : LayoutOk cap.toNat 1 := ⟨hpos_cap, hpow2, hbound_cap⟩
    have hule : cap.ule (BitVec.ofNat 64 bs.length) = false :=
      ule_eq_false_of_lt hcap_lt
    by_cases hbs : bs = []
    · subst hbs
      have hule0 : cap.ule 0#64 = false := hule
      have hnot_le0 : ¬ cap.toNat ≤ 0 := by omega
      simp only [hnot_le0, hcap0, ite_false, List.length_nil,
        pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero, ite_true, emp_sepConj, sepConj_emp]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc (ptr, cap.toNat, 1, st)
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      wp_done
    · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
      have hbound_bs : bs.length + 1 ≤ 2 ^ 63 := by omega
      have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hlay_new : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound_bs⟩
      simp only [hnot_le, hcap0, hbs, ite_false, sepConj_assoc] at *
      wp_steps_sync_pool (lsρ lsRustReallocSym)
      simp only [State.setMem_setMem]
      wp_call hrealloc (ptr, cap.toNat, 1, bs.length, bs, st)
      have hne : sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
      have hbeq : (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
      simp only [Nat.sub_self, memRegion_zero]
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      wp_done

/-- Relocatable `<alloc::vec::Vec<u8>>::into_boxed_slice` (Block `56`) meets
`intoBoxedSliceSpec M A lim`. -/
theorem into_boxed_slice_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_56).rebase (blkPl_56).base H) (blkPl_56).base
      (intoBoxedSliceSpec M A lim) :=
  into_boxed_slice_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (subroutine_ok_rustCliDeallocBudget_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem hdealloc))
    (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_reallocNoOom_of_budget (ls_hook_ok_of_mem hrealloc)))

theorem into_boxed_slice_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_56).rebase (blkPl_56).base H) (blkPl_56).base
      (intoBoxedSliceSpecX M A lim) :=
  into_boxed_slice_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (subroutine_ok_rustCliDeallocBudget_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem hdealloc))
    (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_reallocNoOom_of_budget (ls_hook_ok_of_mem hrealloc)))

theorem into_boxed_slice_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_56).rebase (blkPl_56).base H) (blkPl_56).base
      (intoBoxedSliceSpec M A lim) :=
  into_boxed_slice_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (subroutine_ok_rustCliDeallocBudget_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem hdealloc))
    (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem hrealloc))

theorem into_boxed_slice_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_56).rebase (blkPl_56).base H) (blkPl_56).base
      (intoBoxedSliceSpecX M A lim) :=
  into_boxed_slice_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (subroutine_ok_rustCliDeallocBudget_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem hdealloc))
    (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem hrealloc))

end LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSliceBudget
