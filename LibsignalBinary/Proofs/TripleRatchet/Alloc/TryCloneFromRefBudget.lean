/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
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
# Budget-Threaded Contract for `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (Block `23`)

Verifies `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` against
`tryCloneFromRefSpec M A lim` on `tripleRatchetProgAt{,Ext}` and under `[LibsignalPlacement]`
(Block `23`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRefBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalPlacement blkPC_23 blkPl_23 libsignalSessionCode lsMemcpySym lsRustAllocSym
  lsRustNoAllocShimSym ls_hook_ok_of_mem lsρ
)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.InImageLift (OptCallInv)
open CryptoVerification.LibsignalTripleRatchet (
  SepWP.seq_optImage boxU8Buf extHookStack specWithOptInv
  subroutine_ok_kit_of_trTrap subroutine_ok_of_optNone trTrapProgAt
  tripleRatchetProgAt tripleRatchetProgAtExt
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk VmPreserved
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase)
open LibsignalBinary.Heap.IfaceBudgetLemmas (subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  AllocContractsBudget AllocContractsXBudget fitsEnv_tryCloneFromRef_iff
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec tryCloneFromRefEvents
  tryCloneFromRefName tryCloneFromRefSpec tryCloneFromRefSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  allocNoOomExtern_opt_of_base allocNoOomExtern_opt_of_x memcpySpecWithStack
  memcpyWithStack_of_framelessMemcpy memcpy_opt_of_base memcpy_opt_of_x
  rebase_trapHooks_fnAddr rustAllocNoOomExternSpecWithStack rustAllocNoOomExternSpecWithStackBase
  sepWP_optImage_rebase_vm shimSpecWithStack shimWithStack_of_noAllocShim shim_opt_of_base
  shim_opt_of_x tryCloneFromRefSpecWithStack
)

private theorem fetch_rebase_withSvc_noSyscalls (P : Program) (b : BitVec 64)
    (Hk : String → Option (State → State)) (pc : BitVec 64) :
    ((P.rebase b Hk).withSvc noSyscalls).fetch pc = (P.rebase b Hk).fetch pc := rfl

private theorem sepWP_seq_optImage_lr {prog : Program} {oimg : Option Obj.Image}
    {target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : OptCallInv oimg s)
    (h : SepWP prog (s.readReg64 .lr) s P
      (fun sm Pm => OptCallInv oimg sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  SepWP.seq_optImage (mid := s.readReg64 .lr) hinv h

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

private theorem stackAt_tryCloneFromRef_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

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

theorem try_clone_from_ref_ok_of_hooks_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (specWithOptInv oimg (rustAllocNoOomExternSpecWithStackBase M A lim false hookStack)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (specWithOptInv oimg (memcpySpecWithStack hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName)
      (specWithOptInv oimg (tryCloneFromRefSpecWithStack M A lim hookStack)) := by
  unfold specWithOptInv tripleRatchetProgAtExt at hshim halloc hmemcpy ⊢
  unfold tryCloneFromRefSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack
  simp only [fitsEnv_tryCloneFromRef_iff, tryCloneFromRefEvents,
    boxU8Buf, stackAt_tryCloneFromRef_opt hstack]
  cells_unfold
  dsimp only [shimSpecWithStack] at hshim
  dsimp only [memcpySpecWithStack] at hmemcpy
  dsimp only [rustAllocNoOomExternSpecWithStackBase,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStackBase,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStackBase,
    RustLayoutOk, LayoutOk, ↓reduceIte] at halloc
  have hfn : libsignalSessionCode.fnOff tryCloneFromRefName =
      num% (ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in") :=
    (ls_lemma% fnOff "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    trapHooks hfn (num% (ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")) 112
  rw [← rebase_trapHooks_fnAddr libsignalSessionCode b (Rust.withPanics ext) tryCloneFromRefName]
    at hshim halloc hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr tryCloneFromRefName = entry
  simp (config := { singlePass := true }) only [← fetch_rebase_withSvc_noSyscalls] at *
  examples_hide_fetches
  wp_init g s0
  rcases g with ⟨⟨src, bs⟩, st⟩
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hx1_eq : (s0.readReg64 Reg.x1).toNat = bs.length := by assumption
  have hx1_bv : s0.readReg64 Reg.x1 = BitVec.ofNat 64 bs.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hbs : bs = []
  · subst hbs
    simp only [List.length_nil, ite_true, sepConj_emp] at hx1_bv ⊢
    wp_steps_opt_vm (s0.readReg64 (Reg.gpr 30#5)) (optCallInv_none _)
    wp_done
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_lt63 : bs.length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos (by omega)
    have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
    have hbound : bs.length + 1 ≤ 2 ^ 63 := by omega
    have hlay : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound⟩
    simp only [hbs, ite_false] at *
    wp_steps_opt_vm
      (entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in"))
      hinv0
    apply sepWP_seq_optImage_lr (by assumption)
    wp_call hshim ()
    refine ProofLib.SepWP.done (by assumption) (by assumption) ?_
    intro hinv1
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    wp_steps_opt_vm
      (entry + bv% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in"))
      hinv1
    apply sepWP_seq_optImage_lr (by assumption)
    wp_call halloc (bs.length, 1, st)
    refine ProofLib.SepWP.done (by assumption) (by assumption) ?_
    intro hinv2
    have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by tauto
    have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
    wp_steps_opt_vm
      (entry + bv% (ls_off% "memcpy" -
        ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in"))
      hinv2
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, src, bs)
    have hvm_mc : VmPreserved sf_1 sf_2 := VmPreserved.trans (by assumption) hpost_2
    refine ProofLib.SepWP.transport_budgetPool hvm_mc (hnext := ?_)
    wp_steps_opt_vm (s0.readReg64 (Reg.gpr 30#5)) (optCallInv_none _)
    wp_done

end FixedBaseSteps

theorem try_clone_from_ref_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName)
      (tryCloneFromRefSpec M A lim) :=
  subroutine_ok_of_optNone <|
    try_clone_from_ref_ok_of_hooks_opt (by decide)
      (shim_opt_of_base hA (name := tryCloneFromRefName)
        (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (allocNoOomExtern_opt_of_base hA (name := tryCloneFromRefName)
        (k := num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (memcpy_opt_of_base hA (name := tryCloneFromRefName)
        (k := num% (ls_off% "memcpy" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))

theorem try_clone_from_ref_ok_trap {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr tryCloneFromRefName)
      (tryCloneFromRefSpec M A lim) :=
  try_clone_from_ref_ok_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA)

/-- `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` meets `tryCloneFromRefSpec M A lim`
on `tripleRatchetProgAt`. -/
theorem try_clone_from_ref_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr tryCloneFromRefName)
      (tryCloneFromRefSpec M A lim) :=
  subroutine_ok_kit_of_trTrap (try_clone_from_ref_ok_trap hA)

theorem try_clone_from_ref_ok_ext_x {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryCloneFromRefName)
      ((tryCloneFromRefSpecX M A lim).inImage img) :=
  try_clone_from_ref_ok_of_hooks_opt (oimg := some img) (by decide)
    (shim_opt_of_x hA (name := tryCloneFromRefName)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
    (allocNoOomExtern_opt_of_x hA (name := tryCloneFromRefName)
      (k := num% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
    (memcpy_opt_of_x hA (name := tryCloneFromRefName)
      (k := num% (ls_off% "memcpy" -
        ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `23`) -/

theorem try_clone_from_ref_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsRustAllocSym) (rustAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hmemcpy : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsMemcpySym) (memcpySpecWithStack hookStack)) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpecWithStack M A lim hookStack) := by
  unfold tryCloneFromRefSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack
  simp only [fitsEnv_tryCloneFromRef_iff, tryCloneFromRefEvents,
    boxU8Buf, stackAt_tryCloneFromRef_opt hstack]
  cells_unfold
  dsimp only [shimSpecWithStack] at hshim
  dsimp only [memcpySpecWithStack] at hmemcpy
  dsimp only [rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    RustLayoutOk, LayoutOk, ↓reduceIte] at halloc
  wp_init g s0
  rcases g with ⟨⟨src, bs⟩, st⟩
  dsimp only at *
  have hx1_eq : (s0.readReg64 Reg.x1).toNat = bs.length := by assumption
  have hx1_bv : s0.readReg64 Reg.x1 = BitVec.ofNat 64 bs.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hbs : bs = []
  · subst hbs
    simp only [List.length_nil, ite_true, sepConj_emp] at hx1_bv ⊢
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_lt63 : bs.length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos (by omega)
    have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
    have hbound : bs.length + 1 ≤ 2 ^ 63 := by omega
    have hlay : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound⟩
    simp only [hbs, ite_false] at *
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs.length, 1, st)
    have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
    have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
    wp_steps_sync_pool (lsρ lsMemcpySym)
    simp only [State.setMem_setMem]
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, src, bs)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-- Relocatable `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (Block `23`) meets
`tryCloneFromRefSpec M A lim`. -/
theorem try_clone_from_ref_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpec M A lim) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
    (memcpyWithStack_of_framelessMemcpy allocHookStack (ls_hook_ok_of_mem hmemcpy))

theorem try_clone_from_ref_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpecX M A lim) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
    (memcpyWithStack_of_framelessMemcpy extHookStack (ls_hook_ok_of_mem hmemcpy))

theorem try_clone_from_ref_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpec M A lim) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))
    (memcpyWithStack_of_framelessMemcpy allocHookStack (ls_hook_ok_of_mem hmemcpy))

theorem try_clone_from_ref_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpecX M A lim) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))
    (memcpyWithStack_of_framelessMemcpy extHookStack (ls_hook_ok_of_mem hmemcpy))

end LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRefBudget
