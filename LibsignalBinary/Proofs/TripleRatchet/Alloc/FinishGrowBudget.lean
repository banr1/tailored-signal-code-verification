/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public meta import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import Lean.Elab.Tactic -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<alloc::raw_vec::RawVecInner>::finish_grow` (`0x15de4`, Block `45`)

Verifies `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (`0x15de4`, Block `45`) against
`finishGrowSpecWithStack M A lim hookStack` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`, unconditional
`tag = 0#64` under `FitsEnv M lim st (FinishGrowEnv x)`) on `tripleRatchetProgAt{,Ext}` and under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalPlacement blkPC_45 blkPl_45 libsignalSessionCode ls_hook_ok_of_mem
  lsRustAllocSym lsRustNoAllocShimSym lsRustReallocSym lsρ
)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.InImageLift (OptCallInv)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall SepWP.seq_optImage extHookStack finishGrowName
  specWithOptInv subroutine_ok_kit_of_trTrap subroutine_ok_of_optNone
  trTrapProgAt tripleRatchetProgAt tripleRatchetProgAtExt
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliReallocBudgetSpec rustCliReallocNoOomSpec rustReallocEvents
  subroutine_ok_allocNoOom_of_budget subroutine_ok_reallocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliAllocNoOom_externWithStack
  subroutine_ok_rustCliReallocNoOom_externWithStack
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  AllocContractsBudget AllocContractsXBudget
  FinishGrowEnv finishGrowEvents finishGrowSpec finishGrowSpecX fitsEnv_finishGrow_iff
  noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  allocNoOomExtern_opt_of_base allocNoOomExtern_opt_of_x
  finishGrowSpecWithStack rebase_trapHooks_fnAddr
  reallocNoOom_opt_of_base reallocNoOom_opt_of_x
  rustAllocNoOomExternSpecWithStack rustAllocNoOomExternSpecWithStackBase
  rustReallocNoOomExternSpecWithStack rustReallocNoOomExternSpecWithStackBase
  shimSpecWithStack shimWithStack_of_noAllocShim shim_opt_of_base shim_opt_of_x
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Re-exported arithmetic helpers & local layout lemmas -/

abbrev umulh_stride_eq_zero_shared_lb :=
  @CryptoVerification.LibsignalTripleRatchet.umulh_stride_eq_zero_shared_lb
abbrev mul_stride_toNat_shared_lb :=
  @CryptoVerification.LibsignalTripleRatchet.mul_stride_toNat_shared_lb
abbrev mul_stride_eq_ofNat_shared_lb :=
  @CryptoVerification.LibsignalTripleRatchet.mul_stride_eq_ofNat_shared_lb
abbrev mul_stride_ne_zero_shared_lb :=
  @CryptoVerification.LibsignalTripleRatchet.mul_stride_ne_zero_shared_lb
abbrev beq_mul_stride_zero_eq_false_shared_lb :=
  @CryptoVerification.LibsignalTripleRatchet.beq_mul_stride_zero_eq_false_shared_lb
abbrev hi_stride_eq_false_shared_lb :=
  @CryptoVerification.LibsignalTripleRatchet.hi_stride_eq_false_shared_lb

private abbrev umulh_stride_eq_zero := @umulh_stride_eq_zero_shared_lb
private abbrev mul_stride_toNat := @mul_stride_toNat_shared_lb
private abbrev mul_stride_eq_ofNat := @mul_stride_eq_ofNat_shared_lb
private abbrev beq_mul_stride_zero_eq_false := @beq_mul_stride_zero_eq_false_shared_lb
private abbrev hi_stride_eq_false := @hi_stride_eq_false_shared_lb

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrow_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

private theorem instantiate_post_exists {α : Sort _} {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp} {Q : α → State → SepProp} {oom : State → SepProp}
    (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Q w sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom) :
    SepWP prog target_pc s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (∃∗ a, Q a sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  refine SepWP.mono h fun sf P_f _ _ ⟨hq, hsp, hcs⟩ => ⟨fun hm => ?_, hsp, hcs⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨w, hq hm⟩

private theorem optCallInv_none (s : State) : OptCallInv none s := trivial

public meta section

open Lean Meta Elab Tactic Arm64 ProofLib in
/-- Block-structured counterpart of `wp_steps_opt_sync_pool` that elaborates the continuation
`rest` before `instantiateMVars` + `Expr.replace`, ensuring delayed metavariables introduced
under `SepWP.step_str*` / `SepWP.step_stp*` (`fun m' : Memory => ...`) are fully instantiated
and transported to `(P.rebase b trapHooks).withSvc noSyscalls`. -/
elab "wp_steps_opt_vm " mid:term:max hinv:term:max " => " rest:tacticSeq : tactic => do
  let g0 ← getMainGoal
  let isWpp ← g0.withContext do
    let ty0 := (← instantiateMVars (← g0.getType)).consumeMData
    let ty ← if ty0.isAppOfArity ``SepWP 6 || ty0.isAppOfArity ``SepWPp 7 then pure ty0
      else withReducible (whnf ty0)
    if ty.isAppOfArity ``SepWP 6 then pure false
    else if ty.isAppOfArity ``SepWPp 7 then pure true
    else throwError "wp_steps_opt_vm: expected SepWP or SepWPp goal, got{indentExpr ty0}"
  if isWpp then
    evalTactic (← `(tactic|
      apply LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget.sepWPp_optImage_rebase_vm
        (mid := $mid) $hinv))
  else
    evalTactic (← `(tactic|
      apply LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget.sepWP_optImage_rebase_vm
        (mid := $mid) $hinv))
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    unless ty.getAppFn.isConstOf ``ProofLib.SepWP && ty.getAppNumArgs == 6 do
      throwError "wp_steps_opt_vm: expected SepWP on withSvc, got{indentExpr ty}"
    let e2 := ty.getArg! 0
    unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
      throwError "wp_steps_opt_vm: expected Program.withSvc, got{indentExpr e2}"
    let e1 := e2.getArg! 0
    let ty1 := mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← mkFreshExprMVar ty1
    let savedGoals ← getGoals
    setGoals [g1.mvarId!]
    evalTactic (← `(tactic| (
      wp_steps
      refine ProofLib.SepWP.done
        (by first | rfl | wp_norm_lhs | simp only [wp_norm, arm64_norm])
        (by first | assumption | wp_norm_lhs)
        ⟨by first | rfl | simp only [wp_norm, arm64_norm], fun hinv_next hvm_next => ?_⟩
    )))
    if isWpp then
      evalTactic (← `(tactic| (
        try first
          | refine ProofLib.SepWPp.transport_budgetPool hvm_next (hnext := ?_)
          | refine ProofLib.SepWPp.transport_atStatePool hvm_next (hnext := ?_)
      )))
    else
      evalTactic (← `(tactic| (
        try first
          | refine ProofLib.SepWP.transport_budgetPool hvm_next (hnext := ?_)
          | refine ProofLib.SepWP.transport_atStatePool hvm_next (hnext := ?_)
      )))
    evalTactic (← `(tactic| ($rest)))
    let rem ← getGoals
    unless rem.isEmpty do
      throwError "wp_steps_opt_vm: continuation left {rem.length} unsolved goal(s)"
    let prf1 ← instantiateMVars g1
    let prf2 := prf1.replace fun sub =>
      if sub.eqv e2 then some e2
      else if sub.eqv e1 then some e2
      else none
    g.assign prf2
    setGoals savedGoals.tail!

end

/-! ## Case 1: `cap = 0` (`__rust_alloc`) -/

def finishGrowAllocSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrowCall × M.σ) :=
  { finishGrowSpecWithStack M A lim hookStack with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
        FitsEvents M lim st (rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
      memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 48) }

section FixedBaseSteps

attribute [local irreducible] Program.fnOff

theorem finish_grow_zero_ok_of_hooks_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (rustAllocNoOomExternSpecWithStackBase M A lim false hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowAllocSpecWithStack M A lim hookStack)) := by
  unfold specWithOptInv tripleRatchetProgAtExt at hshim halloc ⊢
  unfold finishGrowAllocSpecWithStack finishGrowSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_opt hstack, sepExists_sepConj_left,
    sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrowName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.libsignalSessionBin b
    trapHooks hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) 180
  rw [← rebase_trapHooks_fnAddr libsignalSessionCode b (Rust.withPanics ext) finishGrowName]
    at hshim halloc ⊢
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr finishGrowName = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  subst cap
  subst bs
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  wp_steps_opt_vm
    (entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"))
    hinv0 =>
    apply SepWP.seq_optImage (mid := entry + bv% 108) (by assumption)
    wp_call hshim ()
    refine ProofLib.SepWP.done (by assumption) (by assumption) ?_
    intro hinv1
    refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
    wp_steps_opt_vm
      (entry + bv% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"))
      hinv1 =>
      wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
      have hret_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false :=
        beq_eq_false_iff_ne.mpr (by tauto)
      have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
        mul_stride_eq_ofNat hlt64
      wp_steps_opt_vm (s0.readReg64 .lr) (optCallInv_none _) =>
        simp only [finishGrowEvents]
        apply instantiate_post_exists (sf_1.readReg64 Reg.x0)
        simp only [pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
        wp_done

/-! ## Case 2: `cap ≠ 0` (`__rust_realloc`) -/

def finishGrowReallocSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrowCall × M.σ) :=
  { finishGrowSpecWithStack M A lim hookStack with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
        FitsEvents M lim st
          (rustReallocEvents (x.cap.toNat * x.stride.toNat)
            (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
        (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool lim st s ∗ stackAt s.sp (hookStack + 48) }

theorem finish_grow_ne_ok_of_hooks_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (rustReallocNoOomExternSpecWithStackBase M A lim hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowReallocSpecWithStack M A lim hookStack)) := by
  unfold specWithOptInv tripleRatchetProgAtExt at hrealloc ⊢
  unfold finishGrowReallocSpecWithStack finishGrowSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_opt hstack, sepExists_sepConj_left,
    sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrowName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.libsignalSessionBin b
    trapHooks hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) 180
  rw [← rebase_trapHooks_fnAddr libsignalSessionCode b (Rust.withPanics ext) finishGrowName]
    at hrealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr finishGrowName = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hrlay_old : RustLayoutOk (cap.toNat * stride.toNat) align.toNat :=
    ⟨⟨hold_pos, hpow, by omega⟩, hal31⟩
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  wp_steps_opt_vm
    (entry + bv% (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"))
    hinv0 =>
    wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
    have hret_beq : (sf.readReg64 Reg.x0 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr (by tauto)
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    have hcap_nat_ne : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
    wp_steps_opt_vm (s0.readReg64 .lr) (optCallInv_none _) =>
      simp only [finishGrowEvents, hcap_nat_ne, ↓reduceIte]
      apply instantiate_post_exists (sf.readReg64 Reg.x0)
      wp_done

end FixedBaseSteps

/-! ## Unified Fixed-Base `finish_grow_ok` Theorems -/

theorem finish_grow_ok_of_hooks_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (rustAllocNoOomExternSpecWithStackBase M A lim false hookStack)))
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (specWithOptInv oimg (rustReallocNoOomExternSpecWithStackBase M A lim hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_ok_of_hooks_opt hstack hshim halloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrowAllocSpecWithStack, fitsEnv_finishGrow_iff, finishGrowEvents,
      FinishGrowCall.oldBuf, hcap0, ↓reduceIte, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
  · refine (finish_grow_ne_ok_of_hooks_opt hstack hrealloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    have hcap_nat_ne : x.cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrowReallocSpecWithStack, fitsEnv_finishGrow_iff, finishGrowEvents,
      FinishGrowCall.oldBuf, hcap0, hcap_nat_ne, ↓reduceIte, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfit⟩, hmem⟩

theorem finish_grow_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrowSpec M A lim) :=
  subroutine_ok_of_optNone <|
    finish_grow_ok_of_hooks_opt (by decide)
      (shim_opt_of_base hA (name := finishGrowName)
        (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (allocNoOomExtern_opt_of_base hA (name := finishGrowName)
        (k := num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (reallocNoOom_opt_of_base hA (name := finishGrowName)
        (k := num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))

theorem finish_grow_ok_trap {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr finishGrowName)
      (finishGrowSpec M A lim) :=
  finish_grow_ok_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA)

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (`0x15de4`) meets
`finishGrowSpec M A lim` on `tripleRatchetProgAt`. -/
theorem finish_grow_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr finishGrowName)
      (finishGrowSpec M A lim) :=
  subroutine_ok_kit_of_trTrap (finish_grow_ok_trap hA)

theorem finish_grow_ok_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowName)
      ((finishGrowSpecX M A lim).inImage img) :=
  finish_grow_ok_of_hooks_opt (oimg := some img) (by decide)
    (shim_opt_of_x hA (name := finishGrowName)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
    (allocNoOomExtern_opt_of_x hA (name := finishGrowName)
      (k := num% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
    (reallocNoOom_opt_of_x hA (name := finishGrowName)
      (k := num% (ls_off% "__rustc::__rust_realloc" -
        ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))

/-! ## Relocatable Per-Block Proofs (`[LibsignalPlacement]`, Block `45`) -/

theorem finish_grow_zero_placed_ok_of_hooks_opt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowAllocSpecWithStack M A lim hookStack) := by
  unfold finishGrowAllocSpecWithStack finishGrowSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_opt hstack, sepExists_sepConj_left,
    sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := x
  dsimp only at *
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  subst cap
  subst bs
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hret_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by tauto)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 .lr)
  simp only [finishGrowEvents]
  apply instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

theorem finish_grow_ne_placed_ok_of_hooks_opt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustReallocSym) (rustReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowReallocSpecWithStack M A lim hookStack) := by
  unfold finishGrowReallocSpecWithStack finishGrowSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_opt hstack, sepExists_sepConj_left,
    sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := x
  dsimp only at *
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hrlay_old : RustLayoutOk (cap.toNat * stride.toNat) align.toNat :=
    ⟨⟨hold_pos, hpow, by omega⟩, hal31⟩
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  wp_steps_sync_pool (lsρ lsRustReallocSym)
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hret_beq : (sf.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by tauto)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  have hcap_nat_ne : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
  wp_steps_sync_pool (s0.readReg64 .lr)
  simp only [finishGrowEvents, hcap_nat_ne, ↓reduceIte]
  apply instantiate_post_exists (sf.readReg64 Reg.x0)
  wp_done

theorem finish_grow_placed_ok_of_hooks_opt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustReallocSym) (rustReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_placed_ok_of_hooks_opt hstack hshim halloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrowAllocSpecWithStack, fitsEnv_finishGrow_iff, finishGrowEvents,
      FinishGrowCall.oldBuf, hcap0, ↓reduceIte, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
  · refine (finish_grow_ne_placed_ok_of_hooks_opt hstack hrealloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    have hcap_nat_ne : x.cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrowReallocSpecWithStack, fitsEnv_finishGrow_iff, finishGrowEvents,
      FinishGrowCall.oldBuf, hcap0, hcap_nat_ne, ↓reduceIte, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfit⟩, hmem⟩

/-- Relocatable `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (Block `45`) meets
`finishGrowSpec M A lim` under `HookSat` budget allocator contracts. -/
theorem finish_grow_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpec M A lim) :=
  finish_grow_placed_ok_of_hooks_opt (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
    (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_reallocNoOom_of_budget (ls_hook_ok_of_mem hrealloc)))

theorem finish_grow_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecX M A lim) :=
  finish_grow_placed_ok_of_hooks_opt (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
    (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_reallocNoOom_of_budget (ls_hook_ok_of_mem hrealloc)))

theorem finish_grow_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpec M A lim) :=
  finish_grow_placed_ok_of_hooks_opt (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))
    (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem hrealloc))

theorem finish_grow_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecX M A lim) :=
  finish_grow_placed_ok_of_hooks_opt (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))
    (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem hrealloc))

end LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget
