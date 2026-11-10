/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `AllocContracts4K` Contracts for `finish_grow` (`[local#2, 4, 8]`)

Proves `finish_grow_{8,2,4}_ok_ext_4k` on `tripleRatchetProgAtExt b ext` under
`Hooks4KBudget.AllocContracts4K b A lim ext` (`allocHookStack = 4096`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall allocName reallocName sessionShimSpec shimName tripleRatchetProgAtExt
)
open CryptoVerification.SpqrV1.Alloc (
  finishGrow2Name finishGrow4Name finishGrow8Name
)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustReallocEvents
  subroutine_ok_allocNoOom_of_budgetBase subroutine_ok_reallocNoOom_of_budgetBase
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStackBase rustCliReallocNoOomExternSpecWithStackBase
  subroutine_ok_rustCliAllocNoOom_externWithStackBase
  subroutine_ok_rustCliReallocNoOom_externWithStackBase
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpec finishGrowSpecWithStack
  fitsEnv_finishGrow_iff noAllocShimSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  FinishGrow1Env
  finishGrow1AllocSpecG finishGrow1Events finishGrow1ReallocSpecG
  finishGrow1Spec finishGrow1SpecWithStack
  finishGrow8AllocSpecG finishGrow8ReallocSpecG
  fitsEnv_finishGrow1_iff memRegion_24 session2ShimSpecWithStack
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem fetch_withSvc (P : Program) (svc : State → State) (a : BitVec 64) :
    P.fetch a = (P.withSvc svc).fetch a := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Arithmetic and Stack Helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) =
      0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hs : stride.toNat < 2 ^ 128 := lt_trans stride.isLt (by decide)
  have hn : new.toNat < 2 ^ 128 := lt_trans new.isLt (by decide)
  rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
  have hprod : stride.toNat * new.toNat < 2 ^ 64 := by rw [Nat.mul_comm]; exact h
  rw [Nat.mod_eq_of_lt (lt_trans hprod (by decide)), Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt hprod]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (hlt : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat hlt] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hlt : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hal : align.toNat ≤ 2 ^ 63 := by omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, not_lt]
  rw [mul_stride_toNat hlt, BitVec.toNat_sub_of_le]
  · change new.toNat * stride.toNat ≤ 2 ^ 63 - align.toNat
    omega
  · rw [BitVec.le_def]
    exact hal

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

theorem sepWP_seg_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) target_pc sm Pm post oom))) :
    SepWP (P.rebase b Hk) target_pc s Pre post oom := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved hwp) hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc (hcont hvm) hPm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem sepWPp_seg_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWPp (P.rebase b Hk) ret sm Pm Q Qp oom))) :
    SepWPp (P.rebase b Hk) ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved hwp) hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ := hcont hvm R hPm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

macro "wp_steps_rebase_pool " mid:term : tactic => `(tactic| (
  first
    | apply LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.sepWP_seg_rebase_vm (mid := $mid)
    | apply LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.sepWPp_seg_rebase_vm (mid := $mid)
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨by simp only [wp_norm, arm64_norm], fun _hvm_seg => ?_⟩
  first
    | refine ProofLib.SepWP.transport_budgetPool _hvm_seg (hnext := ?_)
    | refine ProofLib.SepWPp.transport_budgetPool _hvm_seg (hnext := ?_)
  try simp only [Arm64.State.setMem_setMem]
))

/-! ## `AllocContracts4K` Hook Adapters -/

private theorem shim_ok_of_contracts4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (session2ShimSpecWithStack allocHookStack) := by
  refine subroutine_ok_outcome_intro fun () R s0 hpc hrun hpre hsp => ?_
  dsimp only [session2ShimSpecWithStack] at hpre
  have hpre' : s0.mem ⊨ (withVmPreserved sessionShimSpec).pre () s0 ∗
      (stackAt s0.sp allocHookStack ∗ R) := by
    dsimp only [withVmPreserved, sessionShimSpec, noAllocShimSpec]
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine (hA.shim_ok_at name k hk).mono_outcome () (stackAt s0.sp allocHookStack ∗ R)
    s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, sessionShimSpec, noAllocShimSpec, session2ShimSpecWithStack]
      at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (by
      rcases hfail with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩ <;>
        exact (not_satisfies_false_sepConj hq).elim)

private theorem alloc_ok_of_contracts4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomExternSpecWithStackBase M A lim false allocHookStack) :=
  subroutine_ok_rustCliAllocNoOom_externWithStackBase (by decide) (by decide)
    (subroutine_ok_allocNoOom_of_budgetBase (hA.alloc_ok_at name k hk))

private theorem realloc_ok_of_contracts4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocNoOomExternSpecWithStackBase M A lim allocHookStack) :=
  subroutine_ok_rustCliReallocNoOom_externWithStackBase (by decide) (by decide)
    (subroutine_ok_reallocNoOom_of_budgetBase (hA.realloc_ok_at name k hk))

/-! ## `finish_grow` (`[local#8, 2, 4]`) -/

private theorem finish_grow_8_zero_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)))
      (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (rustCliAllocNoOomExternSpecWithStackBase M A lim false hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8AllocSpecG M A lim hookStack) := by
  unfold finishGrow8AllocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% finishGrow8Name) 180
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.libsignalSessionCode] at *
  simp +singlePass only [Program.fnAddr_rebase, fetch_withSvc _ noSyscalls] at *
  clear hfn
  generalize_entry (libsignalSessionCode.fnOff finishGrow8Name) = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩
  dsimp only at *
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hfits_env : FitsEnv M lim st (FinishGrowEnv ⟨out, 0#64, ptr, new, align, stride, []⟩) := by
    assumption
  have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) := by
    simp only [fitsEnv_finishGrow_iff, finishGrowEvents, BitVec.toNat_zero, ↓reduceIte] at hfits_env
    exact hfits_env
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name))
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name))
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrowEvents, BitVec.toNat_zero, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

private theorem finish_grow_8_zero_ok_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8AllocSpecG M A lim allocHookStack) :=
  finish_grow_8_zero_ok_gen (by decide)
    (shim_ok_of_contracts4k hA (name := finishGrow8Name)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name))
      (by fnoff_eq))
    (alloc_ok_of_contracts4k hA (name := finishGrow8Name)
      (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name))
      (by fnoff_eq))

private theorem finish_grow_8_ne_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (rustCliReallocNoOomExternSpecWithStackBase M A lim hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8ReallocSpecG M A lim hookStack) := by
  unfold finishGrow8ReallocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% finishGrow8Name) 180
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.libsignalSessionCode] at *
  simp +singlePass only [Program.fnAddr_rebase, fetch_withSvc _ noSyscalls] at *
  clear hfn
  generalize_entry (libsignalSessionCode.fnOff finishGrow8Name) = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩
  dsimp only at *
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hcap_nat_ne : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
  have hfits_env : FitsEnv M lim st (FinishGrowEnv ⟨out, cap, ptr, new, align, stride, bs⟩) := by
    assumption
  have hfits : FitsEvents M lim st
      (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) := by
    simp only [fitsEnv_finishGrow_iff, finishGrowEvents, hcap_nat_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name))
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrowEvents, hcap_nat_ne, ↓reduceIte]
  wp_done

private theorem finish_grow_8_ne_ok_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8ReallocSpecG M A lim allocHookStack) :=
  finish_grow_8_ne_ok_gen (by decide)
    (realloc_ok_of_contracts4k hA (name := finishGrow8Name)
      (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name))
      (by fnoff_eq))

/-- `finish_grow [local#8]` meets `finishGrowSpec M A lim` under `AllocContracts4K`. -/
theorem finish_grow_8_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrowSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_8_zero_ok_4k hA).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpec, finishGrowSpecWithStack, finishGrow8AllocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfits⟩,
      hmem⟩
  · refine (finish_grow_8_ne_ok_4k hA).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpec, finishGrowSpecWithStack, finishGrow8ReallocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩

private theorem finish_grow_1_of_zero_ne {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow1AllocSpecG M A lim hookStack))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpecG M A lim hookStack)) :
    subroutine_ok P addr (finishGrow1SpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay, hfits⟩, hmem⟩
  · refine hne.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay, hfits⟩, hmem⟩

private theorem finish_grow_2_zero_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow2Name)))
      (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow2Name)))
      (rustCliAllocNoOomExternSpecWithStackBase M A lim false hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1AllocSpecG M A lim hookStack) := by
  unfold finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow2Name)
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% finishGrow2Name) 168
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.libsignalSessionCode] at *
  simp +singlePass only [Program.fnAddr_rebase, fetch_withSvc _ noSyscalls] at *
  clear hfn
  generalize_entry (libsignalSessionCode.fnOff finishGrow2Name) = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, 0#64, ptr, new, []⟩) := by assumption
  have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow2Name))
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow2Name))
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat, 1, st)
  wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrow1Events, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

private theorem finish_grow_2_zero_ok_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1AllocSpecG M A lim allocHookStack) :=
  finish_grow_2_zero_ok_gen (by decide)
    (shim_ok_of_contracts4k hA (name := finishGrow2Name)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow2Name))
      (by fnoff_eq))
    (alloc_ok_of_contracts4k hA (name := finishGrow2Name)
      (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow2Name))
      (by fnoff_eq))

private theorem finish_grow_2_ne_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow2Name)))
      (rustCliReallocNoOomExternSpecWithStackBase M A lim hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1ReallocSpecG M A lim hookStack) := by
  unfold finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow2Name)
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% finishGrow2Name) 168
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.libsignalSessionCode] at *
  simp +singlePass only [Program.fnAddr_rebase, fetch_withSvc _ noSyscalls] at *
  clear hfn
  generalize_entry (libsignalSessionCode.fnOff finishGrow2Name) = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, cap, ptr, new, bs⟩) := by assumption
  have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, hcap_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow2Name))
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs, st)
  wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrow1Events, hcap_ne, ↓reduceIte]
  wp_done

private theorem finish_grow_2_ne_ok_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1ReallocSpecG M A lim allocHookStack) :=
  finish_grow_2_ne_ok_gen (by decide)
    (realloc_ok_of_contracts4k hA (name := finishGrow2Name)
      (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow2Name))
      (by fnoff_eq))

/-- `finish_grow [local#2]` meets `finishGrow1Spec M A lim` under `AllocContracts4K`. -/
theorem finish_grow_2_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1Spec M A lim) :=
  finish_grow_1_of_zero_ne (finish_grow_2_zero_ok_4k hA) (finish_grow_2_ne_ok_4k hA)

private theorem finish_grow_4_zero_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow4Name)))
      (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow4Name)))
      (rustCliAllocNoOomExternSpecWithStackBase M A lim false hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1AllocSpecG M A lim hookStack) := by
  unfold finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow4Name)
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% finishGrow4Name) 168
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.libsignalSessionCode] at *
  simp +singlePass only [Program.fnAddr_rebase, fetch_withSvc _ noSyscalls] at *
  clear hfn
  generalize_entry (libsignalSessionCode.fnOff finishGrow4Name) = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, 0#64, ptr, new, []⟩) := by assumption
  have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow4Name))
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow4Name))
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat, 1, st)
  wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrow1Events, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

private theorem finish_grow_4_zero_ok_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1AllocSpecG M A lim allocHookStack) :=
  finish_grow_4_zero_ok_gen (by decide)
    (shim_ok_of_contracts4k hA (name := finishGrow4Name)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow4Name))
      (by fnoff_eq))
    (alloc_ok_of_contracts4k hA (name := finishGrow4Name)
      (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow4Name))
      (by fnoff_eq))

private theorem finish_grow_4_ne_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow4Name)))
      (rustCliReallocNoOomExternSpecWithStackBase M A lim hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1ReallocSpecG M A lim hookStack) := by
  unfold finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow4Name)
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% finishGrow4Name) 168
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.libsignalSessionCode] at *
  simp +singlePass only [Program.fnAddr_rebase, fetch_withSvc _ noSyscalls] at *
  clear hfn
  generalize_entry (libsignalSessionCode.fnOff finishGrow4Name) = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, cap, ptr, new, bs⟩) := by assumption
  have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, hcap_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow4Name))
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs, st)
  wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrow1Events, hcap_ne, ↓reduceIte]
  wp_done

private theorem finish_grow_4_ne_ok_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1ReallocSpecG M A lim allocHookStack) :=
  finish_grow_4_ne_ok_gen (by decide)
    (realloc_ok_of_contracts4k hA (name := finishGrow4Name)
      (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow4Name))
      (by fnoff_eq))

/-- `finish_grow [local#4]` meets `finishGrow1Spec M A lim` under `AllocContracts4K`. -/
theorem finish_grow_4_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1Spec M A lim) :=
  finish_grow_1_of_zero_ne (finish_grow_4_zero_ok_4k hA) (finish_grow_4_ne_ok_4k hA)

end LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
