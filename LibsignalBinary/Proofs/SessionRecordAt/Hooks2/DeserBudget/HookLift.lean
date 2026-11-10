/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public meta import ProofLib -- shake: keep
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.Hoare.LibcHooks
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Hook Lifts and `VmPreserved` Basic-Block Steppers

Provides `extHookStack = 16,384` B `NoOom` allocator contracts (`rustCli{Alloc,Dealloc,Realloc}NoOomSpecX`),
`withVmPreserved` leaf/libc hook bridges (`__rust_no_alloc_shim_is_unstable_v2`, `memcpy`, `memmove`),
`AllocContractsBudgetPlaced`, and `by_vm_steps` basic-block steppers preserving `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg LibsignalCodeLoaded
  withLsCodeLoaded withLsCl withMemEq extract_withLsCodeLoaded
  subroutine_ok_withLsCodeLoaded_of_plain
  sepWP_seq_lscl lsmpl lsρ
  lsRustAllocSym lsRustDeallocSym lsRustReallocSym lsRustNoAllocShimSym lsHandleErrorSym
)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionShimSpec sessionMemcpySpec sessionMemmoveSpec
  sessionShim_hookOk hookMemcpy_trace_ok hookMemmove_trace_ok
  ls_externAt?_of_caller ls_hook_ok_of_caller
  ls_subroutine_ok_cl_of_plain_prog ls_subroutine_ok_cl_of_callee
)
open Proofs.libsignal.Hooks2 (subroutine_ok_withLsCodeLoaded_map' subroutine_ok_withLsCl_map')
open Proofs.libsignal.Stage1X (session2ShimSpecX lscall_of_withLsCl)
open ProofLib.StdStartup (hasInstrs)
open VerifiedLibraries.Mallocng.Proofs (memcpySymWords)
open LibsignalBinary.Heap (
  AllocCallPreserved RustLayoutOk VmPreserved
  AllocCostModel BudgetLimits FitsEvents
  rustAllocEvents rustDeallocEvents rustReallocEvents
  RustCliAllocBudget RustAllocAddrs RustCliAllocNoOomEntries
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  allocMemcpyVmSpec allocMemcpyVm_ok_of_hasWords
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack rustCliDeallocNoOomSpecWithStack
  rustCliReallocNoOomSpecWithStack
  subroutine_ok_allocNoOom_withStack_of_hookSat
  subroutine_ok_deallocBudget_withStack_of_hookSat
  subroutine_ok_reallocNoOom_withStack_of_hookSat
)

attribute [local simp, local arm64_norm, local wp_norm] bv_sub_add_lit

/-! ## 1. Layout, Trace, and `withVmPreserved` Combinators -/

theorem rustLayoutOk_of_layoutOk {size align : Nat}
    (hal : align ≤ 2 ^ 31) (h : LayoutOk size align) :
    RustLayoutOk size align :=
  ⟨h, hal⟩

theorem allocCallPreserved_trace_eq {s0 sf : State} (h : AllocCallPreserved s0 sf) :
    sf.trace = s0.trace :=
  h.2.1

/-- Strengthen a `Spec α` postcondition with `⌜VmPreserved s0 sf⌝` so `A.pool lim st s0`
transports across non-allocator calls (`shim`, `memcpy`, `memmove`) via `A.pool_transport`. -/
def withVmPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ spec.post x s0 sf }

theorem vmPreserved_hookNoop (s0 : State) : VmPreserved s0 (hookNoop s0) := by
  unfold hookNoop retHook id
  exact ⟨⟨rfl, rfl, rfl⟩, by cases s0; rfl, fun _ => by cases s0; rfl, fun _ _ _ => by cases s0; rfl⟩

theorem vmPreserved_hookMemcpy (s0 : State) : VmPreserved s0 (hookMemcpy s0) := by
  unfold hookMemcpy retHook
  dsimp only
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, fun _ _ _ => ?_⟩
  · cases s0; rfl
  · cases s0; rfl
  · cases s0; rfl
  · cases s0; rfl
  · intro a
    have hp := congrFun (Memory.perm_writeBytes s0.mem (s0.readReg64 .x0)
      (s0.mem.readBytes (s0.readReg64 .x1) (s0.readReg64 .x2).toNat)) a
    cases s0
    exact hp
  · cases s0; rfl

/-- Lift any `HookOk f spec` witness to `HookOk f (withVmPreserved spec)` when `f` preserves
virtual-memory fields (`VmPreserved s0 (f s0)`) and `trace`. -/
theorem hookOk_withVmPreserved {α : Type} {f : State → State} {spec : Spec α}
    (hok : HookOk f spec) (hvm : ∀ s0, VmPreserved s0 (f s0))
    (htrace : ∀ s0, (f s0).trace = s0.trace := by intro _; rfl) :
    HookOk f (withVmPreserved spec) := by
  refine CryptoVerification.HookTrace.HookOk.of_trace hok (fun _ _ s0 _ hpost => ?_)
    (htrace := htrace)
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm s0, hpost⟩

/-- Concrete `HookOk` witness for `hookNoop` on `withVmPreserved sessionShimSpec`. -/
theorem hookNoop_shimVm_ok : HookOk hookNoop (withVmPreserved sessionShimSpec) :=
  hookOk_withVmPreserved sessionShim_hookOk vmPreserved_hookNoop
    (fun s0 => by simp [hookNoop, retHook])

/-- Concrete `HookOk` witness for `hookMemcpy` on `withVmPreserved (sessionMemcpySpec hookStack)`. -/
theorem hookMemcpy_vm_ok (hookStack : Nat := 4096) :
    HookOk hookMemcpy (withVmPreserved (sessionMemcpySpec hookStack)) :=
  hookOk_withVmPreserved (hookMemcpy_trace_ok hookStack) vmPreserved_hookMemcpy
    (fun s0 => by simp [hookMemcpy, retHook])

/-- Concrete `HookOk` witness for `hookMemmove` on `withVmPreserved (sessionMemmoveSpec hookStack)`. -/
theorem hookMemmove_vm_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (withVmPreserved (sessionMemmoveSpec hookStack)) :=
  hookOk_withVmPreserved (hookMemmove_trace_ok hookStack) vmPreserved_hookMemcpy
    (fun s0 => by simp [hookMemmove, hookMemcpy, retHook])

/-- Stack-slack framing for `withVmPreserved (spec.withHookStack ·)` under `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_withVmPreserved_withHookStack_mono {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withLsCl pl (withVmPreserved (spec.withHookStack s1))))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCl pl (withVmPreserved (spec.withHookStack s2))) := by
  refine subroutine_ok_withLsCl_map' h (fun x R s0 hpre => ?_) h_no_panic h_no_exit h_no_oom
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [← hsplit] at h0
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s2) ∗ R at hpre
    rw [hstack_pre] at hpre
    change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s1) ∗
      (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · intro sf hpost
    change sf.mem ⊨ (⌜VmPreserved s0 sf⌝ ∗ (spec.post x s0 sf ∗ stackAt s0.sp s1)) ∗
      (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) at hpost
    change sf.mem ⊨ (⌜VmPreserved s0 sf⌝ ∗ (spec.post x s0 sf ∗ stackAt s0.sp s2)) ∗ R
    rw [hstack_pre]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

/-! ## 2. Linked-ELF `subroutine_ok` Bridges (`shim` & `memcpy`) -/

/-- `VmPreserved`-preserving no-op contract for `__rustc::__rust_no_alloc_shim_is_unstable_v2()`. -/
def rustAllocShimVmSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝

/-- Discharge `subroutine_ok P shimAddr rustAllocShimVmSpec` from a single `.ret .x30` instruction. -/
theorem rustAllocShimVm_ret_ok {P : Program} {shimAddr : BitVec 64}
    (h : hasInstrs P shimAddr [ .ret .x30 ]) :
    subroutine_ok P shimAddr rustAllocShimVmSpec := by
  apply subroutine_ok_outcome_intro
  intro _ R s0 hpc hrun hpre _hsp
  dsimp only [rustAllocShimVmSpec] at hpre
  rw [emp_sepConj] at hpre
  have hf : P.fetch s0.pc = some (.ret .x30) :=
    hpc ▸ by simpa using h.fetch_off 0 0#64
  apply reaches_outcome_step hrun hf
  have hev : P.evalInst (.ret .x30) s0 = s0.setPC (s0.readReg64 .x30) := by
    simp only [Program.evalInst, execInstWithSvc]
  rw [hev]
  refine reaches_outcome_refl_return rfl hrun ⟨?_, rfl, ?_⟩
  · dsimp only [rustAllocShimVmSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨⟨rfl, rfl, rfl⟩, by cases s0; rfl, fun _ => by cases s0; rfl,
       fun _ _ _ => by cases s0; rfl⟩⟩, hpre⟩
  · rw [CalleeSavedPreserved_setPC]
    unfold CalleeSavedPreserved
    simp [calleeSavedVRegs]

/-- Lift `subroutine_ok P shimAddr rustAllocShimVmSpec` to `withVmPreserved session2ShimSpecX`. -/
theorem session2ShimVm_of_rustAllocShimVm {P : Program} {shimAddr : BitVec 64}
    (h : subroutine_ok P shimAddr rustAllocShimVmSpec) :
    subroutine_ok P shimAddr (withVmPreserved session2ShimSpecX) := by
  refine subroutine_ok_map h (fun x R s0 hpre => ?_)
  refine ⟨x, stackAt s0.sp extHookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withVmPreserved, session2ShimSpecX, Spec.withHookStack, sessionShimSpec] at hpre
    dsimp only [rustAllocShimVmSpec]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · dsimp only [rustAllocShimVmSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hpres, hvm⟩, hstkR⟩
    dsimp only [withVmPreserved, session2ShimSpecX, Spec.withHookStack, sessionShimSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hpres.2.1, hstkR⟩

/-- Linked-ELF discharge of `withVmPreserved session2ShimSpecX` from `[.ret .x30]`. -/
theorem session2ShimVm_ret_ok {P : Program} {shimAddr : BitVec 64}
    (h : hasInstrs P shimAddr [ .ret .x30 ]) :
    subroutine_ok P shimAddr (withVmPreserved session2ShimSpecX) :=
  session2ShimVm_of_rustAllocShimVm (rustAllocShimVm_ret_ok h)

/-- Lift `allocMemcpyVmSpec` (`MallocngBridgeBudget`) to `withVmPreserved (sessionMemcpySpec stk)`. -/
theorem sessionMemcpyVm_of_allocMemcpyVm {P : Program} {memcpyAddr : BitVec 64} {stk : Nat}
    (h : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    subroutine_ok P memcpyAddr (withVmPreserved (sessionMemcpySpec stk)) := by
  refine subroutine_ok_map h (fun ⟨dst, src, bs⟩ R s0 hpre => ?_)
  dsimp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), stackAt s0.sp stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [allocMemcpyVmSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · dsimp only [allocMemcpyVmSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hret, hpres, hvm⟩, hmemf⟩
    dsimp only [withVmPreserved, sessionMemcpySpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hret, hpres.2.1⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemf⟩

/-- Linked-ELF discharge of `withVmPreserved (sessionMemcpySpec stk)` from `musl`'s `memcpySymWords`. -/
theorem sessionMemcpyVm_of_hasWords (P : Program) (memcpyAddr : BitVec 64) {stk : Nat}
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    subroutine_ok P memcpyAddr (withVmPreserved (sessionMemcpySpec stk)) :=
  sessionMemcpyVm_of_allocMemcpyVm (allocMemcpyVm_ok_of_hasWords P memcpyAddr h_no_ext h_words)

/-! ## 3. Stacked `NoOom` Allocator Contracts & `AllocContractsBudgetPlaced` -/

/-- `rustCliAllocNoOomSpec` at `extHookStack = 16,384` B. -/
abbrev rustCliAllocNoOomSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) : Spec (Nat × Nat × M.σ) :=
  rustCliAllocNoOomSpecWithStack M A lim zeroed extHookStack

/-- `rustCliDeallocNoOomSpec` at `extHookStack = 16,384` B. -/
abbrev rustCliDeallocNoOomSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  rustCliDeallocNoOomSpecWithStack M A lim extHookStack

/-- `rustCliReallocNoOomSpec` at `extHookStack = 16,384` B. -/
abbrev rustCliReallocNoOomSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) :=
  rustCliReallocNoOomSpecWithStack M A lim extHookStack

/-- Relocatable `[LibsignalPlacement]` budget-threaded `NoOom` allocator + `shim` + `memcpy` +
panic bundle at `extHookStack = 16,384` B (budget-threaded analogue of `Stage1X.AllocContractsPlaced`
for `deserialize` and `drop` proofs). -/
structure AllocContractsBudgetPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomSpecX M A lim false))
  dealloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomSpecX M A lim))
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustCliReallocNoOomSpecX M A lim))
  shim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (withVmPreserved session2ShimSpecX))
  session_memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (withVmPreserved (sessionMemcpySpec extHookStack)))
  panic_handle_error : H lsHandleErrorSym = some Rust.panicked
  panic_handle_alloc_error :
    H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked

/-- Construct `AllocContractsBudgetPlaced` from block-0 `RustCliAllocNoOomEntries` (`IfaceBudget.lean:694`)
plus `withLsCodeLoaded` contracts for `shim` (`session2ShimVm_ret_ok`) and `memcpy`
(`sessionMemcpyVm_of_hasWords`). -/
theorem AllocContractsBudgetPlaced.of_block0_noOomEntries [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (hEntries : RustCliAllocNoOomEntries M A lim blk0Prog
      { alloc := lsρ lsRustAllocSym,
        dealloc := lsρ lsRustDeallocSym, realloc := lsρ lsRustReallocSym })
    (hshim : subroutine_ok blk0Prog (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl (withVmPreserved session2ShimSpecX)))
    (hmemcpy : subroutine_ok blk0Prog (lsρ "memcpy")
      (withLsCodeLoaded lsmpl (withVmPreserved (sessionMemcpySpec extHookStack))))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    AllocContractsBudgetPlaced M A lim H where
  alloc := ls_subroutine_ok_cl_of_callee (j := 0)
    (subroutine_ok_withLsCodeLoaded_of_plain hEntries.alloc_withStack)
  dealloc := ls_subroutine_ok_cl_of_callee (j := 0)
    (subroutine_ok_withLsCodeLoaded_of_plain hEntries.dealloc_withStack)
  realloc := ls_subroutine_ok_cl_of_callee (j := 0)
    (subroutine_ok_withLsCodeLoaded_of_plain hEntries.realloc_withStack)
  shim := ls_subroutine_ok_cl_of_callee (j := 0) hshim
  session_memcpy := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpy
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

set_option maxRecDepth 2000000 in
/-- Construct `AllocContractsBudgetPlaced` from single-step `HookSat H` assumptions on the
placed external symbol names (`lsRustAllocSym`, `lsRustDeallocSym`, `lsRustReallocSym`,
`lsRustNoAllocShimSym`, `"memcpy"`). -/
theorem AllocContractsBudgetPlaced.of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved sessionShimSpec))
    (hmemcpy : HookSat H "memcpy" (withVmPreserved (sessionMemcpySpec extHookStack)))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    AllocContractsBudgetPlaced M A lim H where
  alloc := fun {callerProg _ _} =>
    ls_subroutine_ok_cl_of_plain_prog
      (subroutine_ok_allocNoOom_withStack_of_hookSat halloc
        (ls_externAt?_of_caller (prog := callerProg)))
  dealloc := fun {callerProg _ _} =>
    ls_subroutine_ok_cl_of_plain_prog
      (subroutine_ok_deallocBudget_withStack_of_hookSat hdealloc
        (ls_externAt?_of_caller (prog := callerProg)))
  realloc := fun {callerProg _ _} =>
    ls_subroutine_ok_cl_of_plain_prog
      (subroutine_ok_reallocNoOom_withStack_of_hookSat hrealloc
        (ls_externAt?_of_caller (prog := callerProg)))
  shim := fun {callerProg _ _} => by
    have h0 : subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
        (withLsCl lsmpl (withVmPreserved (sessionShimSpec.withHookStack 0))) := by
      refine subroutine_ok_withLsCl_map'
        (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hshim))
        fun x R s0 hpre => ⟨x, stackAt s0.sp 0 ∗ R, ?_, fun sf hpost => ?_⟩
      · dsimp only [withVmPreserved, Spec.withHookStack] at hpre ⊢
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      · dsimp only [withVmPreserved, Spec.withHookStack] at hpost ⊢
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    exact subroutine_ok_withLsCl_withVmPreserved_withHookStack_mono (by decide) (by decide) h0
  session_memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

/-- Construct `AllocContractsBudgetPlaced` from allocator `HookSat`s plus concrete `hookNoop` /
`hookMemcpy` entries in `H`. -/
theorem AllocContractsBudgetPlaced.of_concrete_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hshim : H lsRustNoAllocShimSym = some hookNoop)
    (hmemcpy : H "memcpy" = some hookMemcpy)
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    AllocContractsBudgetPlaced M A lim H :=
  AllocContractsBudgetPlaced.of_hooks halloc hdealloc hrealloc
    ⟨hookNoop, hshim, hookNoop_shimVm_ok⟩
    ⟨hookMemcpy, hmemcpy, hookMemcpy_vm_ok extHookStack⟩
    hpan_err hpan_alloc

theorem AllocContractsBudgetPlaced.externAt_handle_error [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    callerProg.externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
  (ls_externAt?_of_caller (sym := lsHandleErrorSym) (by decide)).trans hA.panic_handle_error

theorem AllocContractsBudgetPlaced.externAt_handle_alloc_error [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    callerProg.externAt? (lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") =
      some Rust.panicked :=
  (ls_externAt?_of_caller (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    (by decide)).trans hA.panic_handle_alloc_error

/-! ## 4. `VmPreserved` Basic-Block Steppers (`trapHooks`, `sepWP_rebase_vmPreserved`, `by_vm_steps`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem fetch_withSvc (P : Program) (svc : State → State) (pc : BitVec 64) :
    (P.withSvc svc).fetch pc = P.fetch pc := rfl

/-- Trap-all hook table used with `noSyscalls` in `sepWP_rebase_vmPreserved` so `wp_steps` can
discharge `VmPreserved s sm` across basic blocks containing `STR`/`STP` (`SepWP.step_str*`
quantifies over an abstract `m' : Memory` without `m'.perm = s.mem.perm`). -/
def trapHooks : LibsignalHooks :=
  fun _ => some (fun s => s.setStatus (.Exception "extern"))

private theorem findSome?_override_none :
    ∀ (l : List (String × Nat)) (off : Nat),
      (l.findSome? fun (_n, o) => if o == off then (none : Option (State → State)) else none) = none
  | [], _ => rfl
  | (_n, _o) :: tl, off => by
    dsimp only [List.findSome?]
    rw [ite_self]
    exact findSome?_override_none tl off

private theorem findSome?_trapHooks_some :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then trapHooks n else none) = some f →
      f = fun s => s.setStatus (.Exception "extern")
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons, trapHooks] at h
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte, Option.some.injEq] at h
      exact h.symm
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      exact findSome?_trapHooks_some tl h

private theorem findSome?_stubs_eq_none_of_trapHooks (Hk : LibsignalHooks) :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then trapHooks n else none) = none →
      (l.findSome? fun (n, o) => if o == off then Hk n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    simp only [List.findSome?_cons, trapHooks] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h
      cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_stubs_eq_none_of_trapHooks Hk tl h

private theorem externAt?_rebase_trapHooks_some {P : Program} {b pc : BitVec 64} {f : State → State}
    (h : ((P.rebase b trapHooks).withSvc noSyscalls).externAt? pc = some f) :
    f = fun s => s.setStatus (.Exception "extern") := by
  unfold Program.withSvc Program.externAt? Program.hookAtOff? Program.rebase at h
  dsimp only at h
  rw [findSome?_override_none] at h
  cases hm : (P.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then trapHooks n else none) with
  | none =>
    rw [hm] at h
    cases h
  | some g =>
    rw [hm] at h
    injection h with hgf
    subst hgf
    exact findSome?_trapHooks_some P.stubs hm

private theorem externAt?_rebase_eq_none_of_trapHooks {P : Program} {b pc : BitVec 64}
    {Hk : LibsignalHooks}
    (h : (P.rebase b trapHooks).externAt? pc = none) :
    (P.rebase b Hk).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h ⊢
  dsimp only at h ⊢
  rw [findSome?_override_none] at h ⊢
  have h1 : (P.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then trapHooks n else none) = none := by
    cases hm : (P.stubs.findSome? fun (n, o) =>
        if o == (pc - b).toNat then trapHooks n else none) with
    | none => rfl
    | some g =>
      rw [hm] at h
      cases h
  rw [findSome?_stubs_eq_none_of_trapHooks Hk P.stubs h1]
  rfl

private theorem steps_rebase_trapHooks_noSyscalls {P : Program} {b : BitVec 64}
    {Hk : LibsignalHooks} {s sm : State}
    (hsteps : Steps ((P.rebase b trapHooks).withSvc noSyscalls) s sm)
    (hrun_m : sm.status = .Running) :
    Steps (P.rebase b Hk) s sm ∧ ProofLib.StdStartup.VmFieldsPreserved s sm ∧ sm.fs = s.fs := by
  induction hsteps with
  | refl => exact ⟨Steps.refl _, ProofLib.StdStartup.VmFieldsPreserved.refl _, rfl⟩
  | @step s1 s2 _ h1 hrest ih =>
    have hr2 : s2.status = .Running := by
      cases hrest with
      | refl => exact hrun_m
      | step hs _ => cases hs <;> assumption
    rcases ih hrun_m with ⟨hsteps_rest, hvm_rest, hfs_rest⟩
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern_fault _ _ _ => cases s1; cases hr2
    | extern _ hext _ _ =>
      rw [externAt?_rebase_trapHooks_some hext] at hr2
      cases s1; cases hr2
    | @exec inst hr1 hfe =>
      have hext_trap : (P.rebase b trapHooks).externAt? s1.pc = none := by
        cases he : (P.rebase b trapHooks).externAt? s1.pc with
        | none => rfl
        | some g =>
          unfold Program.fetchMem Program.withSvc at hfe
          change (if (Program.externAt? (P.rebase b trapHooks) s1.pc).isSome then none else _) =
              some inst at hfe
          rw [he] at hfe
          cases hfe
      have hfeH : (P.rebase b Hk).fetchMem s1.mem s1.pc = some inst := by
        have hext_hk := externAt?_rebase_eq_none_of_trapHooks (Hk := Hk) hext_trap
        unfold Program.fetchMem at hfe ⊢
        change (if (Program.externAt? (P.rebase b trapHooks) s1.pc).isSome then none else _) =
            some inst at hfe
        rw [hext_trap] at hfe
        rw [hext_hk]
        exact hfe
      have hnsvc0 : inst.isSvc0 = false := by
        cases ht : inst.isSvc0 with
        | false => rfl
        | true =>
          cases inst with
          | system isHalt imm =>
            cases isHalt with
            | true => simp [Instr.isSvc0] at ht
            | false =>
              simp only [Instr.isSvc0, Bool.not_false, Bool.true_and, beq_iff_eq] at ht
              subst ht
              cases s1; cases hr2
          | _ => simp [Instr.isSvc0] at ht
      have hev1 := ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0
        ((P.rebase b trapHooks).withSvc noSyscalls) hnsvc0 s1
      have hev2 := ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0
        (P.rebase b Hk) hnsvc0 s1
      rw [hev1] at hsteps_rest hvm_rest hfs_rest
      exact ⟨Steps.step (hev2 ▸ Step.exec hr1 hfeH) hsteps_rest,
        ProofLib.StdStartup.VmFieldsPreserved.trans
          (ProofLib.StdStartup.execInst_vmFields_of_not_isSvc0 hnsvc0 s1) hvm_rest,
        hfs_rest.trans (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2.2⟩

/-- Lift a total-correctness `SepWP` on `((P.rebase b trapHooks).withSvc noSyscalls)` to
`P.rebase b Hk` for any `Hk : LibsignalHooks`, supplying `VmPreserved s sm` from
`sm.tpidrEl0 = s.tpidrEl0`. -/
theorem sepWP_rebase_vmPreserved {P : Program} {b : BitVec 64} {Hk : LibsignalHooks}
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) target_pc s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ post sm Pm)) :
    SepWP (P.rebase b Hk) target_pc s Pre (fun sm Pm => VmPreserved s sm ∧ post sm Pm) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hL' : ((P.rebase b trapHooks).withSvc noSyscalls).CodeLoaded s.mem :=
    hL.of_base_code rfl rfl
  obtain ⟨sm, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL'
  rcases hout with ⟨hpc, hrun, Pm, hPm, htp, hpost⟩ | ⟨_, hoom⟩
  · obtain ⟨hsteps_hk, hvm, hfs⟩ := steps_rebase_trapHooks_noSyscalls (Hk := Hk) hsteps hrun
    exact ⟨sm, hsteps_hk, Or.inl ⟨hpc, hrun, Pm, hPm,
      VmPreserved.of_vm_tpidr hvm htp (LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs), hpost⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Sequence a `SepWP` segment up to `mid` under `trapHooks` + `noSyscalls`, continuing on
`P.rebase b Hk` with `VmPreserved s sm` available at `mid` (including `mid = tgt` for epilogues
with `STR`/`STP` before `RET`). -/
theorem sepWP_seq_vmPreserved {P : Program} {b mid tgt : BitVec 64} {Hk : LibsignalHooks}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) tgt sm Pm post))) :
    SepWP (P.rebase b Hk) tgt s Pre post := by
  have h1 := sepWP_rebase_vmPreserved (Hk := Hk) hwp
  apply SepWP.of_reaches_pc
  intro R hm hL
  rcases SepWP.to_reaches_pc h1 hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hvm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ := SepWP.to_reaches_pc (hcont hvm) hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

/-- Sequence a `SepWP` segment up to `mid` on `P.rebase b Hk` while threading both
`VmPreserved s sm` and `LibsignalCodeLoaded pl sm.mem` across `STR`/`STP` steps. -/
theorem sepWP_seq_lscl_vm {P : Program} {b mid tgt : BitVec 64} {Hk : LibsignalHooks}
    {s : State} {Pre : SepProp} {pl : Obj.MultiPlacement} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → LibsignalCodeLoaded pl sm.mem →
          SepWP (P.rebase b Hk) tgt sm Pm post))) :
    SepWP (P.rebase b Hk) tgt s Pre post := by
  have h1 := sepWP_rebase_vmPreserved (Hk := Hk) hwp
  apply SepWP.of_reaches_pc
  intro R hm hL
  rcases SepWP.to_reaches_pc h1 hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hvm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ :=
      SepWP.to_reaches_pc (hcont hvm (hcl.of_keepsFrozen hst1.keepsFrozen)) hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

/-- Panic-aware (`SepWPp`) counterpart of `sepWP_seq_lscl_vm`. -/
theorem sepWPp_seq_lscl_vm {P : Program} {b mid ret : BitVec 64} {Hk : LibsignalHooks}
    {s : State} {Pre : SepProp} {pl : Obj.MultiPlacement}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → LibsignalCodeLoaded pl sm.mem →
          SepWPp (P.rebase b Hk) ret sm Pm Q Qp oom))) :
    SepWPp (P.rebase b Hk) ret s Pre Q Qp oom := by
  have h1 := sepWP_rebase_vmPreserved (Hk := Hk) hwp
  intro R hm hL
  rcases SepWP.to_reaches_pc h1 hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hvm, hcont⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hst2, hout⟩ :=
      (hcont hvm (hcl.of_keepsFrozen hst1.keepsFrozen)) R hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Run `tac` on `SepWP (P.rebase b trapHooks) ...` when the current goal already has outer
program `((P.rebase b trapHooks).withSvc noSyscalls)`, forwarding any remaining continuation
goals (whose programs do not mention `trapHooks`) to the caller. -/
syntax "by_vm_steps_on_withSvc " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| by_vm_steps_on_withSvc $tac:tacticSeq) => do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      unless ty.getAppFn.isConstOf ``SepWP && ty.getAppNumArgs == 6 do
        throwError "by_vm_steps_on_withSvc: expected `SepWP ((P.rebase b trapHooks).withSvc noSyscalls) ...`, got{Lean.indentExpr ty}"
      let e2 := ty.getArg! 0
      unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
        throwError "by_vm_steps_on_withSvc: program is not `Program.withSvc`:{Lean.indentExpr e2}"
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals (rem ++ savedGoals.tail!)
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub => if sub.eqv e1 then some e2 else none
      g.assign prf2

/-- Apply `sepWP_rebase_vmPreserved` and run `tac` on `SepWP (P.rebase b trapHooks) ...`. -/
macro "by_vm_steps " tac:tacticSeq : tactic =>
  `(tactic| (apply sepWP_rebase_vmPreserved; by_vm_steps_on_withSvc $tac))

macro "wp_steps_vm" : tactic => `(tactic| by_vm_steps (wp_steps; wp_done))

/-- Step a `SepWP` goal on `P.rebase b H` up to `mid`, introducing `hvm : VmPreserved s sm` and
`hcl : LibsignalCodeLoaded lsmpl sm.mem` at `mid`. -/
macro "wp_steps_lscl_vm " mid:term " as " hvm:ident hcl:ident : tactic =>
  `(tactic| (
    apply sepWP_seq_lscl_vm ‹_› (mid := $mid)
    by_vm_steps_on_withSvc (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident $hcl:ident))

/-- Step a `SepWPp` goal on `P.rebase b H` up to `mid`, introducing `hvm : VmPreserved s sm` and
`hcl : LibsignalCodeLoaded lsmpl sm.mem` at `mid`. -/
macro "wp_steps_p_lscl_vm " mid:term " as " hvm:ident hcl:ident : tactic =>
  `(tactic| (
    apply sepWPp_seq_lscl_vm ‹_› (mid := $mid)
    by_vm_steps_on_withSvc (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident $hcl:ident))

/-- Step a `SepWP` goal on `P.rebase b H` to its own `target_pc` (e.g. across epilogue `STR`s up
to `RET`), leaving `SepWP (P.rebase b H) target_pc sm Pm post` at `sm.pc = target_pc` with
`hvm : VmPreserved s sm` in context so `SepWP.transport_budgetPool hvm` + `wp_done` closes it. -/
macro "wp_steps_to_tgt_vm" " as " hvm:ident : tactic =>
  `(tactic| (
    apply sepWP_seq_vmPreserved
    by_vm_steps_on_withSvc (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident))

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
