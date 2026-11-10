/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlaced
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Per-Block Proofs for `AllocAndVec`

Proves `RustCliAllocBudget M` total-correctness and conditional-OOM contracts under `RustLayoutOk`
(`align ≤ 2 ^ 31`) for Block `588` (`RawVecInner::try_allocate_in`, `[LibsignalPlacement]`) and
`VmPreserved`-strengthened contracts for Block `55` (`Vec<u8>::append_elements`,
`[LibsignalFullPlacement]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalPlacement LibsignalFullPlacement LibsignalHooks IsLsBlockProg
  blkPC_588 blkPl_588 blkPC_55 blkPl_55 lsmpl lsρ
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym ls_hook_ok_any
  withLsCodeLoaded ls_subroutine_ok_of_block subroutine_ok_withLsCodeLoaded_of_plain
  full_ls_subroutine_ok_of_plain libsignalSessionLib
)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (finishGrowStack SepWP.instantiate_post_exists)
open CryptoVerification.E2E.Pqxdh.Shared (TryAllocateInCall VecAppendFastCall)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimSpec framelessMemcpySpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecBudget (
  tryAllocateInEvents TryAllocateInEnv fitsEvents_tryAllocateIn_of_fitsEnv
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Arithmetic, Memory, and VM-Stepping Helpers -/

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

private theorem sepWP_vm_trans {prog : Program} {target : BitVec 64} {s0 s : State}
    {Pre : SepProp} {post : State → SepProp → Prop}
    (h0 : VmPreserved s0 s)
    (h : SepWP prog target s Pre (fun sf P_f => VmPreserved s sf ∧ post sf P_f)) :
    SepWP prog target s Pre (fun sf P_f => VmPreserved s0 sf ∧ post sf P_f) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm, hp⟩ => ⟨h0.trans hvm, hp⟩

private theorem sepWP_cut_vm {P : Program} {b mid ret : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) ret sm Pm post oom))) :
    SepWP (P.rebase b Hk) ret s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hsteps1, ⟨_, _, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc h hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      SepWP.to_reaches_pc (hcont hvm) hPm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]
  omega

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_tryAllocateIn (sp : BitVec 64) :
    stackAt sp finishGrowStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 4096 6 (by decide)

private theorem hi_append_eq_false {cap len n : Nat}
    (hle : len + n ≤ cap) (hcap : cap < 2 ^ 64) :
    (BitVec.ofNat 64 cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 n) = false := by
  have hlen : len < 2 ^ 64 := by omega
  have hn : n < 2 ^ 64 := by omega
  have hsub : (BitVec.ofNat 64 cap - BitVec.ofNat 64 len).toNat = cap - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hlen]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hlen]
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  omega

private theorem ofNat_beq_zero_eq_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

/-! ## Block `588`: `RawVecInner::try_allocate_in` (`[LibsignalPlacement]`) -/

/-- Total-correctness (`FitsEnv`) budget contract under `RustLayoutOk` (`align ≤ 2 ^ 31`) for
`<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (Block `588`). -/
def tryAllocateInSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryAllocateInCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEnv M lim st (TryAllocateInEnv x)⌝ ∗
    memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp finishGrowStack
  post := (AllocAndVecBudget.tryAllocateInSpec M A lim).post

/-- Conditional-OOM budget contract under `RustLayoutOk` (`align ≤ 2 ^ 31`) for
`<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (Block `588`). -/
def tryAllocateInCondSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryAllocateInCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp finishGrowStack
  post := (AllocAndVecBudget.tryAllocateInCondSpec M A lim).post
  onOom := (AllocAndVecBudget.tryAllocateInCondSpec M A lim).onOom

theorem tryAllocateIn2_noOom_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim' : subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec)
    (halloc' : subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (blkPl_588).base
      (tryAllocateInSpec M A lim) := by
  unfold tryAllocateInSpec AllocAndVecBudget.tryAllocateInSpec
  simp only [memRegion_24, stackAt_tryAllocateIn, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  dsimp only [noAllocShimSpec, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec] at hshim'
  dsimp only [rustCliAllocNoOomSpec] at halloc'
  wp_init xst s0
  obtain ⟨⟨out, new, align, stride⟩, st⟩ := xst
  dsimp only at *
  rcases ‹RustLayoutOk (new.toNat * stride.toNat) align.toNat› with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hfitEvs : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) :=
    fitsEvents_tryAllocateIn_of_fitsEnv M lim st ⟨out, new, align, stride⟩
      ‹FitsEnv M lim st (TryAllocateInEnv ⟨out, new, align, stride⟩)›
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (new.toNat * stride.toNat, align.toNat, st)
  have hne0 : sf_1.readReg64 .x0 ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  have htr_all : sf_1.trace = s0.trace := ‹AllocCallPreserved _ sf_1›.2.1.trans ‹sf.trace = s0.trace›
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply SepWP.instantiate_post_exists (tryAllocateInEvents ⟨out, new, align, stride⟩)
  apply SepWP.instantiate_post_exists (sf_1.readReg64 .x0)
  dsimp only [tryAllocateInEvents, TryAllocateInEnv]
  wp_done

theorem tryAllocateIn2_noOom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (blkPl_588).base
      (tryAllocateInSpec M A lim) :=
  tryAllocateIn2_noOom_placed_ok_of_contracts (ls_hook_ok_any hshim) (ls_hook_ok_any halloc)

/-- Relocatable `<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (Block `588`, unmutated)
meets `tryAllocateInSpec M A lim` from conditional-OOM `rustCliAllocBudgetSpec` hooks. -/
theorem tryAllocateIn2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (blkPl_588).base
      (tryAllocateInSpec M A lim) :=
  tryAllocateIn2_noOom_placed_ok_of_contracts (ls_hook_ok_any hshim)
    (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_any halloc))

theorem tryAllocateIn2_placed_ok_cl [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 588)
      (withLsCodeLoaded lsmpl (tryAllocateInSpec M A lim)) :=
  ls_subroutine_ok_of_block (j := 588)
    (subroutine_ok_withLsCodeLoaded_of_plain (tryAllocateIn2_placed_ok hshim halloc)) hi

/-- Per-call specialization of `AllocAndVecBudget.tryAllocateInSpec` at any `x` with
`x.align.toNat ≤ 2 ^ 31`. -/
theorem tryAllocateIn2_at_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : TryAllocateInCall) (hal : x.align.toNat ≤ 2 ^ 31)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_588).rebase (blkPl_588).base H)
      (blkPl_588).base
      { pre := fun (st : M.σ) s => (AllocAndVecBudget.tryAllocateInSpec M A lim).pre (x, st) s
        post := fun (st : M.σ) s0 sf => (AllocAndVecBudget.tryAllocateInSpec M A lim).post (x, st) s0 sf } := by
  have hbase := tryAllocateIn2_placed_ok hshim halloc
  refine subroutine_ok_outcome_intro fun st R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (tryAllocateInSpec M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [AllocAndVecBudget.tryAllocateInSpec, tryAllocateInSpec] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨h0, h1, h2, h3, h4, h5, hlay, hfit⟩, hrest⟩
    exact ⟨⟨h0, h1, h2, h3, h4, h5, ⟨hlay, hal⟩, hfit⟩, hrest⟩
  exact hbase.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun _ hout => hout

/-! ## Block `55`: `Vec<u8>::append_elements` (`[LibsignalFullPlacement]`) -/

/-- `VmPreserved`-strengthened fast-path contract for `<Vec<u8>>::append_elements` (Block `55`). -/
def pqxdhVecAppendElementsFastSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.Shared.pqxdhVecAppendElementsFastSpec

/-- `VmPreserved`-strengthened general fast-path contract for `<Vec<u8>>::append_elements`
(Block `55`). -/
def vecAppendElementsGenFastSpec : Spec VecAppendFastCall :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.Shared.vecAppendElementsGenFastSpec

/-- Relocatable fast-path `<alloc::vec::Vec<u8>>::append_elements` (`128 + 32 ≤ 192`, Block `55`)
meets `pqxdhVecAppendElementsFastSpec` under `[LibsignalFullPlacement]`. -/
theorem vecAppendElements_fast_placed_ok [LibsignalFullPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_55).rebase (blkPl_55).base H)
      (blkPl_55).base
      pqxdhVecAppendElementsFastSpec := by
  unfold pqxdhVecAppendElementsFastSpec
  apply subroutine_ok_withVmPreserved_intro
  have hmemcpy' : subroutine_ok ((blkPC_55).rebase (blkPl_55).base H)
      (lsρ lsMemcpySym) framelessMemcpySpec := ls_hook_ok_any hmemcpy
  dsimp only [framelessMemcpySpec, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec] at hmemcpy'
  intro ⟨vecHdr, vecPtr, srcPtr, bs⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [CryptoVerification.E2E.Pqxdh.Shared.pqxdhVecAppendElementsFastSpec] at *
  cells_unfold
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨rfl, rfl, hx2, hbs32⟩
  apply sepWP_cut_vm (mid := lsρ lsMemcpySym)
  by_vm_steps (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [← hbs32]
    wp_call hmemcpy' (vecPtr + 128#64, s0.readReg64 (.gpr 1#5), bs)
    simp only [hbs32] at *
    have hvm12 : VmPreserved s0 sf := hvm1.trans ‹VmPreserved _ sf›
    have htr : sf.trace = s0.trace := by simp_all
    apply sepWP_vm_trans hvm12
    by_vm_steps (wp_steps; wp_done))

theorem vecAppendElements_fast_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec) :=
  full_ls_subroutine_ok_of_plain (j := 55) (vecAppendElements_fast_placed_ok hmemcpy)

/-- Relocatable general fast-path `<alloc::vec::Vec<u8>>::append_elements` (`len + bs.length ≤ cap`,
Block `55`) meets `vecAppendElementsGenFastSpec` under `[LibsignalFullPlacement]`. -/
theorem vecAppendElements_gen_fast_placed_ok [LibsignalFullPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_55).rebase (blkPl_55).base H)
      (blkPl_55).base
      vecAppendElementsGenFastSpec := by
  unfold vecAppendElementsGenFastSpec
  apply subroutine_ok_withVmPreserved_intro
  have hmemcpy' : subroutine_ok ((blkPC_55).rebase (blkPl_55).base H)
      (lsρ lsMemcpySym) framelessMemcpySpec := ls_hook_ok_any hmemcpy
  dsimp only [framelessMemcpySpec, LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec] at hmemcpy'
  intro ⟨vecHdr, vecPtr, srcPtr, cap, len, bs⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [CryptoVerification.E2E.Pqxdh.Shared.vecAppendElementsGenFastSpec] at *
  cells_unfold
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨rfl, rfl, hx2, hle, hcap⟩
  have hhi := hi_append_eq_false hle hcap
  cases bs with
  | nil =>
    simp only [List.length_nil, Nat.add_zero,
      memRegion_zero, pointsToBytes_nil] at *
    by_vm_steps (wp_steps; wp_done)
  | cons b0 bs' =>
    have hpos : 0 < (b0 :: bs').length := by simp
    have hlt : (b0 :: bs').length < 2 ^ 64 := by omega
    have hcbz := ofNat_beq_zero_eq_false hpos hlt
    apply sepWP_cut_vm (mid := lsρ lsMemcpySym)
    by_vm_steps (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      wp_call hmemcpy' (vecPtr + BitVec.ofNat 64 len, s0.readReg64 (.gpr 1#5), b0 :: bs')
      have hvm12 : VmPreserved s0 sf := hvm1.trans ‹VmPreserved _ sf›
      have htr : sf.trace = s0.trace := by simp_all
      apply sepWP_vm_trans hvm12
      by_vm_steps (wp_steps; wp_done))

abbrev vecAppendElements1_gen_fast_placed_ok [LibsignalFullPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :=
  vecAppendElements_gen_fast_placed_ok hmemcpy

abbrev vecAppendElements2_gen_fast_placed_ok [LibsignalFullPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :=
  vecAppendElements_gen_fast_placed_ok hmemcpy

theorem vecAppendElements_gen_fast_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl vecAppendElementsGenFastSpec) :=
  full_ls_subroutine_ok_of_plain (j := 55) (vecAppendElements_gen_fast_placed_ok hmemcpy)

end LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
