/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# `FdsGe3Closed`-Threaded Epilogues and Cache-Hit Exit for `Dir::get`

Verifies `.keepsFs` lifts for `bcmp` and `memcpy` together with the `FdsGe3Closed`-threaded
epilogues and cache-hit exit for `Dir::get` on Block 589.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (ls_hook_ok_ultra_of_mem)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName sessionMemcpyRegionSpec withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (strRefAt)
open CryptoVerification.RustHeap (arrayAt vecAt vecHeader vecOf vecU8)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (DirGetGhost DirGhost ReadRule cliBcmpName cliBcmpSpec dirAt dirEntryAt getResultAt)
open CryptoVerification.SignalSession.Cli.Get.Helpers (arrayAt_dirEntry_append dirGhost_get_append_of_ne dirGhost_get_cons_eq frame_0x70_join getResultAt_ok_of_vec memRegion_48_split6 ofNat_beq_zero_false savedRegsAt stackAt_sub_split vecU8At_expose vecU8_of_pos vecU8_of_zero)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_589 lsProg_589)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyBytesAtSpec sessionMemcpyRegionROSpec)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalHooks LibsignalPlacement lsmpl lsρ)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1aFd

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.SignalSession.Cli.Get.PlacedHelpers
  (HighCalleeSaved arrayAt_dirEntry_cons call_lscro_frame cstk_le_pow64 ite_false_eq
   lt_pow64_of_lt_pow32 lt_pow64_of_lt_pow63 ofNat64_toNat_of_lt32 ofNat64_toNat_of_lt63
   pure_sepConj_pure_assoc sepWPp_exists_left sepWPp_pure_mid2
   sepWPp_unfold_vecU8 seq_lscro_state spAligned_of_sp_eq subroutine_ok_lscro_withFsInv
   vecBuf_dirEntry_expose)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false bytesAt_true)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (dealloc_keepsFs_lscro_of_fs session_memcpy_region_keepsFs_lscro_of_fs
   session_memcpy_region_ro_keepsFs_lscro_of_fs shim_keepsFs_lscro_of_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetEnv dirGetEnv_of_hit dirGetPanicQpBudget_false dirGetPanicQpPlacedBudget
   dirGetPostQBudget_of_ret)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `.keepsFs` `bcmp` & `memcpy` Lifts on Block `589` -/

theorem bcmp_keepsFs_lscro_vm_ok_at_589 [LibsignalPlacement] {H : LibsignalHooks}
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs) :
    subroutine_ok (lsProg_589 H) (lsρ cliBcmpName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (withVmPreserved cliBcmpSpec).keepsFs) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem (prog := lsProg_589 H) (i := 589) hBcmp (by decide))

theorem memcpy_bytesAt_keepsFs_lscro_vm_ok_at_589 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H)
    (ro : Bool) :
    subroutine_ok (lsProg_589 H) (lsρ memcpyName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withStack (withVmPreserved (sessionMemcpyBytesAtSpec ro)) extHookStack).keepsFs) := by
  cases ro
  · have hmc := session_memcpy_region_keepsFs_lscro_of_fs (callerProg := lsProg_589 H)
      (stk := extHookStack) hFs
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    obtain ⟨hcrl0, hpre0⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (withStack sessionMemcpyRegionBudgetSpec extHookStack).keepsFs).pre
          (dst, src, bs) s0 ∗ R := by
      apply CryptoVerification.SignalSession.Cli.Store.PlacedCommon.satisfies_lscro_pre hcrl0
      simp only [Spec.keepsFs, withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, bytesAt_false,
        sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1⟩, hpre0.2⟩
    refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs, withStack, withVmPreserved,
        sessionMemcpyBytesAtSpec, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
        memcpyRegionSpec, bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl ⟨‹_›, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨‹_›, ‹_›, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨‹_›, hoom⟩))
  · have hmc_ro := session_memcpy_region_ro_keepsFs_lscro_of_fs (callerProg := lsProg_589 H)
      (stk := extHookStack) hFs
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    obtain ⟨hcrl0, hpre0⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (withStack (withVmPreserved sessionMemcpyRegionROSpec) extHookStack).keepsFs).pre
          (dst, src, bs) s0 ∗ R := by
      apply CryptoVerification.SignalSession.Cli.Store.PlacedCommon.satisfies_lscro_pre hcrl0
      simpa only [Spec.keepsFs, withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionROSpec, bytesAt_true, sepConj_assoc] using hpre0
    refine hmc_ro.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs, withStack, withVmPreserved,
        sessionMemcpyBytesAtSpec, sessionMemcpyRegionROSpec, bytesAt_true,
        sepConj_assoc] using hpost
    · exact Or.inr (Or.inl ⟨‹_›, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨‹_›, ‹_›, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨‹_›, hoom⟩))

/-! ## 2. `FdsGe3Closed`-Threaded Postcondition Helpers for `withFdsGe3Closed (dirGetSpecPlaced …)` -/

def dirGetPostQPlacedBudgetFd [LibsignalPlacement] {M : AllocCostModel}
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) (x : DirGetGhost) (st0 : M.σ) (s0 : State)
    (Fr R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ Fr) →
      (sf.mem ⊨ (withFdsGe3Closed
        (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk)).post (x, st0) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev dirGetPanicQpPlacedBudgetFd [LibsignalPlacement] {M : AllocCostModel}
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) (x : DirGetGhost) (st0 : M.σ) (s0 : State)
    (Fr R : SepProp) : State → SepProp → Prop :=
  dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0 Fr R

theorem dirGetPostQPlacedBudgetFd_perm [LibsignalPlacement] {M : AllocCostModel}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat} {x : DirGetGhost} {st0 : M.σ} {s0 sf : State}
    {Fr R P1 P2 : SepProp}
    (h : dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0 Fr R sf P2)
    (heq : P1 = P2) :
    dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0 Fr R sf P1 :=
  heq ▸ h

theorem dirGetPostQBudgetFd_of_ret [LibsignalPlacement] {M : AllocCostModel}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs : List AllocEvent}
    {s0 sf : State} {r : Except Unit (List (BitVec 8))} {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hfds : FdsGe3Closed sf.fs)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace ∧
      GetEnv s0.fs.files x.dir x.name evs)
    (hsp : sf.sp = s0.sp) (hcs : CalleeSavedPreserved s0 sf) :
    dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
      (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R sf
      ((getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112 ∗
        A.pool lim (M.stepEvents evs st0) sf) ∗ Extra) := by
  have hbase := dirGetPostQBudget_of_ret (M := M) (A := A) (lim := lim) (st0 := st0)
    (pathOk := pathOk) (Extra := Extra) (R := R)
    hstk hfull hres hsp hcs
  refine ⟨fun hm => ?_, hbase.2⟩
  dsimp only [withFdsGe3Closed]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfds, hbase.1 hm⟩

/-! ## 3. Shared Epilogues (`+284` and `+464`) on Block `589` -/

theorem step_epilogue_284_budget_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs : List AllocEvent}
    {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpc : s.pc = (blkPl_589).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfds : FdsGe3Closed s.fs)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace ∧
      GetEnv s0.fs.files x.dir x.name evs) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.pool lim (M.stepEvents evs st0) s) ∗ Extra)
      (dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  dsimp only [lsProg_589]
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.fold (frame_0x70_join (s0.sp - 112#64) s0) (by unfold savedRegsAt; sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine dirGetPostQPlacedBudgetFd_perm
    (dirGetPostQBudgetFd_of_ret (evs := evs) (r := r) (Extra := Extra)
      hstk hfull (by simp only [wp_norm, arm64_norm]; exact hfds)
      ?_ (by simp only [wp_norm, arm64_norm]) ?_)
    (by sep_ac_rfl)
  · exact ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2.1], hres.2.2⟩
  · exact ⟨by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simpa only [wp_norm, arm64_norm] using hhcs.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.2.2.1,
           by simp only [wp_norm, arm64_norm],
           by simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hhcs.2.2.2.2⟩

theorem step_dealloc_epilogue_464_budget_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {pathCap pathPtr pathLenW : BitVec 64} {Extra R : SepProp}
    (hFs : AllocContractsFsPlaced A lim H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hcrl : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 464#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfds : FdsGe3Closed s.fs)
    (hx1 : s.readReg64 .x1 = pathCap)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hcap_ne : pathCap ≠ 0#64) (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace ∧
      GetEnv s0.fs.files x.dir x.name (evs_pre ++ rustDeallocEvents pathCap.toNat 1)) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ pathLenW) ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.repAlloc.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
        A.pool lim (M.stepEvents evs_pre st0) s) ∗ Extra)
      (dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hdealloc := dealloc_keepsFs_lscro_of_fs (callerProg := lsProg_589 H) hFs
  clear hFs
  have hcap_pos : 0 < pathCap.toNat := by
    by_contra h0
    have hz : pathCap.toNat = 0 := by omega
    exact hcap_ne (BitVec.eq_of_toNat_eq (by simpa using hz))
  have hlay : RustLayoutOk pathCap.toNat 1 := ⟨⟨hcap_pos, ⟨0, rfl⟩, by omega⟩, by omega⟩
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
  refine seq_lscro_state (mid := lsρ lsRustDeallocSymCli) hcrl ?_
  dsimp only [lsProg_589]
  wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
  refine call_lscro_frame (x := (pathPtr, pathCap.toNat, 1, M.stepEvents evs_pre st0))
    (T := A.pool lim (M.stepEvents evs_pre st0) _ ∗
      A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
      stackAt (s0.sp - 112#64) extHookStack)
    hdealloc hcrl1 (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp_al)
    (by wp_norm_lhs)
    (by dsimp only [Spec.keepsFs, TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm],
                hlay,
                by simp (config := { decide := true }) only [Reg.x30, Reg.lr, wp_norm, arm64_norm]⟩)
    (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQpBudget_false)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 _ => ?_)
  dsimp only [Spec.keepsFs, TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
  simp only [wp_norm, hsp, sepConj_assoc, ← M.stepEvents_append]
  refine SepWPp.pure_left fun hfs1 => SepWPp.pure_left fun htr1 => ?_
  have hfds1 : FdsGe3Closed sf1.fs := by
    rw [hfs1]; simpa only [wp_norm, arm64_norm] using hfds
  have hhcs1 : HighCalleeSaved s0 sf1 :=
    hhcs.of_step_call hcs1
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
  have hsp1_eq : sf1.sp = s0.sp - 112#64 := by
    rw [hsp1]; simp only [wp_norm, arm64_norm, *]
  have htr1_s : sf1.trace = s.trace := htr1
  have hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ pathLenW) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have hcstk_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
        stackAt (s0.sp - 112#64) extHookStack ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    exact Entails.refl _
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.fold hp24 (by sep_frame)
  apply SepWP.fold hcstk_join (by sep_frame)
  apply SepWP.fold (frame_0x70_join (s0.sp - 112#64) s0) (by unfold savedRegsAt; sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine dirGetPostQPlacedBudgetFd_perm
    (dirGetPostQBudgetFd_of_ret (evs := evs_pre ++ rustDeallocEvents pathCap.toNat 1)
      (r := r) (Extra := Extra)
      hstk hfull (by simp only [wp_norm, arm64_norm]; exact hfds1)
      ?_ (by simp only [wp_norm, arm64_norm]) ?_)
    (by dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)
  · exact ⟨hres.1, by simp only [wp_norm, arm64_norm, htr1_s, hres.2.1], hres.2.2⟩
  · exact ⟨by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simpa only [wp_norm, arm64_norm] using hhcs1.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.2.2.1,
           by simp only [wp_norm, arm64_norm],
           by simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hhcs1.2.2.2.2⟩

/-! ## 4. Cache-Hit Exit (`+112`) on Block `589` -/

theorem step_hit_exit_budget_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {s0 s : State}
    {changedCap changedPtr : BitVec 64}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {bs : List (BitVec 8)} {Extra R : SepProp}
    (hFs : AllocContractsFsPlaced A lim H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hfit0 : FitsEnv M lim st0 (DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name))
    (hGetEnv : ∀ evs, DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name evs →
      GetEnv s0.fs.files x.dir x.name evs)
    (hchanged : x.dir.changed = pre ++ ((x.name, bs) :: rest))
    (hne : ∀ e ∈ pre, e.1 ≠ x.name)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hcrl : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 112#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfds : FdsGe3Closed s.fs)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx23 : s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
        arrayAt (dirEntryAt A.repAlloc) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 24#64) x.dir.path) ∗
        CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 s) ∗ Extra)
      (dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hget : x.dir.get rd s0.fs.files x.name = .ok bs := by
    cases hdir : x.dir with | mk p ch =>
    simp only [hdir] at hchanged ⊢
    rw [hchanged, dirGhost_get_append_of_ne pre ((x.name, bs) :: rest) p rd s0.fs.files x.name hne,
        dirGhost_get_cons_eq]
  have hEnv_eq := dirGetEnv_of_hit (PathEnv := PathEnv) (ReadEnv := ReadEnv)
    (rd := rd) (F0 := s0.fs.files) hchanged hne
  have hrepack_dir :
      (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
        arrayAt (dirEntryAt A.repAlloc) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48))) ∗
        strRefAt (x.self + 24#64) x.dir.path ⊢
      dirAt A.repAlloc x.self x.dir := by
    have hentry_eq :
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest =
        arrayAt (dirEntryAt A.repAlloc) 48 (changedPtr + BitVec.ofNat 64 (48 * pre.length))
          ((x.name, bs) :: rest) := by
      dsimp only [arrayAt, dirEntryAt]
      sep_ac_rfl
    have happ_eq :
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
          arrayAt (dirEntryAt A.repAlloc) 48 (changedPtr + BitVec.ofNat 64 (48 * pre.length))
            ((x.name, bs) :: rest) =
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr x.dir.changed := by
      rw [hchanged, arrayAt_dirEntry_append]
    have hlhs_eq :
        (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
          (if changedCap = 0 then emp
           else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48))) =
        vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr x.dir.changed ∗
          (if changedCap = 0 then emp
           else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48)) := by
      rw [← happ_eq, ← hentry_eq]; sep_ac_rfl
    unfold dirAt vecOf vecAt
    refine sepConj_mono ?_ (Entails.refl _)
    refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
    refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
    rw [vecBuf_dirEntry_expose, hlhs_eq]
    exact sepConj_mono_right (Entails.pure_right hcap_ok (Entails.refl _))
  refine SepWPp.perm
    (P' := vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        arrayAt (dirEntryAt A.repAlloc) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 24#64) x.dir.path) ∗
        CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 s) ∗ Extra))
    ?_ (by sep_frame)
  refine sepWPp_unfold_vecU8 fun valCap valPtr hbs_le hvcap_lt hvptr_ne => ?_
  rw [memRegion_48_split6 x.ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun r0 => sepWPp_exists_left fun r1 =>
    sepWPp_exists_left fun r2 => sepWPp_exists_left fun r3 =>
    sepWPp_exists_left fun r4 => sepWPp_exists_left fun r5 => ?_
  have hbs_lt63 : bs.length < 2 ^ 63 := by omega
  have hbs_lt64 : bs.length < 2 ^ 64 := by omega
  have hv24_32 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) + 8#64 =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64 := by bv_omega
  have hv24_40 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) + 16#64 =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 := by bv_omega
  have hx23_sub8 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-8#64) =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64 := by bv_omega
  rw [hv24_32, hv24_40]
  have hrepack_val :
      ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) ↦₆₄ valCap) ∗
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64) ↦₆₄ valPtr) ∗
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (valPtr ↦ₛ bs) ∗
        (if valCap = 0 then emp
         else A.repAlloc.live valPtr valCap.toNat 1 ∗
           memRegion (valPtr + BitVec.ofNat 64 bs.length) (valCap.toNat - bs.length)) ⊢
      vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs := by
    dsimp only [vecU8]
    refine Entails.trans ?_ (Entails.sepExists_intro valCap)
    refine Entails.trans ?_ (Entails.sepExists_intro valPtr)
    rw [vecU8At_expose, hv24_32, hv24_40]
    exact Entails.pure_right ⟨hbs_le, hvcap_lt, hvptr_ne⟩ (Entails.refl _)
  have hbs_cases : bs = [] ∨ 0 < bs.length := by cases bs <;> simp
  rcases hbs_cases with rfl | hbs_pos
  · clear hFs
    have hevs_nil : GetEnv s0.fs.files x.dir x.name [] := by
      apply hGetEnv
      rw [hEnv_eq]
      rfl
    refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl ?_
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at *
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 284#64)
    have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by bv_omega
    have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by bv_omega
    have hvec0 :
        ((x.ret + 8#64) ↦₆₄ 0#64) ∗ ((x.ret + 16#64) ↦₆₄ 1#64) ∗ ((x.ret + 24#64) ↦₆₄ 0#64) ⊢
        vecU8 A.repAlloc (x.ret + 8#64) [] := by
      have h0 := vecU8_of_zero A.repAlloc (x.ret + 8#64)
      rwa [hret8, hret16] at h0
    apply SepWP.fold hvec0 (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A.repAlloc x.ret r1 r0 []) (by sep_frame)
    apply SepWP.fold hrepack_val (by sep_frame)
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _
    refine SepWPp.perm
      (step_epilogue_284_budget_fd (evs := []) hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm]; exact hfds)
        ⟨hget.symm, by simp only [wp_norm, arm64_norm, *], hevs_nil⟩)
      (by simp only [M.stepEvents_nil]; sep_frame)
  · have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      ofNat_beq_zero_false hbs_pos hbs_lt64
    have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs_lt64]
    have hlay : RustLayoutOk bs.length 1 := ⟨⟨hbs_pos, ⟨0, rfl⟩, by omega⟩, by omega⟩
    have hEnv_pos : DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name
        (rustAllocEvents bs.length 1) := by
      rw [hEnv_eq]
      simp [allocBytes1Events, Nat.ne_of_gt hbs_pos]
    have hfit_bs : FitsEvents M lim st0 (rustAllocEvents bs.length 1) :=
      hfit0 _ hEnv_pos
    have hevs_pos : GetEnv s0.fs.files x.dir x.name (rustAllocEvents bs.length 1) :=
      hGetEnv _ hEnv_pos
    have hshim := shim_keepsFs_lscro_of_fs (callerProg := lsProg_589 H) (stk := extHookStack) hFs
    have halloc := allocNoOom_lscro_of_cli (callerProg := lsProg_589 H)
      (LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget.AllocContractsFsPlaced.toAllocContractsX hFs)
    have hmc := memcpy_bytesAt_keepsFs_lscro_vm_ok_at_589 hFs false
    clear hFs
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    refine seq_lscro_state (mid := lsρ lsRustNoAllocShimSymCli) hcrl ?_
    dsimp only [lsProg_589]
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    refine call_lscro_frame (x := ())
      (T := stackAt (s0.sp - 112#64) extHookStack)
      hshim hcrl1 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [Spec.keepsFs, withStack, sessionShimBudgetSpec, withVmPreserved,
            CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
            emp_sepConj, pure_true_sepConj, wp_norm, hsp])
      trivial (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQpBudget_false)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
    dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hfs1 => SepWPp.pure_left fun hvm1 =>
      SepWPp.pure_left fun htr1 => ?_
    have hfds1 : FdsGe3Closed sf1.fs := by
      rw [hfs1]; simpa only [wp_norm, arm64_norm] using hfds
    refine SepWPp.transport_budgetPool hvm1 (hnext := ?_)
    simp only [wp_norm, hsp, sepConj_assoc]
    have hhcs1 : HighCalleeSaved s0 sf1 :=
      hhcs.of_step_call hcs1
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp1_al : sf1.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
    have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
    have hx19_1 : sf1.readReg64 .x19 = x.ret := by
      have := hcs1.1; simp only [wp_norm, arm64_norm, *] at this; exact this
    have hx20_1 : sf1.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      have := hcs1.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have hx22_1 : sf1.readReg64 .x22 = valPtr := by
      have := hcs1.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have htr1_s0 : sf1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
    refine seq_lscro_state (mid := lsρ lsRustAllocSymCli) hcrl2 ?_
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl3
    refine call_lscro_frame (x := (bs.length, 1, st0))
      (T := A.pool lim st0 _ ∗ stackAt (s0.sp - 112#64) extHookStack)
      halloc hcrl3 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp1_al)
      (by wp_norm_lhs)
      (by dsimp only [TripleRatchet.Hooks2Budget.rustAllocNoOomSpecWithStack,
            rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomSpec]
          simp only [wp_norm, hsp1_eq]; rfl)
      (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm],
                  hlay, hfit_bs,
                  by simp (config := { decide := true }) only [Reg.x30, Reg.lr, wp_norm, arm64_norm]⟩)
      (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQpBudget_false)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 hcrl4 => ?_)
    dsimp only [TripleRatchet.Hooks2Budget.rustAllocNoOomSpecWithStack,
      rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp1_eq, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hacp2, hoom_ne, _⟩ => ?_
    have hfds2 : FdsGe3Closed sf2.fs := by
      rw [hacp2.1]; simpa only [wp_norm, arm64_norm] using hfds1
    set buf := sf2.readReg64 (Reg.gpr 0#5)
    have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
    have hhcs2 : HighCalleeSaved s0 sf2 :=
      hhcs1.of_step_call hcs2
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp2_al : sf2.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp1_al) hsp2
    have hsp2_eq : sf2.sp = s0.sp - 112#64 := by rw [hsp2]; simp only [wp_norm, arm64_norm, *]
    have hx19_2 : sf2.readReg64 .x19 = x.ret := by
      have := hcs2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_1
    have hx20_2 : sf2.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      have := hcs2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_1
    have hx22_2 : sf2.readReg64 .x22 = valPtr := by
      have := hcs2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22_1
    have htr2_s0 : sf2.trace = s0.trace := by
      rw [hacp2.2.1]; simp only [wp_norm, arm64_norm, *]
    refine seq_lscro_state (mid := lsρ memcpyName) hcrl4 ?_
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl5
    refine call_lscro_frame (x := (buf, valPtr, bs))
      (T := memRegion buf bs.length ∗ (valPtr ↦ₛ bs) ∗
        stackAt (s0.sp - 112#64) extHookStack)
      hmc hcrl5 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp2_al)
      (by wp_norm_lhs)
      (by simp only [Spec.keepsFs, withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
            bytesAt_false, sepConj_assoc, wp_norm, hsp2_eq]; rfl)
      (by refine ⟨rfl,
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  by omega⟩)
      (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQpBudget_false)
      (fun sf3 hpc3 hrun3 hsp3 hcs3 hcrl6 => ?_)
    dsimp only [Spec.keepsFs, withStack, withVmPreserved, sessionMemcpyBytesAtSpec, bytesAt_false]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hfs3 => SepWPp.pure_left fun hvm3 =>
      SepWPp.pure_left fun ⟨_, htr3⟩ => ?_
    have hfds3 : FdsGe3Closed sf3.fs := by
      rw [hfs3]; simpa only [wp_norm, arm64_norm] using hfds2
    refine SepWPp.transport_budgetPool hvm3 (hnext := ?_)
    simp only [wp_norm, hsp2_eq, sepConj_assoc]
    have hhcs3 : HighCalleeSaved s0 sf3 :=
      hhcs2.of_step_call hcs3
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp3_eq : sf3.sp = s0.sp - 112#64 := by rw [hsp3]; simp only [wp_norm, arm64_norm, *]
    have hx19_3 : sf3.readReg64 .x19 = x.ret := by
      have := hcs3.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_2
    have hx20_3 : sf3.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      have := hcs3.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_2
    have hx21_3 : sf3.readReg64 .x21 = buf := by
      have := hcs3.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have htr3_s0 : sf3.trace = s0.trace := by rw [htr3]; simp only [wp_norm, arm64_norm, *]
    have hcstk_join :
        memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
          stackAt (s0.sp - 112#64) extHookStack ⊢
        stackAt (s0.sp - 112#64) cstk := by
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
      exact Entails.refl _
    refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl6 ?_
    wp_steps_sync_pool ((blkPl_589).base + 284#64)
    have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by bv_omega
    have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by bv_omega
    have hvec_pos :
        ((x.ret + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((x.ret + 16#64) ↦₆₄ buf) ∗
          ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live buf bs.length 1 ∗ (buf ↦ₛ bs) ⊢
        vecU8 A.repAlloc (x.ret + 8#64) bs := by
      have hp := vecU8_of_pos A.repAlloc (x.ret + 8#64) buf bs hbs_pos hbs_lt63 hoom_ne
      rwa [hret8, hret16] at hp
    simp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm] at hrepack_val hrepack_dir
    apply SepWP.fold hvec_pos (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A.repAlloc x.ret r1 r0 bs) (by sep_frame)
    apply SepWP.fold hrepack_val (by sep_frame)
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.fold hcstk_join (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _
    refine SepWPp.perm
      (step_epilogue_284_budget_fd (evs := rustAllocEvents bs.length 1) hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs3.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm]; exact hfds3)
        ⟨hget.symm, by simp only [wp_norm, arm64_norm, *], hevs_pos⟩)
      (by sep_frame)

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1aFd
