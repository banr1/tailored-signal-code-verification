/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1aFd
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# `FdsGe3Closed`-Threaded Loop Advance and Entry-Scan Loop for `Dir::get`

Verifies `step_loop_advance_budget_fd` (`+68`..`+80` / `+164`) and `step_loop_budget_fd`
(`+80`..`+108`) for `Dir::get` on Block 589.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles TraceFsSound)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (strRefAt)
open CryptoVerification.RustHeap (arrayAt vecAt vecHeader vecOf vecU8)
open CryptoVerification.SignalSession.Cli (DirGetGhost DirGhost ReadRule cliBcmpName cliBcmpSpec dirAt dirEntryAt withFsInv)
open CryptoVerification.SignalSession.Cli.Get.Helpers (arrayAt_dirEntry_append files_eq_of_fsInv_trace_eq fsInv_of_files_trace_eq savedRegsAt stackAt_sub_split vecU8At_expose)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_589 lsProg_589)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv false_of_fsInv_false_budget panicQpBudget_of_fsInv_false)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1bFd

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.SignalSession.Cli.Get.PlacedHelpers
  (HighCalleeSaved arrayAt_dirEntry_cons call_lscro_frame cstk_le_pow64 ite_false_eq
   lt_pow64_of_lt_pow32 lt_pow64_of_lt_pow63 ofNat64_toNat_of_lt32 ofNat64_toNat_of_lt63
   sepWPp_exists_left sepWPp_pure_mid2
   sepWPp_unfold_vecU8 seq_lscro_state spAligned_of_sp_eq subroutine_ok_lscro_withFsInv
   vecBuf_dirEntry_expose)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false bytesAt_true)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1aFd
  (bcmp_keepsFs_lscro_vm_ok_at_589 dirGetPanicQpPlacedBudgetFd dirGetPostQPlacedBudgetFd
   step_hit_exit_budget_fd)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Loop Advance (`+68`..`+80` / `+164`) on Block `589` -/

private theorem sub48_cons_len
    {hd : List (BitVec 8) × List (BitVec 8)}
    {rest : List (List (BitVec 8) × List (BitVec 8))} :
    BitVec.ofNat 64 (48 * (hd :: rest).length) - 48#64 =
      BitVec.ofNat 64 (48 * rest.length) := by
  have hbeq : BitVec.ofNat 64 (48 * (hd :: rest).length) =
      BitVec.ofNat 64 (48 * rest.length) + 48#64 := by
    rw [List.length_cons, Nat.mul_add_one, ← BitVec.ofNat_add]
  rw [hbeq]
  bv_bits

private theorem ofNat48_beq_48_false
    {hd nxt : List (BitVec 8) × List (BitVec 8)}
    {tail : List (List (BitVec 8) × List (BitVec 8))}
    (hlt : 48 * (hd :: nxt :: tail).length < 2 ^ 63) :
    (BitVec.ofNat 64 (48 * (hd :: nxt :: tail).length) == 48#64) = false := by
  have hlt64 : 48 * (hd :: nxt :: tail).length < 2 ^ 64 := lt_pow64_of_lt_pow63 hlt
  clear hlt
  apply beq_false_of_ne
  intro h
  have ht : (BitVec.ofNat 64 (48 * (hd :: nxt :: tail).length)).toNat = (48#64).toNat :=
    congrArg BitVec.toNat h
  have h48_nat : (48#64).toNat = 48 := rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, h48_nat] at ht
  clear hlt64 h48_nat h
  simp only [List.length_cons] at ht
  omega

theorem step_loop_advance_budget_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {s0 sm : State}
    {changedCap changedPtr : BitVec 64}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {hdName hdBytes : List (BitVec 8)}
    {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hchanged : x.dir.changed = pre ++ (hdName, hdBytes) :: rest)
    (hne : ∀ e ∈ pre, e.1 ≠ x.name)
    (hhd_ne : hdName ≠ x.name)
    (hmiss : ∀ sm : State,
      sm.pc = (blkPl_589).base + 164#64 →
      sm.status = .Running →
      sm.spAligned = true →
      sm.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sm →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs →
      sm.fs.files = s0.fs.files →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sm.readReg64 .x21 = x.self →
      sm.readReg64 .x22 = x.nameA →
      (∀ e ∈ x.dir.changed, e.1 ≠ x.name) →
      SepWPp (lsProg_589 H)
        (s0.readReg64 .lr) sm
        ((dirAt A.repAlloc x.self x.dir ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 sm) ∗ Extra)
        (dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQpPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R))
    (ih : ∀ (pre' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest ≠ [] →
      x.dir.changed = pre' ++ rest →
      (∀ e ∈ pre', e.1 ≠ x.name) →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sn.mem →
      sn.pc = (blkPl_589).base + 80#64 →
      sn.status = .Running →
      sn.spAligned = true →
      sn.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sn →
      FdsGe3Closed sn.fs →
      sn.fs.files = s0.fs.files →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = x.ret →
      sn.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x21 = x.self →
      sn.readReg64 .x22 = x.nameA →
      sn.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre'.length) + 40#64 →
      sn.readReg64 .x24 = BitVec.ofNat 64 (48 * rest.length) →
      SepWPp (lsProg_589 H)
        (s0.readReg64 .lr) sn
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre' ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre'.length)) rest ∗
          (if changedCap = 0 then emp
           else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
          strRefAt (x.self + 24#64) x.dir.path) ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 sn) ∗ Extra)
        (dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQpPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R))
    (hcrl_m : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpc_m : sm.pc = (blkPl_589).base + 68#64)
    (hrun_m : sm.status = .Running)
    (hsp_al_m : sm.spAligned = true)
    (hsp_m : sm.sp = s0.sp - 112#64)
    (hhcs_m : HighCalleeSaved s0 sm)
    (hfds_m : FdsGe3Closed sm.fs)
    (hfs_m : sm.fs.files = s0.fs.files)
    (htr_m : sm.trace = s0.trace)
    (hx19_m : sm.readReg64 .x19 = x.ret)
    (hx20_m : sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21_m : sm.readReg64 .x21 = x.self)
    (hx22_m : sm.readReg64 .x22 = x.nameA)
    (hx23_m : sm.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64)
    (hx24_m : sm.readReg64 .x24 = BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: rest).length)) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) sm
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
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
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 sm) ∗ Extra)
      (dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have _ := hstk; have _ := hfull
  have hsuf_lt63 : 48 * ((hdName, hdBytes) :: rest).length < 2 ^ 63 := by
    have hch_len : pre.length + ((hdName, hdBytes) :: rest).length = x.dir.changed.length := by
      rw [hchanged, List.length_append]
    have hle : ((hdName, hdBytes) :: rest).length ≤ changedCap.toNat :=
      Nat.le_trans (hch_len ▸ Nat.le_add_left _ pre.length) hcap_ok.1
    rw [Nat.mul_comm]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 48 hle) hcap_ok.2.1
  have hne_next : ∀ e ∈ pre ++ [(hdName, hdBytes)], e.1 ≠ x.name := by
    intro e he
    rcases List.mem_append.mp he with he1 | he2
    · exact hne e he1
    · rcases List.mem_singleton.mp he2 with rfl
      exact hhd_ne
  have hrest_cases : rest = [] ∨ ∃ nxt tail, rest = nxt :: tail := by
    cases rest with
    | nil => exact Or.inl rfl
    | cons nxt tail => exact Or.inr ⟨nxt, tail, rfl⟩
  rcases hrest_cases with hr_nil | ⟨nxt, tail, hr_cons⟩
  · clear ih
    rw [hr_nil] at hchanged hx24_m ⊢
    have hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name := by
      simpa [hchanged] using hne_next
    have hrepack_dir :
        (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) [] ∗
          (if changedCap = 0 then emp
           else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48))) ∗
          strRefAt (x.self + 24#64) x.dir.path ⊢
        dirAt A.repAlloc x.self x.dir := by
      unfold dirAt vecOf vecAt
      refine sepConj_mono ?_ (Entails.refl _)
      refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
      refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
      rw [vecBuf_dirEntry_expose]
      refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hcap_ok (Entails.refl _)))
      rw [hchanged, arrayAt_dirEntry_append]
      dsimp only [arrayAt, dirEntryAt]
      sep_frame
    refine seq_lscro_state (mid := (blkPl_589).base + 164#64) hcrl_m ?_
    simp only [List.length_singleton, Nat.mul_one] at hx24_m
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 164#64)
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_m'
    refine SepWPp.perm
      (hmiss _
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al_m)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs_m.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        hcrl_m'
        (by simp only [wp_norm, arm64_norm]; exact hfds_m)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hall_ne)
      (by sep_frame)
  · clear hmiss
    have hsuf_lt63' : 48 * ((hdName, hdBytes) :: nxt :: tail).length < 2 ^ 63 := by
      rwa [← hr_cons]
    have hsub48 :
        BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: nxt :: tail).length) - 48#64 =
          BitVec.ofNat 64 (48 * (nxt :: tail).length) :=
      sub48_cons_len
    have hbeq48 :
        (BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: nxt :: tail).length) == 48#64) = false :=
      ofNat48_beq_48_false hsuf_lt63'
    have hpeel :
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ⊢
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr (pre ++ [(hdName, hdBytes)]) := by
      rw [arrayAt_dirEntry_append]
      dsimp only [arrayAt, dirEntryAt]
      sep_frame
    have hnext_ptr :
        changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64 =
          changedPtr + BitVec.ofNat 64 (48 * (pre ++ [(hdName, hdBytes)]).length) := by
      rw [List.length_append, List.length_singleton, Nat.mul_add_one, BitVec.add_assoc, ← BitVec.ofNat_add]
    have hx23_next :
        changedPtr + BitVec.ofNat 64 (48 * pre.length) + 88#64 =
          changedPtr + BitVec.ofNat 64 (48 * (pre ++ [(hdName, hdBytes)]).length) + 40#64 := by
      rw [← hnext_ptr]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine seq_lscro_state (mid := (blkPl_589).base + 80#64) hcrl_m ?_
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 80#64)
    simp only [← hr_cons]
    apply SepWP.fold hpeel (by sep_frame)
    rw [hnext_ptr]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_m'
    refine SepWPp.perm
      (ih (pre ++ [(hdName, hdBytes)]) _
        (by rw [hr_cons]; simp)
        (by rw [hchanged, List.append_assoc]; rfl)
        hne_next
        hcrl_m'
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al_m)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs_m.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm]; exact hfds_m)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
      (by sep_frame)

/-! ## 2. Entry-Scan Loop (`+80`..`+108`) on Block `589` -/

private theorem w32_zext_beq_zero_false {v : BitVec 64} (hne : v.setWidth 32 ≠ 0#32) :
    (((v.truncate 32).zeroExtend 64) == 0#64) = false := by
  apply beq_false_of_ne
  intro hz
  apply hne
  change (v.setWidth 32).setWidth 64 = 0#64 at hz
  bv_bits

theorem step_loop_budget_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {s0 : State}
    {changedCap changedPtr : BitVec 64}
    {Extra R : SepProp}
    (hAllocFs : AllocContractsFsPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hFs : TraceFsSound (lsProg_589 H))
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hname_lt : x.name.length < 2 ^ 32)
    (hfit0 : FitsEnv M lim st0 (DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name))
    (hGetEnv : ∀ evs, DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name evs →
      GetEnv s0.fs.files x.dir x.name evs)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hmiss : ∀ sm : State,
      sm.pc = (blkPl_589).base + 164#64 →
      sm.status = .Running →
      sm.spAligned = true →
      sm.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sm →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs →
      sm.fs.files = s0.fs.files →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sm.readReg64 .x21 = x.self →
      sm.readReg64 .x22 = x.nameA →
      (∀ e ∈ x.dir.changed, e.1 ≠ x.name) →
      SepWPp (lsProg_589 H)
        (s0.readReg64 .lr) sm
        ((dirAt A.repAlloc x.self x.dir ∗
          CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 sm) ∗ Extra)
        (dirGetPostQPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQpPlacedBudgetFd rd pathOk A lim GetEnv stk x st0 s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)) :
    ∀ (suf pre : List (List (BitVec 8) × List (BitVec 8))) (s : State),
      suf ≠ [] →
      x.dir.changed = pre ++ suf →
      (∀ e ∈ pre, e.1 ≠ x.name) →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = (blkPl_589).base + 80#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 s →
      FdsGe3Closed s.fs →
      s.fs.files = s0.fs.files →
      s.trace = s0.trace →
      s.readReg64 .x19 = x.ret →
      s.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      s.readReg64 .x21 = x.self →
      s.readReg64 .x22 = x.nameA →
      s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 →
      s.readReg64 .x24 = BitVec.ofNat 64 (48 * suf.length) →
      SepWPp (lsProg_589 H)
        (s0.readReg64 .lr) s
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length)) suf ∗
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
  intro suf
  induction suf with
  | nil =>
    intro _ _ hsuf
    exact False.elim (hsuf rfl)
  | cons hd rest ih =>
    rcases hd with ⟨hdName, hdBytes⟩
    intro pre s _ hchanged hne hcrl hpc hrun hsp_al hsp hhcs hfds hfs htr
      hx19 hx20 hx21 hx22 hx23 hx24
    rw [arrayAt_dirEntry_cons]
    refine SepWPp.perm
      (P' := vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
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
    refine sepWPp_unfold_vecU8 fun nmCap nmPtr hnm_le hnm_lt hnm_ne => ?_
    have hrepack_nm :
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length)) ↦₆₄ nmCap) ∗
          ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 8#64) ↦₆₄ nmPtr) ∗
          ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 16#64) ↦₆₄
            BitVec.ofNat 64 hdName.length) ∗
          (nmPtr ↦ₛ hdName) ∗
          (if nmCap = 0 then emp
           else A.repAlloc.live nmPtr nmCap.toNat 1 ∗
             memRegion (nmPtr + BitVec.ofNat 64 hdName.length) (nmCap.toNat - hdName.length)) ⊢
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName := by
      dsimp only [vecU8]
      refine Entails.trans ?_ (Entails.sepExists_intro nmCap)
      refine Entails.trans ?_ (Entails.sepExists_intro nmPtr)
      rw [vecU8At_expose]
      exact Entails.pure_right ⟨hnm_le, hnm_lt, hnm_ne⟩ (Entails.refl _)
    have hx23_sub24 :
        (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-24#64) =
          changedPtr + BitVec.ofNat 64 (48 * pre.length) + 16#64 := by
      simp only [BitVec.add_assoc]; rfl
    have hx23_sub32 :
        (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-32#64) =
          changedPtr + BitVec.ofNat 64 (48 * pre.length) + 8#64 := by
      simp only [BitVec.add_assoc]; rfl
    by_cases hlen_eq : hdName.length = x.name.length
    · have hbcmp_fs := subroutine_ok_lscro_withFsInv hFs
        (bcmp_keepsFs_lscro_vm_ok_at_589 hBcmp) s0.fs.files s0.trace
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk (cstk_le_pow64 hstk hfull)]
      have hcstk_join :
          memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
            stackAt (s0.sp - 112#64) extHookStack ⊢
          stackAt (s0.sp - 112#64) cstk := by
        rw [stackAt_sub_split (s0.sp - 112#64) hcstk (cstk_le_pow64 hstk hfull)]
        exact Entails.refl _
      refine seq_lscro_state (mid := lsρ cliBcmpName) hcrl ?_
      rw [hlen_eq]
      dsimp only [lsProg_589]
      wp_steps_sync_pool (lsρ cliBcmpName)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl_b
      have hx2_nat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
        ofNat64_toNat_of_lt32 hname_lt
      refine call_lscro_frame
        (x := CryptoVerification.SignalSession.Cli.CliBcmpCall.mk nmPtr false hdName x.nameA x.nameRo x.name)
        (T := (nmPtr ↦ₛ hdName) ∗ CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 112#64) extHookStack)
        (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_budget ho))
        hbcmp_fs hcrl_b (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al)
        (by wp_norm_lhs)
        (by simp only [withFsInv, Spec.keepsFs, withVmPreserved, cliBcmpSpec, bytesAt_false,
              wp_norm, hsp, pure_sepConj_pure_assoc]; rfl)
        (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                      (by simp only [wp_norm, arm64_norm, *]),
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    hlen_eq.symm⟩)
        (by sep_frame)
        (fun _ _ _ _ hex => false_of_fsInv_false_budget hex)
        (fun _ _ => panicQpBudget_of_fsInv_false)
        (fun sfb hpcb hrunb hspb hcsb hcrlb => ?_)
      dsimp only [withFsInv, Spec.keepsFs, withVmPreserved, cliBcmpSpec, bytesAt_false]
      simp only [sepConj_assoc]
      refine SepWPp.pure_left fun hfs_fb =>
        SepWPp.pure_left fun hfs_eq_b =>
        SepWPp.pure_left fun hvmb =>
        SepWPp.pure_left fun ⟨hw0_iff, htrb⟩ => ?_
      have hfds_b : FdsGe3Closed sfb.fs := by
        rw [hfs_eq_b]; simpa only [wp_norm, arm64_norm] using hfds
      refine SepWPp.transport_budgetPool hvmb (hnext := ?_)
      simp only [wp_norm, hsp, sepConj_assoc]
      simp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm] at hrepack_nm
      have hhcsb : HighCalleeSaved s0 sfb :=
        hhcs.of_step_call hcsb
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
      have hspb_al : sfb.spAligned = true :=
        spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hspb
      have hspb_eq : sfb.sp = s0.sp - 112#64 := by rw [hspb]; simp only [wp_norm, arm64_norm, *]
      have hx19_b : sfb.readReg64 .x19 = x.ret := by
        have := hcsb.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
      have hx20_b : sfb.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
        have := hcsb.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20
      have hx21_b : sfb.readReg64 .x21 = x.self := by
        have := hcsb.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21
      have hx22_b : sfb.readReg64 .x22 = x.nameA := by
        have := hcsb.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22
      have hx23_b : sfb.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 := by
        have := hcsb.2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx23
      have hx24_b : sfb.readReg64 .x24 = BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: rest).length) := by
        have := hcsb.2.2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx24
      have htrb_s0 : sfb.trace = s0.trace := by rw [htrb]; simp only [wp_norm, arm64_norm, *]
      have hfiles_b : sfb.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs_fb htrb_s0
      rw [← hlen_eq]
      by_cases hname_eq : hdName = x.name
      · have hw0_eq : (sfb.readReg64 .x0).setWidth 32 = 0#32 := hw0_iff.mpr hname_eq
        have hw0_zext : ((sfb.readReg64 .x0).truncate 32).zeroExtend 64 = 0#64 := by
          change ((sfb.readReg64 .x0).setWidth 32).zeroExtend 64 = 0#64
          rw [hw0_eq]; rfl
        have hw0_rr : sfb.readReg .W32 .x0 = 0#64 := hw0_zext
        have _ := hw0_eq; have _ := hw0_zext; have _ := hw0_rr
        subst hname_eq
        refine seq_lscro_state (mid := (blkPl_589).base + 112#64) hcrlb ?_
        wp_steps_sync_pool ((blkPl_589).base + 112#64)
        apply SepWP.fold hrepack_nm (by sep_frame)
        apply SepWP.fold hcstk_join (by sep_frame)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_hit
        refine SepWPp.perm
          (step_hit_exit_budget_fd (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
            (pre := pre) (rest := rest) (bs := hdBytes) (Extra := Extra)
            hAllocFs hcstk hstk hfull hsp0_al hfit0 hGetEnv hchanged hne hcap_ok hcrl_hit
            (by wp_norm_lhs)
            (by simp only [wp_norm, arm64_norm, *])
            (by simpa only [wp_norm, arm64_norm] using hspb_al)
            (by simp only [wp_norm, arm64_norm, *])
            (hhcsb.of_steps
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
            (by simp only [wp_norm, arm64_norm]; exact hfds_b)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
          (by simp only [← LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm]; sep_frame)
      · have hw0_ne : ((sfb.readReg64 .x0).setWidth 32 == 0#32) = false :=
          beq_false_of_ne (fun h => hname_eq (hw0_iff.mp h))
        have hw0_zext_ne : (((sfb.readReg64 .x0).truncate 32).zeroExtend 64 == 0#64) = false :=
          w32_zext_beq_zero_false (fun h => hname_eq (hw0_iff.mp h))
        have hw0_rr_ne : (sfb.readReg .W32 .x0 == 0#64) = false := hw0_zext_ne
        have _ := hw0_ne; have _ := hw0_zext_ne; have _ := hw0_rr_ne
        refine seq_lscro_state (mid := (blkPl_589).base + 68#64) hcrlb ?_
        wp_steps_sync_pool ((blkPl_589).base + 68#64)
        apply SepWP.fold hrepack_nm (by sep_frame)
        apply SepWP.fold hcstk_join (by sep_frame)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_adv
        refine SepWPp.perm
          (step_loop_advance_budget_fd (cstk := cstk) (changedCap := changedCap)
            (changedPtr := changedPtr) (pre := pre) (rest := rest)
            (hdName := hdName) (hdBytes := hdBytes) (Extra := Extra)
            hstk hfull hcap_ok hchanged hne hname_eq hmiss ih
            hcrl_adv
            (by wp_norm_lhs)
            (by simp only [wp_norm, arm64_norm, *])
            (by simpa only [wp_norm, arm64_norm] using hspb_al)
            (by simp only [wp_norm, arm64_norm, *])
            (hhcsb.of_steps
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
            (by simp only [wp_norm, arm64_norm]; exact hfds_b)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
          (by simp only [← LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm]; sep_frame)
    · have hbv_ne : BitVec.ofNat 64 hdName.length ≠ BitVec.ofNat 64 x.name.length := by
        intro heq_bv
        have hnat := congrArg BitVec.toNat heq_bv
        rw [ofNat64_toNat_of_lt63 (Nat.lt_of_le_of_lt hnm_le hnm_lt),
            ofNat64_toNat_of_lt32 hname_lt] at hnat
        exact hlen_eq hnat
      have hbne_len : (BitVec.ofNat 64 hdName.length != BitVec.ofNat 64 x.name.length) = true :=
        bne_iff_ne.mpr hbv_ne
      have hbeq_len : (BitVec.ofNat 64 hdName.length == BitVec.ofNat 64 x.name.length) = false :=
        beq_false_of_ne hbv_ne
      have _ := hbv_ne; have _ := hbne_len; have _ := hbeq_len
      have hname_ne : hdName ≠ x.name := fun heq => hlen_eq (congrArg List.length heq)
      refine seq_lscro_state (mid := (blkPl_589).base + 68#64) hcrl ?_
      dsimp only [lsProg_589]
      wp_steps_sync_pool ((blkPl_589).base + 68#64)
      apply SepWP.fold hrepack_nm (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl_adv
      refine SepWPp.perm
        (step_loop_advance_budget_fd (cstk := cstk) (changedCap := changedCap)
          (changedPtr := changedPtr) (pre := pre) (rest := rest)
          (hdName := hdName) (hdBytes := hdBytes) (Extra := Extra)
          hstk hfull hcap_ok hchanged hne hname_ne hmiss ih
          hcrl_adv
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simpa only [wp_norm, arm64_norm] using hsp_al)
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
          (by simp only [wp_norm, arm64_norm]; exact hfds)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by sep_frame)

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1bFd
