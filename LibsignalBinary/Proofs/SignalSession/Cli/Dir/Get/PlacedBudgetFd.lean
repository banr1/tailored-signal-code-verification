/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2bFd
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded `[LibsignalPlacement]` `<signal_session::stores::Dir>::get` (Block 589)

Discharges `PathIoContractPlacedBudgetFd` at `lr = (blkPl_589).base + 336#64` and establishes
block-589 and caller-transferable `withFdsGe3Closed (SpecsPlacedBudget.dirGetSpecPlaced …)`
contracts for `Dir::get`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles TraceFsSound)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (strRefAt)
open CryptoVerification.RustHeap (arrayAt vecAt vecHeader vecOf)
open CryptoVerification.SignalSession (lsReadFileSym)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule cliBcmpName cliBcmpSpec dirAt dirEntryAt pathOf)
open CryptoVerification.SignalSession.Cli.Get.Helpers (dirGetCalleeStk frame_0x70_split ofNat_beq_zero_false savedRegsAt stackAt_dirGet_split stk_le_of_memRegion_sep)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_589 lsProg_589)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ)
open LibsignalBinary.Proofs.Placed.PlacedCallSym (IsLsBlockProg)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv dirGetEnv_of_miss)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.SignalSession.Cli.Get.PlacedHelpers
  (HighCalleeSaved call_lscro_frame dirGetRoBundlePlaced dirGetRoData_of_lscro
   lt_pow64_of_lt_pow63 ofNat64_toNat_of_lt32 sepWPp_exists_left seq_lscro_state
   vecBuf_dirEntry_expose)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (hookSat_keepLr_withFds_of_withFds_keepLrAndFds lsReadFile_withLsCodeRoLoaded_of_hookSat
   ls_transfer_withFdsGe3Closed_lscro withKeepLrAndFds withLsRetAddr624AndFds withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1bFd
  (step_loop_budget_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2aFd
  (PathIoContractPlacedBudgetFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2bFd
  (step_miss_tail_budget_fd)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Isolated `read_file` Call Site Twins (`+332`..`+336`) on Block `589` -/

private theorem lscro_of_mem_eq [LibsignalPlacement] {s1 s2 : State}
    (h : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem) (hm : s1.mem = s2.mem) :
    CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem :=
  hm ▸ h

/-- `FdsGe3Closed`-threaded `read_file` call step on Block 589 (`+332`..`+336`), parameterized by a
return-address predicate `lrOk` satisfied at `(blkPl_589).base + 336#64`. -/
theorem step_read_file_call_budget_guard_fd [LibsignalPlacement]
    {lrOk : BitVec 64 → Prop} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk : Nat}
    (hRead : subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withPreGuard (fun s => lrOk (s.readReg64 .lr))
          (withFdsGe3Closed
            (SpecsPlacedBudget.readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))))
    (hlr_ok : lrOk ((blkPl_589).base + 336#64)) :
    PathIoContractPlacedBudgetFd A lim H rd pathOk ReadEnv readStk := by
  intro s0 s st1 pathPtr pth F Q Qp hcrl hpc hrun hsp hfds hinv htr
    hx0 hx1 hx8 hlt hpOk hfit_rd hnext
  have hfiles : s.fs.files = s0.fs.files :=
    hinv.files_eq (evs := []) (by simp [htr]) CryptoVerification.LibsignalPublicApi.StoreKit.NoFsEv.nil
  refine SepWPp.seq_frozen
    (mid := lsρ lsReadFileSym)
    (Φ := fun m => CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m)
    (fun m m' hf hkf => hf.of_keepsFrozen hkf)
    hcrl ?_
  dsimp only [lsProg_589]
  wp_steps_sync_pool (lsρ lsReadFileSym)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  refine SepWPp.seq_frozen
    (mid := (blkPl_589).base + 336#64)
    (Φ := fun m => CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m)
    (fun m m' hf hkf => hf.of_keepsFrozen hkf)
    (lscro_of_mem_eq hcrl1 (by simp only [wp_norm])) ?_
  refine CryptoVerification.SignalSession.Cli.Store.PlacedCommon.SepWP.call_lscro (x := (CryptoVerification.SignalSession.Cli.ReadFileGhost.mk pathPtr pth s.sp, st1)) (F := F)
    hRead (lscro_of_mem_eq hcrl1 (by simp only [wp_norm]))
    (by wp_norm_lhs)
    (by simp only [wp_norm, *])
    (by simpa only [arm64_norm] using hsp)
    (by wp_norm_lhs)
    (fun R hm => by
      dsimp only [withPreGuard, withFdsGe3Closed, SpecsPlacedBudget.readFileSpecPlaced]
      simp only [wp_norm, sepConj_assoc, pure_sepConj_pure_assoc]
      rw [satisfies_pure_sepConj]
      refine ⟨⟨by simpa only [Reg.lr, Reg.x30, wp_norm, arm64_norm] using hlr_ok,
               by simpa only [wp_norm, arm64_norm] using hfds,
               by simp only [wp_norm, arm64_norm, *],
               by simp only [wp_norm, arm64_norm, *],
               by simp only [wp_norm, arm64_norm, *],
               hlt, hpOk,
               by simp only [wp_norm, arm64_norm, hfiles]; exact hfit_rd⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_frame)) hm)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf hpc_f hrun_f hsp_f hcs hcrl_f => ?_)
  apply SepWP.done hpc_f hrun_f
  intro _hcrl_f2
  have hcs' : CalleeSavedPreserved s sf := ⟨
    by simpa only [wp_norm] using hcs.1,
    by simpa only [wp_norm] using hcs.2.1,
    by simpa only [wp_norm] using hcs.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.2.2.1,
    by simpa only [calleeSavedVRegs, wp_norm] using hcs.2.2.2.2.2.2.2.2.2.2.2⟩
  have hsp_f' : sf.sp = s.sp := by rw [hsp_f]; simp only [wp_norm]
  dsimp only [withPreGuard, withFdsGe3Closed, SpecsPlacedBudget.readFileSpecPlaced]
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun hfds_f => ?_
  have hh := hnext sf hpc_f hrun_f hsp_f' hcs' hcrl_f hfds_f
  simpa [wp_norm, arm64_norm, hfiles, htr, sepExists_sepConj_left, sepConj_assoc] using hh

/-- `subroutine_ok` `LsRetAddr624` specialization of `step_read_file_call_budget_guard_fd`. -/
theorem step_read_file_call_budget_subroutine_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk : Nat}
    (hRead : subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withLsRetAddr624AndFds
          (SpecsPlacedBudget.readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))) :
    PathIoContractPlacedBudgetFd A lim H rd pathOk ReadEnv readStk :=
  step_read_file_call_budget_guard_fd hRead
    (lsRetAddr624_blockPlacement_base_add 589 336#64 (by decide) (by decide))

/-- `HookSat` `LsRetAddr624` specialization of `step_read_file_call_budget_guard_fd`. -/
theorem step_read_file_call_budget_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk : Nat}
    (hSat : HookSat H lsReadFileSym
      (withLsRetAddr624AndFds
        (SpecsPlacedBudget.readFileSpecPlaced rd pathOk A lim readStk ReadEnv))) :
    PathIoContractPlacedBudgetFd A lim H rd pathOk ReadEnv readStk :=
  step_read_file_call_budget_subroutine_fd
    (lsReadFile_withLsCodeRoLoaded_of_hookSat (callerProg := lsProg_589 H) (i := 589) hSat)

/-- `HookSat` specialization of `step_read_file_call_budget_guard_fd` for `withKeepLrAndFds keepSet`. -/
theorem step_read_file_call_budget_keep_fd [LibsignalPlacement]
    {keepSet : BitVec 64 → Bool} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk : Nat}
    (hSat : HookSat H lsReadFileSym
      (withFdsGe3Closed
        (withKeepLrAndFds keepSet
          (SpecsPlacedBudget.readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))
    (hlr : keepSet ((blkPl_589).base + 336#64) = false) :
    PathIoContractPlacedBudgetFd A lim H rd pathOk ReadEnv readStk :=
  step_read_file_call_budget_guard_fd (lrOk := fun lr => keepSet lr = false)
    (lsReadFile_withLsCodeRoLoaded_of_hookSat (callerProg := lsProg_589 H) (i := 589)
      (hookSat_keepLr_withFds_of_withFds_keepLrAndFds hSat))
    hlr

/-! ## 2. Entry Prologue (`+0`..`+68`) & Top-Level `withFdsGe3Closed (dirGetSpecPlaced …)` Twins -/

private def stateOfLscro [LibsignalPlacement] {st : State}
    (_ : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl st.mem) : State := st

private theorem state_setMem_setMem (st : State) (m1 m2 : Memory) :
    (st.setMem m1).setMem m2 = st.setMem m2 := by
  cases st; rfl

private theorem setup_x24_48_eq (n : Nat) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n)) <<< 4 =
      BitVec.ofNat 64 (48 * n) := by
  have hb : BitVec.ofNat 64 (2 * n) = BitVec.ofNat 64 n <<< 1 := by
    rw [Nat.mul_comm 2 n, BitVec.ofNat_mul]
    have h2 : ∀ v : BitVec 64, v * BitVec.ofNat 64 2 = v <<< 1 := by intro v; bv_bits
    exact h2 _
  have hc : ∀ v : BitVec 64, (v + (v <<< 1)) <<< 4 = 48#64 * v := by intro v; bv_bits
  rw [hb, hc, Nat.mul_comm 48 n, BitVec.ofNat_mul, BitVec.mul_comm]

private theorem sub112_aligned {sp : BitVec 64} (hm : sp &&& 15#64 = 0#64) :
    (sp - 112#64) &&& 15#64 = 0#64 := by
  bv_bits

/-- Verifies `withFdsGe3Closed (dirGetSpecPlaced …)` on Block 589 from `PathIoContractPlacedBudgetFd`. -/
theorem dirGet_placed_ok_of_ioCall_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk ioStk stk : Nat}
    (hAllocFs : AllocContractsFsPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hPath : subroutine_ok (lsProg_589 H) (lsmpl.base 596)
      (withFdsGe3Closed (SpecsPlacedBudget.pathSpecPlaced A lim PathEnv pathStk)))
    (hIoCall : PathIoContractPlacedBudgetFd A lim H rd pathOk ReadEnv ioStk)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hGetEnv : ∀ F0 d nm evs, DirGetEnv PathEnv ReadEnv rd F0 d nm evs → GetEnv F0 d nm evs) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (withFdsGe3Closed (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk)) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hstk112 : 112 + cstk ≤ stk := hstk
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc hrun hpre halign
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := halign
  have hsp_sub_al : ({ s0 with sp := s0.sp - 112#64 } : State).spAligned = true :=
    beq_iff_eq.mpr (sub112_aligned (eq_of_beq hsp0_mask))
  dsimp only [withFdsGe3Closed] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfds0, hpre_lscro⟩
  obtain ⟨hcrl0, hpre0⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre_lscro
  dsimp only [SpecsPlacedBudget.dirGetSpecPlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hname_lt, hdir_lt, hpOk, hFitGet⟩, hsat0⟩
  have hfit0 : FitsEnv M lim st0 (DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name) :=
    fun evs he => hFitGet evs (hGetEnv s0.fs.files x.dir x.name evs he)
  have hGetEnv0 : ∀ evs, DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name evs →
      GetEnv s0.fs.files x.dir x.name evs :=
    hGetEnv s0.fs.files x.dir x.name
  have hpth_len_lt : (pathOf x.dir.path x.name).length < 2 ^ 32 := hpathLen _ hpOk
  have hx3_bv : s0.readReg64 .x3 = BitVec.ofNat 64 x.name.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx3, ofNat64_toNat_of_lt32 hname_lt]
  have hfull : stk ≤ 2 ^ 64 :=
    stk_le_of_memRegion_sep (r := x.ret) (sp0 := s0.sp) (stk := stk)
      (F := dirAt A.repAlloc x.self x.dir ∗ CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        A.pool lim st0 s0 ∗ R)
      (Satisfies.mono (Entails.of_eq (by sep_frame)) hsat0)
  obtain ⟨w0, w1, wTail, hsat_ro⟩ := dirGetRoData_of_lscro hcrl0 hsat0
  rw [stackAt_dirGet_split s0.sp hstk112 hfull] at hsat_ro
  let P0 : SepProp :=
    (dirAt A.repAlloc x.self x.dir ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
      memRegion x.ret 48 ∗
      stackAt (s0.sp - 112#64) cstk ∗
      memRegion (s0.sp - 112#64) 112 ∗
      A.pool lim st0 s0) ∗
    dirGetRoBundlePlaced w0 w1 wTail
  let Fr : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R
  refine ⟨P0, Fr, Satisfies.mono (Entails.of_eq (by dsimp only [P0, Fr]; sep_frame)) hsat_ro, ?_⟩
  have hpc0 : s0.pc = (blkPl_589).base := hpc
  clear hpc
  dsimp only [P0, Fr]
  rw [frame_0x70_split (s0.sp - 112#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  refine sepWPp_exists_left fun v0 => sepWPp_exists_left fun v1 =>
    sepWPp_exists_left fun v2 => sepWPp_exists_left fun v3 =>
    sepWPp_exists_left fun v4 => sepWPp_exists_left fun v5 =>
    sepWPp_exists_left fun v6 => sepWPp_exists_left fun v7 => ?_
  unfold dirAt vecOf vecAt
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_left fun changedCap => sepWPp_exists_left fun changedPtr => ?_
  rw [vecBuf_dirEntry_expose]
  simp only [sepConj_assoc]
  rw [← sepConj_assoc, sepConj_comm (vecHeader _ _ _ _) ⌜_⌝, sepConj_assoc]
  refine SepWPp.pure_left fun hcap_ok => ?_
  unfold vecHeader
  have hch_cases : x.dir.changed = [] ∨ (x.dir.changed ≠ [] ∧ 0 < x.dir.changed.length) := by
    cases x.dir.changed <;> simp
  rcases hch_cases with hch_nil | ⟨hch_ne, hch_pos⟩
  · have hrepack_dir0 :
        ((x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
          ((x.self + 16#64) ↦₆₄ 0#64) ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr [] ∗
          (if changedCap = 0 then emp
           else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48))) ∗
          strRefAt (x.self + 24#64) x.dir.path ⊢
        dirAt A.repAlloc x.self x.dir := by
      unfold dirAt vecOf vecAt
      refine sepConj_mono ?_ (Entails.refl _)
      refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
      refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
      rw [vecBuf_dirEntry_expose]
      unfold vecHeader
      simp only [hch_nil, List.length_nil, sepConj_assoc]
      have hpure_r :
          (x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
            ((x.self + 16#64) ↦₆₄ 0#64) ∗
            ⌜(0 : Nat) ≤ changedCap.toNat ∧ changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0⌝ ∗
            arrayAt (dirEntryAt A.repAlloc) 48 changedPtr [] ∗
            (if changedCap = 0 then emp
             else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
               memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48)) =
          ⌜(0 : Nat) ≤ changedCap.toNat ∧ changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0⌝ ∗
            ((x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
              ((x.self + 16#64) ↦₆₄ 0#64) ∗
              arrayAt (dirEntryAt A.repAlloc) 48 changedPtr [] ∗
              (if changedCap = 0 then emp
               else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
                 memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48))) := by sep_ac_rfl
      rw [hpure_r]
      exact Entails.pure_right (by simpa [hch_nil] using hcap_ok) (Entails.refl _)
    refine seq_lscro_state (mid := (blkPl_589).base + 164#64) hcrl0 ?_
    simp only [hch_nil, List.length_nil]
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 164#64)
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.fold (Entails.refl (savedRegsAt (s0.sp - 112#64) s0))
      (by unfold savedRegsAt; simp only [wp_norm, arm64_norm]; sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    rw [state_setMem_setMem] at hcrl1 ⊢
    let st1 := stateOfLscro hcrl1
    have hpc1 : st1.pc = (blkPl_589).base + 164#64 := by dsimp only [st1, stateOfLscro]; wp_norm_lhs
    have hrun1 : st1.status = ExecStatus.Running := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hsp1_al : st1.spAligned = true := by simpa only [st1, stateOfLscro, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al
    have hsp1 : st1.sp = s0.sp - 112#64 := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hhcs1 : HighCalleeSaved s0 st1 :=
      (CryptoVerification.SignalSession.Cli.Get.PlacedHelpers.HighCalleeSaved.refl s0).of_steps
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, calleeSavedVRegs, wp_norm, arm64_norm])
    have hfds1 : FdsGe3Closed st1.fs := by simpa only [st1, stateOfLscro, wp_norm, arm64_norm] using hfds0
    have hfs1 : st1.fs.files = s0.fs.files := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have htr1 : st1.trace = s0.trace := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hx19_1 : st1.readReg64 .x19 = x.ret := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx20_1 : st1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hx21_1 : st1.readReg64 .x21 = x.self := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx22_1 : st1.readReg64 .x22 = x.nameA := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hall_nil : ∀ e ∈ x.dir.changed, e.1 ≠ x.name :=
      fun _ hm => False.elim (List.not_mem_nil (hch_nil ▸ hm))
    have hmiss_eq := dirGetEnv_of_miss (PathEnv := PathEnv) (ReadEnv := ReadEnv)
      (rd := rd) (F0 := s0.fs.files) hall_nil
    refine SepWPp.perm
      (step_miss_tail_budget_fd (w0 := w0) (w1 := w1) (wTail := wTail)
        hAllocFs hPath hIoCall hFs hstk112 hfull halign
        hname_lt hdir_lt hpOk hpth_len_lt
        (hmiss_eq ▸ hfit0) (fun evs hm => hGetEnv0 evs (hmiss_eq.symm ▸ hm))
        hcrl1 hpc1 hrun1 hsp1_al hsp1 hhcs1
        hfds1 hfs1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hall_nil)
      (by sep_frame)
  · have hch_lt48 : x.dir.changed.length * 48 < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 48 hcap_ok.1) hcap_ok.2.1
    have hch_lt63 : x.dir.changed.length < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by decide : 0 < 48)) hch_lt48
    have hch_ne0 : (BitVec.ofNat 64 x.dir.changed.length == 0#64) = false :=
      ofNat_beq_zero_false hch_pos (lt_pow64_of_lt_pow63 hch_lt63)
    have hx24_init :
        (BitVec.ofNat 64 x.dir.changed.length + BitVec.ofNat 64 (2 * x.dir.changed.length)) <<< 4 =
          BitVec.ofNat 64 (48 * x.dir.changed.length) :=
      setup_x24_48_eq x.dir.changed.length
    refine seq_lscro_state (mid := (blkPl_589).base + 80#64) hcrl0 ?_
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 80#64)
    apply SepWP.fold (Entails.refl (vecHeader x.self changedCap changedPtr x.dir.changed.length))
      (by unfold vecHeader; sep_frame)
    apply SepWP.fold (Entails.refl (savedRegsAt (s0.sp - 112#64) s0))
      (by unfold savedRegsAt; simp only [wp_norm, arm64_norm]; sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    rw [state_setMem_setMem] at hcrl1 ⊢
    let st1 := stateOfLscro hcrl1
    have harr_init :
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr x.dir.changed =
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr [] ∗
            arrayAt (dirEntryAt A.repAlloc) 48 changedPtr x.dir.changed :=
      (emp_sepConj _).symm
    rw [harr_init]
    have hpc1 : st1.pc = (blkPl_589).base + 80#64 := by dsimp only [st1, stateOfLscro]; wp_norm_lhs
    have hrun1 : st1.status = ExecStatus.Running := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hsp1_al : st1.spAligned = true := by simpa only [st1, stateOfLscro, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al
    have hsp1 : st1.sp = s0.sp - 112#64 := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hhcs1 : HighCalleeSaved s0 st1 :=
      (CryptoVerification.SignalSession.Cli.Get.PlacedHelpers.HighCalleeSaved.refl s0).of_steps
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, calleeSavedVRegs, wp_norm, arm64_norm])
    have hfds1 : FdsGe3Closed st1.fs := by simpa only [st1, stateOfLscro, wp_norm, arm64_norm] using hfds0
    have hfs1 : st1.fs.files = s0.fs.files := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have htr1 : st1.trace = s0.trace := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hx19_1 : st1.readReg64 .x19 = x.ret := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx20_1 : st1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hx21_1 : st1.readReg64 .x21 = x.self := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx22_1 : st1.readReg64 .x22 = x.nameA := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx23_1 : st1.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * ([] : List (List (BitVec 8) × List (BitVec 8))).length) + 40#64 := by
      simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx24_1 : st1.readReg64 .x24 = BitVec.ofNat 64 (48 * x.dir.changed.length) := by
      simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    refine SepWPp.perm
      (step_loop_budget_fd (PathEnv := PathEnv) (ReadEnv := ReadEnv) (GetEnv := GetEnv)
        (cstk := cstk) (stk := stk) (x := x) (st0 := st0) (s0 := s0)
        (changedCap := changedCap) (changedPtr := changedPtr)
        (Extra := dirGetRoBundlePlaced w0 w1 wTail) (R := R)
        hAllocFs hBcmp hFs hcstk_ext hstk112 hfull halign hname_lt hfit0 hGetEnv0 hcap_ok
        (fun sm hpcm hrunm hsp_alm hspm hhcsm hcrlm hfdsm hfsm htrm hx19m hx20m hx21m hx22m hall_ne => by
          have hmiss_eq := dirGetEnv_of_miss (PathEnv := PathEnv) (ReadEnv := ReadEnv)
            (rd := rd) (F0 := s0.fs.files) hall_ne
          exact step_miss_tail_budget_fd (PathEnv := PathEnv) (ReadEnv := ReadEnv) (GetEnv := GetEnv)
            (w0 := w0) (w1 := w1) (wTail := wTail)
            hAllocFs hPath hIoCall hFs hstk112 hfull halign
            hname_lt hdir_lt hpOk hpth_len_lt
            (hmiss_eq ▸ hfit0) (fun evs hm => hGetEnv0 evs (hmiss_eq.symm ▸ hm))
            hcrlm hpcm hrunm hsp_alm hspm hhcsm
            hfdsm hfsm htrm hx19m hx20m hx21m hx22m hall_ne)
        x.dir.changed [] _ hch_ne rfl (fun _ hm => False.elim (List.not_mem_nil hm))
        hcrl1 hpc1 hrun1 hsp1_al hsp1 hhcs1 hfds1 hfs1 htr1
        hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1)
      (by simp only [List.length_nil, Nat.mul_zero, BitVec.add_zero,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm, arm64_norm]
          sep_frame)

/-- `Dir::get` satisfies `withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv stk)` on Block 589 under `withLsRetAddr624AndFds`. -/
theorem dirGet_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (SpecsPlacedBudget.pathSpecPlaced A lim PathEnv pathStk)))
    (hReadSat : HookSat H lsReadFileSym
      (withLsRetAddr624AndFds
        (SpecsPlacedBudget.readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hGetEnv : ∀ F0 d nm evs, DirGetEnv PathEnv ReadEnv rd F0 d nm evs → GetEnv F0 d nm evs) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (withFdsGe3Closed (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk)) := by
  have hPath589 : subroutine_ok (lsProg_589 H) (lsmpl.base 596)
      (withFdsGe3Closed (SpecsPlacedBudget.pathSpecPlaced A lim PathEnv pathStk)) :=
    ls_transfer_withFdsGe3Closed_lscro
      (callerProg := lsProg_589 H) (calleeProg := pathProg) (i := 589) (j := jPath)
      hPath (by decide) hjPath hjPath_unmut
  exact dirGet_placed_ok_of_ioCall_fd hAllocFs hBcmp hPath589
    (step_read_file_call_budget_fd hReadSat) hFs hstk hpathLen hGetEnv

/-- `Dir::get` satisfies `withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv stk)` on Block 589 under `withKeepLrAndFds keepSet`. -/
theorem dirGet_placed_ok_of_keep_fd [LibsignalPlacement]
    {keepSet : BitVec 64 → Bool} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (SpecsPlacedBudget.pathSpecPlaced A lim PathEnv pathStk)))
    (hReadSat : HookSat H lsReadFileSym
      (withFdsGe3Closed
        (withKeepLrAndFds keepSet
          (SpecsPlacedBudget.readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))
    (hlr : keepSet ((blkPl_589).base + 336#64) = false)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hGetEnv : ∀ F0 d nm evs, DirGetEnv PathEnv ReadEnv rd F0 d nm evs → GetEnv F0 d nm evs) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (withFdsGe3Closed (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk)) := by
  have hPath589 : subroutine_ok (lsProg_589 H) (lsmpl.base 596)
      (withFdsGe3Closed (SpecsPlacedBudget.pathSpecPlaced A lim PathEnv pathStk)) :=
    ls_transfer_withFdsGe3Closed_lscro
      (callerProg := lsProg_589 H) (calleeProg := pathProg) (i := 589) (j := jPath)
      hPath (by decide) hjPath hjPath_unmut
  exact dirGet_placed_ok_of_ioCall_fd hAllocFs hBcmp hPath589
    (step_read_file_call_budget_keep_fd hReadSat hlr) hFs hstk hpathLen hGetEnv

/-- Caller-transferable `[LibsignalPlacement]` `withFdsGe3Closed (dirGetSpecPlaced …)` contract
    for any block `< 619` from `HookSat H lsReadFileSym (withLsRetAddr624AndFds …)`. -/
theorem dirGet_placed_caller_ok_of_deps_fd [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (SpecsPlacedBudget.pathSpecPlaced A lim PathEnv pathStk)))
    (hReadSat : HookSat H lsReadFileSym
      (withLsRetAddr624AndFds
        (SpecsPlacedBudget.readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hGetEnv : ∀ F0 d nm evs, DirGetEnv PathEnv ReadEnv rd F0 d nm evs → GetEnv F0 d nm evs)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 589)
      (withFdsGe3Closed (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk)) :=
  ls_transfer_withFdsGe3Closed_lscro
    (callerProg := callerProg) (calleeProg := lsProg_589 H) (i := i) (j := 589)
    (dirGet_placed_ok_of_deps_fd hpathLen hAllocFs hBcmp
      hjPath hjPath_unmut hPath hReadSat hFs hstk hGetEnv) hi

/-- Caller-transferable `[LibsignalPlacement]` `withFdsGe3Closed (dirGetSpecPlaced …)` contract
    for any block `< 619` from `HookSat H lsReadFileSym (withFdsGe3Closed (withKeepLrAndFds keepSet …))`. -/
theorem dirGet_placed_caller_ok_of_keep_fd [LibsignalPlacement]
    {keepSet : BitVec 64 → Bool}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (SpecsPlacedBudget.pathSpecPlaced A lim PathEnv pathStk)))
    (hReadSat : HookSat H lsReadFileSym
      (withFdsGe3Closed
        (withKeepLrAndFds keepSet
          (SpecsPlacedBudget.readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))
    (hlr : keepSet ((blkPl_589).base + 336#64) = false)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hGetEnv : ∀ F0 d nm evs, DirGetEnv PathEnv ReadEnv rd F0 d nm evs → GetEnv F0 d nm evs)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 589)
      (withFdsGe3Closed (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk)) :=
  ls_transfer_withFdsGe3Closed_lscro
    (callerProg := callerProg) (calleeProg := lsProg_589 H) (i := i) (j := 589)
    (dirGet_placed_ok_of_keep_fd hpathLen hAllocFs hBcmp
      hjPath hjPath_unmut hPath hReadSat hlr hFs hstk hGetEnv) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
