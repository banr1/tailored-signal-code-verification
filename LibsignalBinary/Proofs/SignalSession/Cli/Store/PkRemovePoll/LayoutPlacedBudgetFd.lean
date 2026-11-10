/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded Relocatable Helpers for `remove_pre_key::{closure#0}`

`FdsGe3Closed`-threaded call wrappers for Block `575` (`lsProg_575 H`), nesting
`withFsInv (withFdsGe3Closed spec) F0 T0` at `FsInv` call sites and `withFdsGe3Closed` around
top-level poll and callee specs.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DecimalGhost DirGetGhost DirGhost DirPutGhost ReadRule decimalText dirAt getResultAt pathOf
   withFsInv)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_575 blkPl_575 lsProg_575)
open CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
  (entails_withLsCodeRoLoaded_pre sepWPp_conseq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_base_add lsRetAddr624_base_zero
   lsRetAddr624_blockPlacement_base_add lsRetAddr624_blockPlacement_base_zero)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (dealloc_keepsFs_lscro_of_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (pkrm_call_total_placed_raw)

section Placed

theorem pkrm_dealloc_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) :=
  dealloc_keepsFs_lscro_of_fs (callerProg := lsProg_575 H) hFs

theorem pkrm_call_decimal_fs_placed_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {decStk : Nat} {callee ret_pc ret : BitVec 64}
    {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee
      (withFsInv (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)) s0_files s0_trace))
    (xg : DecimalGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hfit : FitsEnv M lim st (DecEnv xg.n))
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm → FdsGe3Closed sm.fs →
      sm.trace = s.trace → DecEnv xg.n evs →
      SepWPp prog ret sm
        ((vecU8 A.repAlloc xg.ret (decimalText xg.n.toNat) ∗
          stackAt s.sp decStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFsInv, withFdsGe3Closed]
    simp only [sepConj_assoc]
    refine Entails.pure_right hfs (Entails.pure_right hfds ?_)
    unfold decimalSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFsInv, withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun hfsm =>
      SepWPp.pure_elim fun hfdsm => SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm hfsm hfdsm htrm hevs)

theorem pkrm_call_decimal_placed_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {decStk : Nat} {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (xg : DecimalGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hfit : FitsEnv M lim st (DecEnv xg.n))
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs → sm.trace = s.trace → DecEnv xg.n evs →
      SepWPp prog ret sm
        ((vecU8 A.repAlloc xg.ret (decimalText xg.n.toNat) ∗
          stackAt s.sp decStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFdsGe3Closed]
    simp only [sepConj_assoc]
    refine Entails.pure_right hfds ?_
    unfold decimalSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFdsGe3Closed, decimalSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun hfdsm =>
      SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm hfdsm htrm hevs)

theorem pkrm_call_dirGet_placed_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee
      (withFsInv (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
        s0_files s0_trace))
    (xg : DirGetGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsInv s0_files s0_trace s) (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hfit : FitsEnv M lim st (GetEnv s.fs.files xg.dir xg.name))
    (hpre : P ⊢ (dirAt A.repAlloc xg.self xg.dir ∗ bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm → FdsGe3Closed sm.fs →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace ∧
        GetEnv s.fs.files xg.dir xg.name evs) →
      SepWPp prog ret sm
        ((getResultAt A.repAlloc xg.ret gr ∗ dirAt A.repAlloc xg.self xg.dir ∗
          bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFsInv, withFdsGe3Closed]
    simp only [sepConj_assoc]
    refine Entails.pure_right hfs (Entails.pure_right hfds ?_)
    unfold dirGetSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFsInv, withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun gr =>
      SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun hfdsm =>
      SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs gr hpcm hrunm hspm hcsm hcrlm hfsm hfdsm hgr)

theorem pkrm_call_dirPut_placed_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {putStk : Nat} {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (xg : DirPutGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameV)
    (hx2 : s.readReg64 .x2 = xg.bytesV) (hlen : xg.dir.changed.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (PutEnv xg.dir xg.name xg.bytes))
    (hpre : P ⊢ (dirAt A.repAlloc xg.self xg.dir ∗ vecU8 A.repAlloc xg.nameV xg.name ∗
      vecU8 A.repAlloc xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs → sm.trace = s.trace → PutEnv xg.dir xg.name xg.bytes evs →
      SepWPp prog ret sm
        ((dirAt A.repAlloc xg.self (xg.dir.put xg.name xg.bytes) ∗
          memRegion xg.nameV 24 ∗ memRegion xg.bytesV 24 ∗
          stackAt s.sp putStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | (apply lsRetAddr624_blockPlacement_base_add <;> decide)
      | (apply lsRetAddr624_base_add <;> decide)
      | (apply lsRetAddr624_blockPlacement_base_zero <;> decide)
      | (apply lsRetAddr624_base_zero <;> decide)
      | simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFdsGe3Closed]
    simp only [sepConj_assoc]
    refine Entails.pure_right hfds ?_
    unfold dirPutSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    have hlr30 : LsRetAddr624 (s.readReg64 .x30) := by
      change LsRetAddr624 (s.readReg64 Reg.lr)
      rwa [hlr]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlen, hfit, hlr30⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFdsGe3Closed, dirPutSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [withFdsGe3Closed, dirPutSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [withFdsGe3Closed, dirPutSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFdsGe3Closed, dirPutSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun hfdsm =>
      SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm hfdsm htrm hevs)

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudgetFd
