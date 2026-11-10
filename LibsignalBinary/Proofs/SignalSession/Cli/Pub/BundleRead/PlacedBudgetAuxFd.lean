/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.Hoare.Safety

/-!
# `FdsGe3Closed`-Threaded `read_file` Call Steps for `read_bundle::{closure#0}`

File-descriptor-preserving (`FdsGe3Closed`) call-site lemmas for `bl signal_session_io::read_file`
at `+40` on Block `563`, parameterized by return-address guards (`lrOk`, `LsRetAddr624`, or `keepSet`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAuxFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles FsInv LibsignalCodeRoLoaded NoFsEv
  TraceFsSound sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SignalSession (lsReadFileSym)
open CryptoVerification.SignalSession.Cli (ReadFileGhost ReadRule ioVecAt subroutine_ok_withFsInv
  withFsInv withFsInv_post_elim withFsInv_pre_intro)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_563 blkPC_563 blkPl_563 lsProg_563)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (hookSat_keepLr_withFds_of_withFds_keepLrAndFds lsReadFile_withLsCodeRoLoaded_of_hookSat
   withKeepLrAndFds withLsRetAddr624AndFds withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
  (bind_sepWP_state satisfies_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv readFileSpecPlaced)

attribute [local irreducible] Arm64.Program.fetch Arm64.Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setMem_local (s : State) (m : Arm64.Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem fs_setMem_local (s : State) (m : Arm64.Memory) :
    (s.setMem m).fs = s.fs := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem readReg64_setPState_local (s : State) (ps : Arm64.PState) (r : Arm64.Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_setPState_local (s : State) (ps : Arm64.PState) :
    (s.setPState ps).sp = s.sp := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem status_setPState_local (s : State) (ps : Arm64.PState) :
    (s.setPState ps).status = s.status := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem trace_setPState_local (s : State) (ps : Arm64.PState) :
    (s.setPState ps).trace = s.trace := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setPState_local (s : State) (ps : Arm64.PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := rfl

/-- Return-address-guarded `withFdsGe3Closed` subroutine hypothesis for `read_file` on Block `563`. -/
abbrev ReadCallGuardHypPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (lrOk : BitVec 64 → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (readStk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) : Prop :=
  subroutine_ok (lsProg_563 H) (lsρ lsReadFileSym)
    (withLsCodeRoLoaded lsmpl
      (withPreGuard (fun s => lrOk (s.readReg64 .lr))
        (withFdsGe3Closed (readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))

/-- `LsRetAddr624`-guarded `withFdsGe3Closed` subroutine hypothesis for `read_file` on Block `563`. -/
abbrev ReadCallHypPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (readStk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) : Prop :=
  subroutine_ok (lsProg_563 H) (lsρ lsReadFileSym)
    (withLsCodeRoLoaded lsmpl
      (withLsRetAddr624AndFds (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))

/-- Executes `bl signal_session_io::read_file` at `+40` on Block `563`, preserving `FdsGe3Closed` under return-address guard `lrOk`. -/
theorem readCall_step_p_guard_fd [LibsignalPlacement] {M : AllocCostModel}
    {lrOk : BitVec 64 → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hRead : ReadCallGuardHypPlacedFd lrOk A lim H rd pathOk readStk ReadEnv)
    (hlr_ok : lrOk ((blkPl_563).base + 44#64))
    (hFs : TraceFsSound (lsProg_563 H))
    (F0 : FsFiles) (T0 : List TraceEvent)
    {ret : BitVec 64} {s : State} {st : M.σ}
    {pathPtr retSlot : BitVec 64} {p : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hPC : s.pc = (blkPl_563).base + 40#64)
    (hRun : s.status = .Running)
    (hAl : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : FsInv F0 T0 s)
    (hfds : FdsGe3Closed s.fs)
    (htr : s.trace = T0)
    (hx0 : s.readReg64 .x0 = pathPtr)
    (hx1 : (s.readReg64 .x1).toNat = p.length)
    (hx8 : s.readReg64 .x8 = retSlot)
    (hlen : p.length < 2 ^ 32)
    (hpOk : pathOk p)
    (hfit : FitsEnv M lim st (ReadEnv F0 p))
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_563).base + 44#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.spAligned = true →
      CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      FsInv F0 T0 sf →
      FdsGe3Closed sf.fs →
      ∀ evs : List AllocEvent,
      ReadEnv F0 p evs →
      ∀ r : Except Unit (List (BitVec 8)),
      (r = rd F0 p ∧ sf.trace = T0) →
      SepWPp (lsProg_563 H) ret sf
        (ioVecAt A.repAlloc retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) Q Qp) :
    SepWPp (lsProg_563 H) ret s
      (((pathPtr ↦ₛ p) ∗ memRegion retSlot 24 ∗ stackAt s.sp readStk ∗ A.pool lim st s) ∗ F) Q Qp := by
  apply sepWPp_seq_lscro hcrl (mid := lsρ lsReadFileSym)
  wp_steps_sync_pool (lsρ lsReadFileSym)
  apply bind_sepWP_state; intro s1
  refine SepWP.done ?_ ?_ ?_
  · simp only [s1, wp_norm, arm64_norm]
  · simp only [s1, wp_norm, arm64_norm, hRun]
  · intro hcrl1 R hm1 hL
    have hpc1 : s1.pc = lsρ lsReadFileSym := by simp only [s1, wp_norm, arm64_norm]
    have hlr1 : s1.readReg64 .lr = (blkPl_563).base + 44#64 := by
      simp only [s1, wp_norm, arm64_norm]
    have hs_files : s.fs.files = F0 :=
      hinv.files_eq (by simp [htr] : s.trace = T0 ++ []) (by simp [NoFsEv])
    have hs1_files : s1.fs.files = F0 := by simpa [s1, wp_norm, arm64_norm] using hs_files
    have hs1_fds : FdsGe3Closed s1.fs := by simpa [s1, wp_norm, arm64_norm] using hfds
    have hs1_lr : lrOk (s1.readReg64 .lr) := hlr1 ▸ hlr_ok
    have hLift : subroutine_ok (lsProg_563 H) (lsρ lsReadFileSym)
        (withFsInv
          (withLsCodeRoLoaded lsmpl
            (withPreGuard (fun s => lrOk (s.readReg64 .lr))
              (withFdsGe3Closed (readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))
          F0 T0) :=
      subroutine_ok_withFsInv hFs hRead F0 T0
    let g : ReadFileGhost := { pathA := pathPtr, path := p, ret := retSlot }
    obtain ⟨sm, hsteps_call, hout, -⟩ :=
      hLift.no_fault_before_outcome (g, st) (F ∗ R) s1
        hpc1
        (by simp [s1, wp_norm, arm64_norm, hRun])
        (withFsInv_pre_intro
          ⟨[], by simp [s1, wp_norm, arm64_norm, htr], fun _ => hs1_files⟩
          (by
            have hmem1 : s1.mem ⊨
                (withPreGuard (fun s => lrOk (s.readReg64 .lr))
                  (withFdsGe3Closed (readFileSpecPlaced rd pathOk A lim readStk ReadEnv))).pre
                  (g, st) s1 ∗ (F ∗ R) := by
              dsimp only [withPreGuard, withFdsGe3Closed, readFileSpecPlaced]
              rw [sepConj_assoc, satisfies_pure_sepConj,
                  sepConj_assoc, satisfies_pure_sepConj,
                  sepConj_assoc, satisfies_pure_sepConj]
              refine ⟨hs1_lr, hs1_fds, ⟨by simpa [s1, g, wp_norm, arm64_norm] using hx0,
                by simpa [s1, g, wp_norm, arm64_norm] using hx1,
                by simpa [s1, g, wp_norm, arm64_norm] using hx8,
                hlen, hpOk, hs1_files ▸ hfit⟩, ?_⟩
              have hsp1 : s1.sp = s.sp := by simp [s1, wp_norm, arm64_norm]
              rw [hsp1]
              refine satisfies_of_eq ?_ hm1
              dsimp only [g]
              sep_ac_rfl
            exact satisfies_lscro_pre hcrl1 hmem1))
        (by simpa [State.spAligned, s1, wp_norm, arm64_norm] using hAl)
        hL
    rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ |
      ⟨_, hpost⟩
    · obtain ⟨hinv_sm, hpost_rf0⟩ := withFsInv_post_elim hpost
      dsimp only [withLsCodeRoLoaded, withPreGuard, withFdsGe3Closed] at hpost_rf0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_rf0
      obtain ⟨hfds_sm, hpost_rf⟩ := hpost_rf0
      dsimp only [readFileSpecPlaced] at hpost_rf
      simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpost_rf
      obtain ⟨evs, hpost_evs⟩ := hpost_rf
      rw [satisfies_pure_sepConj] at hpost_evs
      obtain ⟨hevs_raw, hpost_r0⟩ := hpost_evs
      have hevs : ReadEnv F0 p evs := by simpa [g, hs1_files] using hevs_raw
      rw [satisfies_sepExists] at hpost_r0
      obtain ⟨r, hpost_r⟩ := hpost_r0
      rw [satisfies_pure_sepConj] at hpost_r
      obtain ⟨⟨hr1, hr2⟩, hmem_sm⟩ := hpost_r
      have hr_out : r = rd F0 p ∧ sm.trace = T0 :=
        ⟨hr1.trans (by simp [g, hs1_files]),
          hr2.trans (by simpa [s1, wp_norm, arm64_norm] using htr)⟩
      rw [hlr1] at hpcm
      have hsp_eq : sm.sp = s.sp := hspm.trans (by simp [s1, wp_norm, arm64_norm])
      have hsp_al_sm : sm.spAligned = true := by simpa [State.spAligned, hsp_eq] using hAl
      have hcs_s : CalleeSavedPreserved s sm := by
        simpa [CalleeSavedPreserved, s1, wp_norm, arm64_norm] using hcsm
      have hmem_sm' : sm.mem ⊨
          (ioVecAt A.repAlloc retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗
            A.pool lim (M.stepEvents evs st) sm ∗ F) ∗ R := by
        have hsp1 : s1.sp = s.sp := by simp [s1, wp_norm, arm64_norm]
        rw [hsp1] at hmem_sm
        refine satisfies_of_eq ?_ hmem_sm
        dsimp only [g]
        sep_ac_rfl
      obtain ⟨sf, hsteps_rest, hout_rest⟩ :=
        hnext sm hpcm hrunm hsp_eq hsp_al_sm hcs_s
          (hcrl1.of_keepsFrozen hsteps_call.keepsFrozen)
          hinv_sm hfds_sm evs hevs r hr_out R hmem_sm' (hsteps_call.codeLoaded hL)
      exact ⟨sf, hsteps_call.trans hsteps_rest, hout_rest⟩
    · dsimp only [withFsInv, withLsCodeRoLoaded, withPreGuard, withFdsGe3Closed,
        readFileSpecPlaced] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact (not_satisfies_false_sepConj hpost.2).elim
    · dsimp only [withFsInv, withLsCodeRoLoaded, withPreGuard, withFdsGe3Closed,
        readFileSpecPlaced] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact (not_satisfies_false_sepConj hpost.2).elim
    · dsimp only [withFsInv, withLsCodeRoLoaded, withPreGuard, withFdsGe3Closed,
        readFileSpecPlaced] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact (not_satisfies_false_sepConj hpost.2).elim

/-- `LsRetAddr624` specialization of `readCall_step_p_guard_fd` from a `subroutine_ok` witness. -/
theorem readCall_step_p_subroutine_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hRead : ReadCallHypPlacedFd A lim H rd pathOk readStk ReadEnv)
    (hFs : TraceFsSound (lsProg_563 H))
    (F0 : FsFiles) (T0 : List TraceEvent)
    {ret : BitVec 64} {s : State} {st : M.σ}
    {pathPtr retSlot : BitVec 64} {p : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hPC : s.pc = (blkPl_563).base + 40#64)
    (hRun : s.status = .Running)
    (hAl : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : FsInv F0 T0 s)
    (hfds : FdsGe3Closed s.fs)
    (htr : s.trace = T0)
    (hx0 : s.readReg64 .x0 = pathPtr)
    (hx1 : (s.readReg64 .x1).toNat = p.length)
    (hx8 : s.readReg64 .x8 = retSlot)
    (hlen : p.length < 2 ^ 32)
    (hpOk : pathOk p)
    (hfit : FitsEnv M lim st (ReadEnv F0 p))
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_563).base + 44#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.spAligned = true →
      CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      FsInv F0 T0 sf →
      FdsGe3Closed sf.fs →
      ∀ evs : List AllocEvent,
      ReadEnv F0 p evs →
      ∀ r : Except Unit (List (BitVec 8)),
      (r = rd F0 p ∧ sf.trace = T0) →
      SepWPp (lsProg_563 H) ret sf
        (ioVecAt A.repAlloc retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) Q Qp) :
    SepWPp (lsProg_563 H) ret s
      (((pathPtr ↦ₛ p) ∗ memRegion retSlot 24 ∗ stackAt s.sp readStk ∗ A.pool lim st s) ∗ F) Q Qp :=
  readCall_step_p_guard_fd hRead
    (lsRetAddr624_blockPlacement_base_add 563 44#64 (by decide) (by decide))
    hFs F0 T0 hPC hRun hAl hcrl hinv hfds htr hx0 hx1 hx8 hlen hpOk hfit hnext

/-- `LsRetAddr624` specialization of `readCall_step_p_guard_fd` from a `HookSat` witness. -/
theorem readCall_step_p_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hSat : HookSat H lsReadFileSym
      (withLsRetAddr624AndFds (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hFs : TraceFsSound (lsProg_563 H))
    (F0 : FsFiles) (T0 : List TraceEvent)
    {ret : BitVec 64} {s : State} {st : M.σ}
    {pathPtr retSlot : BitVec 64} {p : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hPC : s.pc = (blkPl_563).base + 40#64)
    (hRun : s.status = .Running)
    (hAl : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : FsInv F0 T0 s)
    (hfds : FdsGe3Closed s.fs)
    (htr : s.trace = T0)
    (hx0 : s.readReg64 .x0 = pathPtr)
    (hx1 : (s.readReg64 .x1).toNat = p.length)
    (hx8 : s.readReg64 .x8 = retSlot)
    (hlen : p.length < 2 ^ 32)
    (hpOk : pathOk p)
    (hfit : FitsEnv M lim st (ReadEnv F0 p))
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_563).base + 44#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.spAligned = true →
      CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      FsInv F0 T0 sf →
      FdsGe3Closed sf.fs →
      ∀ evs : List AllocEvent,
      ReadEnv F0 p evs →
      ∀ r : Except Unit (List (BitVec 8)),
      (r = rd F0 p ∧ sf.trace = T0) →
      SepWPp (lsProg_563 H) ret sf
        (ioVecAt A.repAlloc retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) Q Qp) :
    SepWPp (lsProg_563 H) ret s
      (((pathPtr ↦ₛ p) ∗ memRegion retSlot 24 ∗ stackAt s.sp readStk ∗ A.pool lim st s) ∗ F) Q Qp :=
  readCall_step_p_subroutine_fd
    (lsReadFile_withLsCodeRoLoaded_of_hookSat (callerProg := lsProg_563 H) (i := 563) hSat)
    hFs F0 T0 hPC hRun hAl hcrl hinv hfds htr hx0 hx1 hx8 hlen hpOk hfit hnext

/-- `keepSet`-guarded `HookSat` specialization of `readCall_step_p_guard_fd`. -/
theorem readCall_step_p_keep_fd [LibsignalPlacement] {M : AllocCostModel}
    {keepSet : BitVec 64 → Bool}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hSat : HookSat H lsReadFileSym
      (withFdsGe3Closed
        (withKeepLrAndFds keepSet (readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))
    (hlr : keepSet ((blkPl_563).base + 44#64) = false)
    (hFs : TraceFsSound (lsProg_563 H))
    (F0 : FsFiles) (T0 : List TraceEvent)
    {ret : BitVec 64} {s : State} {st : M.σ}
    {pathPtr retSlot : BitVec 64} {p : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hPC : s.pc = (blkPl_563).base + 40#64)
    (hRun : s.status = .Running)
    (hAl : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : FsInv F0 T0 s)
    (hfds : FdsGe3Closed s.fs)
    (htr : s.trace = T0)
    (hx0 : s.readReg64 .x0 = pathPtr)
    (hx1 : (s.readReg64 .x1).toNat = p.length)
    (hx8 : s.readReg64 .x8 = retSlot)
    (hlen : p.length < 2 ^ 32)
    (hpOk : pathOk p)
    (hfit : FitsEnv M lim st (ReadEnv F0 p))
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_563).base + 44#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.spAligned = true →
      CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      FsInv F0 T0 sf →
      FdsGe3Closed sf.fs →
      ∀ evs : List AllocEvent,
      ReadEnv F0 p evs →
      ∀ r : Except Unit (List (BitVec 8)),
      (r = rd F0 p ∧ sf.trace = T0) →
      SepWPp (lsProg_563 H) ret sf
        (ioVecAt A.repAlloc retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) Q Qp) :
    SepWPp (lsProg_563 H) ret s
      (((pathPtr ↦ₛ p) ∗ memRegion retSlot 24 ∗ stackAt s.sp readStk ∗ A.pool lim st s) ∗ F) Q Qp :=
  readCall_step_p_guard_fd (lrOk := fun lr => keepSet lr = false)
    (lsReadFile_withLsCodeRoLoaded_of_hookSat (callerProg := lsProg_563 H) (i := 563)
      (hookSat_keepLr_withFds_of_withFds_keepLrAndFds hSat))
    hlr hFs F0 T0 hPC hRun hAl hcrl hinv hfds htr hx0 hx1 hx8 hlen hpOk hfit hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAuxFd
