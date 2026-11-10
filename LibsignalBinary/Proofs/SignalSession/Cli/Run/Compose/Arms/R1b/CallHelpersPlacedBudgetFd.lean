/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public meta import ProofLib -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFrame
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout

/-!
# `FdsGe3Closed`-Threaded I/O and Splitter Callee `SepWPp` Wrappers for Arm `R1b`

File-descriptor-preserving (`FdsGe3Closed`) `SepWPp` call wrappers on Block `579` for `Dir::path`
(Block `596`), `read_file`, `read_bundle::{closure#0}` (Block `563`), `split_signed` (Block `592`),
and `split_id` (Block `593`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (doReserveStackX)
open CryptoVerification.LibsignalTripleRatchetRepr
  (okTagVec speAt speWord strRefAt utf8 vecResultAt)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (lsReadFileSym)
open CryptoVerification.SignalSession.Cli
  (getResultAt ioVecAt splitId splitOkTag splitSigned)
open CryptoVerification.SignalSession.Cli.BundleRead.Helpers (stackAt_split_sub)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliWrOk handleErrorSymCli ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (memRegion_16_cells vecU8_to_ownedBytes)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InRunPlaced PanicK r1b_CodeOk r1b_StackBounds r1b_cells2_to_region16
   r1b_entails_frame_core r1b_ownedBytes_borrow r1b_ownedBytes_rejoin r1b_ownedRest
   r1b_sepWPp_drop_left r1b_sepWPp_frame_core r1b_sepWPp_with_ro_placed r1b_spAligned_of_fsp
   runFsp runPcPlaced runProgPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (sepWP_with_vm_oom)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots pathNeed runFrame)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
  (path_placed_caller_ok_of_allocFs_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed withLsRetAddr624AndFds withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
  (r1b_call_splitId_placed_fd r1b_call_splitSigned_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_placed r1b_files_eq_of_trace_eq_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (bundleReadSpecPlaced pathSpecPlaced readFileSpecPlaced)

theorem path_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) {stk : Nat} (hstk : pathNeed ≤ stk) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv stk)) :=
  path_placed_caller_ok_of_allocFs_fd (callerProg := runProgPlaced H) (i := 579)
    (resStack := doReserveStackX) hh.allocFs (by decide) hstk
    (hh.panics handleErrorSymCli (by decide)) (by decide)

theorem r1b_call_path_ro_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret dirCap dirPtr nameA : BitVec 64} {dir name : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hro : ∀ {m : Memory} {R : SepProp}, r1b_CodeOk m → (m ⊨ R) → (m ⊨ (nameA ↦ᵣ name) ∗ R))
    (hpc : st_bl.pc = lsmpl.base 596)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ret)
    (hx1 : st_bl.readReg64 .x1 = dirPtr)
    (hx2 : (st_bl.readReg64 .x2).toNat = dir.length)
    (hx3 : st_bl.readReg64 .x3 = nameA)
    (hx4 : (st_bl.readReg64 .x4).toNat = name.length)
    (hdir_lt : dir.length < 2 ^ 32)
    (hname_lt : name.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (PathEnv dir name))
    (hfds : FdsGe3Closed st_bl.fs)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (pCap pPtr : BitVec 64),
      PathEnv dir name evs →
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      FdsGe3Closed sf.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ pCap) ∗ ((ret + 8#64) ↦₆₄ pPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length) ∗
          ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length)
            (dir ++ [0x2f#8] ++ name) ∗
          ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
        memRegion ret 24 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  refine r1b_sepWPp_with_ro_placed hinv hro ?_
  rw [r1b_ownedBytes_borrow A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir]
  have hcomm :
      ((nameA ↦ᵣ name) ∗
        (⌜BitVec.ofNat 64 dir.length = BitVec.ofNat 64 dir.length ∧
            dir.length ≤ dirCap.toNat ∧ dirCap.toNat < 2 ^ 63 ∧ dirPtr ≠ 0⌝ ∗
          (dirPtr ↦ₛ dir) ∗ r1b_ownedRest A.repAlloc dirCap dirPtr dir.length) ∗
        memRegion ret 24 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st st_bl ∗ F) =
      (⌜BitVec.ofNat 64 dir.length = BitVec.ofNat 64 dir.length ∧
          dir.length ≤ dirCap.toNat ∧ dirCap.toNat < 2 ^ 63 ∧ dirPtr ≠ 0⌝ ∗
        ((dirPtr ↦ₛ dir) ∗ (nameA ↦ᵣ name) ∗ memRegion ret 24 ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗
          (r1b_ownedRest A.repAlloc dirCap dirPtr dir.length ∗ F))) := by
    sep_ac_rfl
  rw [hcomm]
  refine SepWPp.pure_elim fun hdir_inv => ?_
  rcases hdir_inv with ⟨-, hdir_le, hdir_cap, hdir_ne⟩
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hpath_raw := path_placed_ok_fd hh hbnd.path; unfold pathSpecPlaced at hpath_raw
  have hpath_call := subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed hpath_raw
  refine r1b_call_placed
    (x := ({ dirA := dirPtr, dir := dir, dirRo := false,
             nameA := nameA, name := name, nameRo := true, ret := ret }, st))
    hpath_call hinv hpc hrun hal_bl hlr hpanicK
    (F := r1b_ownedRest A.repAlloc dirCap dirPtr dir.length ∗ F)
    ?_ (hnext := ?_)
  · dsimp only [withFdsGe3Closed, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hfds
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hdir_lt, hname_lt, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withFdsGe3Closed, bytesAt]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hfds_f => ?_
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc,
      sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun hp => ?_
    rcases hp with ⟨htr_f, hevs⟩
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    have hrejoin := r1b_ownedBytes_rejoin A.repAlloc dirCap dirPtr dir hdir_le hdir_cap hdir_ne
    have hvec := vecU8_to_ownedBytes A.repAlloc ret (dir ++ [0x2f#8] ++ name)
    simp only [List.append_assoc] at hvec ⊢
    refine sepWPp_weaken_pre
      (P' := (nameA ↦ᵣ name) ∗
        (∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64,
          (ret ↦₆₄ pCap) ∗ ((ret + 8#64) ↦₆₄ pPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (dir ++ ([0x2f#8] ++ name)).length) ∗
          ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 (dir ++ ([0x2f#8] ++ name)).length)
            (dir ++ ([0x2f#8] ++ name))) ∗
        ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
    · rw [hsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (nameA ↦ᵣ name) ∗ vecU8 A.repAlloc ret (dir ++ ([0x2f#8] ++ name)) ∗
        ((dirPtr ↦ₛ dir) ∗ r1b_ownedRest A.repAlloc dirCap dirPtr dir.length) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ F by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono hvec (sepConj_mono_left hrejoin))
    · refine r1b_sepWPp_drop_left ?_
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun pCap => SepWPp.exists_elim fun pPtr => ?_
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
      simpa only [List.append_assoc] using
        hnext sf evs pCap pPtr hevs hin_f hcs_f hfiles_f htr_f hfds_f

/-- `FdsGe3Closed`- and `LsRetAddr624`-guarded `read_file` call wrapper on Block `579`. -/
theorem r1b_call_readFile_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {pathCap pathPtr ret : BitVec 64} {path : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsReadFileSym) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff))
    (hx0 : st_bl.readReg64 .x0 = pathPtr) (hx1 : (st_bl.readReg64 .x1).toNat = path.length)
    (hx8 : st_bl.readReg64 .x8 = ret) (hlen : path.length < 2 ^ 32)
    (hok_p : cliWrOk path)
    (hfit : FitsEnv M lim st (cEnvs.readFile st_bl.fs.files path))
    (hfds : FdsGe3Closed st_bl.fs)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (w1 w2 : BitVec 64),
      cEnvs.readFile st_bl.fs.files path evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      (cliIo.rd st_bl.fs.files path = .error () ∧
        sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace) →
      FdsGe3Closed sf.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ 0xffffffffffffffff#64) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
          ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (rCap rPtr : BitVec 64) (bs : List (BitVec 8)),
      cEnvs.readFile st_bl.fs.files path evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      cliIo.rd st_bl.fs.files path = .ok bs → sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      FdsGe3Closed sf.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ rCap) ∗ ((ret + 8#64) ↦₆₄ rPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ownedBytes A.repAlloc rCap rPtr (BitVec.ofNat 64 bs.length) bs ∗
          ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
        memRegion ret 24 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  rw [r1b_ownedBytes_borrow A.repAlloc pathCap pathPtr (BitVec.ofNat 64 path.length) path]
  have hsplit := stackAt_split_sub (runFsp s0)
    (resStack - runFrame) B.readFile hbnd.readFile hbnd.sub64
  rw [hsplit]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - B.readFile)
  have hcomm :
      ((⌜BitVec.ofNat 64 path.length = BitVec.ofNat 64 path.length ∧
            path.length ≤ pathCap.toNat ∧ pathCap.toNat < 2 ^ 63 ∧ pathPtr ≠ 0⌝ ∗
          (pathPtr ↦ₛ path) ∗ r1b_ownedRest A.repAlloc pathCap pathPtr path.length) ∗
        memRegion ret 24 ∗ (subFrame ∗ stackAt (runFsp s0) B.readFile) ∗
        A.pool lim st st_bl ∗ F) =
      (⌜BitVec.ofNat 64 path.length = BitVec.ofNat 64 path.length ∧
          path.length ≤ pathCap.toNat ∧ pathCap.toNat < 2 ^ 63 ∧ pathPtr ≠ 0⌝ ∗
        ((pathPtr ↦ₛ path) ∗ memRegion ret 24 ∗ stackAt (runFsp s0) B.readFile ∗
          A.pool lim st st_bl ∗
          (r1b_ownedRest A.repAlloc pathCap pathPtr path.length ∗ subFrame ∗ F))) := by
    dsimp +zetaDelta only [subFrame]
    sep_ac_rfl
  rw [hcomm]
  refine SepWPp.pure_elim fun ⟨_, hp_le, hp_cap, hp_ne⟩ => ?_
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (x := ({ pathA := pathPtr, path := path, ret := ret }, st))
    (subroutine_ok_withLsCodeRoLoaded_of_plain hc.readFile)
    hinv hpc hrun hal_bl hlr hpanicK
    (F := r1b_ownedRest A.repAlloc pathCap pathPtr path.length ∗ subFrame ∗ F)
    ?_ (hnext := ?_)
  · dsimp only [withLsRetAddr624AndFds, withPreGuard, withFdsGe3Closed, readFileSpecPlaced]
    simp only [hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right (hlr.symm ▸ hlr_ls)
    apply Entails.pure_right hfds
    apply Entails.pure_right ⟨hx0, hx1, hx8, hlen, hok_p, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withLsRetAddr624AndFds, withPreGuard, withFdsGe3Closed, readFileSpecPlaced]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hfds_f => ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun hevs => ?_
    refine SepWPp.exists_elim fun r => SepWPp.pure_elim fun hdisj => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hrejoin := r1b_ownedBytes_rejoin A.repAlloc pathCap pathPtr path hp_le hp_cap hp_ne
    cases r with
    | error u =>
      cases u
      dsimp only [ioVecAt]
      have hout :
          cliIo.rd st_bl.fs.files path = .error () ∧
            sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace :=
        ⟨hdisj.1.symm, r1b_files_eq_of_trace_eq_placed hh hsteps hdisj.2, hdisj.2⟩
      refine sepWPp_weaken_pre
        (P' := (ret ↦₆₄ 0xffffffffffffffff#64) ∗
          (∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2)) ∗
          ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
      · rw [hsp, hsplit]
        refine Entails.trans (Entails.of_eq (show _ =
          (ret ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ret + 8#64) 16 ∗
          ((pathPtr ↦ₛ path) ∗ r1b_ownedRest A.repAlloc pathCap pathPtr path.length) ∗
          (subFrame ∗ stackAt (runFsp s0) B.readFile) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F by
            dsimp +zetaDelta only [subFrame]; sep_ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono (memRegion_16_cells ret)
          (sepConj_mono_left hrejoin))
      · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 => ?_
        rw [sepConj_assoc]
        exact herr sf evs w1 w2 hevs hin_f hcs_f hout hfds_f
    | ok bs =>
      dsimp only [ioVecAt]
      rcases hdisj with ⟨hrd, htr_f⟩
      have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
      have hvec := vecU8_to_ownedBytes A.repAlloc ret bs
      refine sepWPp_weaken_pre
        (P' := (∃∗ rCap : BitVec 64, ∃∗ rPtr : BitVec 64,
          (ret ↦₆₄ rCap) ∗ ((ret + 8#64) ↦₆₄ rPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ownedBytes A.repAlloc rCap rPtr (BitVec.ofNat 64 bs.length) bs) ∗
          ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
      · rw [hsp, hsplit]
        refine Entails.trans (Entails.of_eq (show _ =
          vecU8 A.repAlloc ret bs ∗
          ((pathPtr ↦ₛ path) ∗ r1b_ownedRest A.repAlloc pathCap pathPtr path.length) ∗
          (subFrame ∗ stackAt (runFsp s0) B.readFile) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F by
            dsimp +zetaDelta only [subFrame]; sep_ac_rfl)) ?_
        exact sepConj_mono hvec (sepConj_mono_left hrejoin)
      · simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun rCap => SepWPp.exists_elim fun rPtr => ?_
        rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
        exact hok sf evs rCap rPtr bs hevs hin_f hcs_f hrd.symm hfiles_f htr_f hfds_f

/-- `FdsGe3Closed`-preserving `read_bundle::{closure#0}` call wrapper on Block `579`. -/
theorem r1b_call_bundleRead_ro_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret dirCap dirPtr nameA : BitVec 64} {dir name : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hro : ∀ {m : Memory} {R : SepProp}, r1b_CodeOk m → (m ⊨ R) → (m ⊨ (nameA ↦ᵣ name) ∗ R))
    (hpc : st_bl.pc = lsmpl.base 563) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ret) (hx1 : st_bl.readReg64 .x1 = dirPtr)
    (hx2 : (st_bl.readReg64 .x2).toNat = dir.length) (hx3 : st_bl.readReg64 .x3 = nameA)
    (hx4 : (st_bl.readReg64 .x4).toNat = name.length)
    (hdir_lt : dir.length < 2 ^ 32) (hname_lt : name.length < 2 ^ 32)
    (hok_p : cliWrOk (dir ++ [0x2f#8] ++ name))
    (hfit : FitsEnv M lim st (cEnvs.bundleRead st_bl.fs.files dir name))
    (hfds : FdsGe3Closed st_bl.fs)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      cEnvs.bundleRead st_bl.fs.files dir name evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      (cliIo.rd st_bl.fs.files (dir ++ [0x2f#8] ++ name) = .error () ∧
        sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace) →
      FdsGe3Closed sf.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (rCap rPtr : BitVec 64) (bs : List (BitVec 8)),
      cEnvs.bundleRead st_bl.fs.files dir name evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      cliIo.rd st_bl.fs.files (dir ++ [0x2f#8] ++ name) = .ok bs →
      sf.fs.files = st_bl.fs.files → sf.trace = st_bl.trace →
      FdsGe3Closed sf.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ okTagVec) ∗
          ((ret + 8#64) ↦₆₄ rCap) ∗ ((ret + 16#64) ↦₆₄ rPtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc rCap rPtr (BitVec.ofNat 64 bs.length) bs ∗
          ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
        memRegion ret 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  refine r1b_sepWPp_with_ro_placed hinv hro ?_
  rw [r1b_ownedBytes_borrow A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir]
  have hcomm :
      ((nameA ↦ᵣ name) ∗
        (⌜BitVec.ofNat 64 dir.length = BitVec.ofNat 64 dir.length ∧
            dir.length ≤ dirCap.toNat ∧ dirCap.toNat < 2 ^ 63 ∧ dirPtr ≠ 0⌝ ∗
          (dirPtr ↦ₛ dir) ∗ r1b_ownedRest A.repAlloc dirCap dirPtr dir.length) ∗
        memRegion ret 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st st_bl ∗ F) =
      (⌜BitVec.ofNat 64 dir.length = BitVec.ofNat 64 dir.length ∧
          dir.length ≤ dirCap.toNat ∧ dirCap.toNat < 2 ^ 63 ∧ dirPtr ≠ 0⌝ ∗
        ((dirPtr ↦ₛ dir) ∗ (nameA ↦ᵣ name) ∗ memRegion ret 48 ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗
          (r1b_ownedRest A.repAlloc dirCap dirPtr dir.length ∗ F))) := by
    sep_ac_rfl
  rw [hcomm]
  refine SepWPp.pure_elim fun ⟨_, hdir_le, hdir_cap, hdir_ne⟩ => ?_
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hbr_raw := hc.bundleRead hbnd.bundleRead; unfold bundleReadSpecPlaced at hbr_raw
  have hbr_call := subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed hbr_raw
  refine r1b_call_placed
    (x := ({ ret := ret, dirA := dirPtr, dir := dir, dirRo := false,
             nameA := nameA, name := name, nameRo := true }, st))
    hbr_call hinv hpc hrun hal_bl hlr hpanicK
    (F := r1b_ownedRest A.repAlloc dirCap dirPtr dir.length ∗ F)
    ?_ (hnext := ?_)
  · dsimp only [withFdsGe3Closed, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hfds
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hdir_lt, hname_lt, hok_p, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withFdsGe3Closed, bytesAt]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hfds_f => ?_
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs =>
      SepWPp.exists_elim fun r =>
      SepWPp.pure_elim fun hdisj => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hrejoin := r1b_ownedBytes_rejoin A.repAlloc dirCap dirPtr dir hdir_le hdir_cap hdir_ne
    cases r with
    | error u =>
      cases u
      dsimp only [getResultAt, speAt]
      rcases hdisj with ⟨hrd, htr_f, hevs⟩
      have hout :
          cliIo.rd st_bl.fs.files (dir ++ [0x2f#8] ++ name) = .error () ∧
            sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace :=
        ⟨hrd.symm, r1b_files_eq_of_trace_eq_placed hh hsteps htr_f, htr_f⟩
      have hstr_drop : strRefAt (ret + 32#64) (utf8 "read") ⊢
          ∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "read") ∗ memRegion (ret + 32#64) 16 := by
        dsimp only [strRefAt]
        refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_right fnPtr ?_
        have hcells :
            ((ret + 32#64) ↦₆₄ fnPtr) ∗
              ((ret + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ⊢
            memRegion (ret + 32#64) 16 := r1b_cells2_to_region16 _ _ _
        exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_right hcells)
      have hev : ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ⊢
          ∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs := by
        rw [sepExists_sepConj_right]
        refine Entails.sepExists_elim fun eBs => Entails.sepExists_right eBs ?_
        have hv := vecU8_to_ownedBytes A.repAlloc (ret + 8#64) eBs
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
        exact Entails.trans (sepConj_mono_right hv) (by
          simp only [sepExists_sepConj_right]
          exact Entails.sepExists_elim fun eCap => Entails.sepExists_right eCap
            (Entails.sepExists_elim fun ePtr => Entails.sepExists_right ePtr
              (Entails.of_eq (by sep_ac_rfl))))
      refine sepWPp_weaken_pre
        (P' := (nameA ↦ᵣ name) ∗
          (∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs) ∗
          (∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "read") ∗ memRegion (ret + 32#64) 16) ∗
          ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          (nameA ↦ᵣ name) ∗
          ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ∗
          strRefAt (ret + 32#64) (utf8 "read") ∗
          ((dirPtr ↦ₛ dir) ∗ r1b_ownedRest A.repAlloc dirCap dirPtr dir.length) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F by sep_ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono hev (sepConj_mono hstr_drop
          (sepConj_mono_left hrejoin)))
      · refine r1b_sepWPp_drop_left ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun fnPtr =>
          SepWPp.exists_elim fun eBs =>
          SepWPp.exists_elim fun eCap =>
          SepWPp.exists_elim fun ePtr => ?_
        refine sepWPp_weaken_pre
          (P' := (fnPtr ↦ᵣ utf8 "read") ∗
            ((ret ↦₆₄ speWord 1) ∗
              ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
              ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
              memRegion (ret + 32#64) 16 ∗
              ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
              ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evs st) sf ∗ F))
          ?_ ?_
        · exact Entails.of_eq (by sep_ac_rfl)
        · exact r1b_sepWPp_drop_left (herr sf evs eCap ePtr eBs hevs hin_f hcs_f hout hfds_f)
    | ok bs =>
      dsimp only [getResultAt, vecResultAt]
      rcases hdisj with ⟨hrd, htr_f, hevs⟩
      have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
      have hvec := vecU8_to_ownedBytes A.repAlloc (ret + 8#64) bs
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hvec
      refine sepWPp_weaken_pre
        (P' := (nameA ↦ᵣ name) ∗
          (ret ↦₆₄ okTagVec) ∗
          (∃∗ rCap : BitVec 64, ∃∗ rPtr : BitVec 64,
            ((ret + 8#64) ↦₆₄ rCap) ∗ ((ret + 16#64) ↦₆₄ rPtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ownedBytes A.repAlloc rCap rPtr (BitVec.ofNat 64 bs.length) bs) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          (nameA ↦ᵣ name) ∗ (ret ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (ret + 8#64) bs ∗
          memRegion (ret + 32#64) 16 ∗
          ((dirPtr ↦ₛ dir) ∗ r1b_ownedRest A.repAlloc dirCap dirPtr dir.length) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F by sep_ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hvec
          (sepConj_mono_right (sepConj_mono_left hrejoin))))
      · refine r1b_sepWPp_drop_left ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun rCap => SepWPp.exists_elim fun rPtr => ?_
        refine sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hok sf evs rCap rPtr bs hevs hin_f hcs_f hrd.symm hfiles_f htr_f hfds_f)

theorem r1b_call_splitSigned_placed_fds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret fp : BitVec 64} {file : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 592) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ret) (hx1 : st_bl.readReg64 .x1 = fp)
    (hx2 : (st_bl.readReg64 .x2).toNat = file.length)
    (hfit : FitsEnv M lim st (cEnvs.splitSigned file))
    (hfds : FdsGe3Closed st_bl.fs)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      cEnvs.splitSigned file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitSigned file = none → sf.fs.files = st_bl.fs.files → sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (id : BitVec 32) (key sig : List (BitVec 8)),
      cEnvs.splitSigned file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitSigned file = some (id, key, sig) → sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      FdsGe3Closed sf.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ splitOkTag) ∗
          ((ret + 8#64) ↦₆₄ (fp + 4#64)) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗
          ((ret + 24#64) ↦₃₂ id) ∗ memRegion (ret + 28#64) 4 ∗
          ((ret + 32#64) ↦₆₄ (fp + 4#64 + BitVec.ofNat 64 key.length)) ∗
          ((ret + 40#64) ↦₆₄ 64#64) ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((fp ↦ₛ file) ∗ memRegion ret 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom :=
  r1b_call_splitSigned_placed_fd hh hc hbnd hinv hpc hrun hsp hfp hvregs hsp0 hlr hx0 hx1 hx2
    hfit hpanicK herr
    (fun sf evs id key sig hevs hin hcs hsome hfs_eq hfiles htr =>
      hok sf evs id key sig hevs hin hcs hsome hfiles htr (hfs_eq ▸ hfds))

theorem r1b_call_splitId_placed_fds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret fp : BitVec 64} {file : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 593) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ret) (hx1 : st_bl.readReg64 .x1 = fp)
    (hx2 : (st_bl.readReg64 .x2).toNat = file.length)
    (hfit : FitsEnv M lim st (cEnvs.splitId file))
    (hfds : FdsGe3Closed st_bl.fs)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      cEnvs.splitId file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitId file = none → sf.fs.files = st_bl.fs.files → sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (id : BitVec 32) (key : List (BitVec 8)),
      cEnvs.splitId file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitId file = some (id, key) → sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      FdsGe3Closed sf.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ splitOkTag) ∗
          ((ret + 8#64) ↦₃₂ id) ∗ memRegion (ret + 12#64) 4 ∗
          ((ret + 16#64) ↦₆₄ (fp + 4#64)) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗
          memRegion (ret + 32#64) 16 ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((fp ↦ₛ file) ∗ memRegion ret 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom :=
  r1b_call_splitId_placed_fd hh hc hbnd hinv hpc hrun hsp hfp hvregs hsp0 hlr hx0 hx1 hx2
    hfit hpanicK herr
    (fun sf evs id key hevs hin hcs hsome hfs_eq hfiles htr =>
      hok sf evs id key hevs hin hcs hsome hfiles htr (hfs_eq ▸ hfds))

scoped elab "by_vm_open " tac:tacticSeq : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm_oom))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let e2 := ty.getArg! 0
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
    let rem ← Lean.Elab.Tactic.getGoals
    unless rem.isEmpty do
      throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
    Lean.Elab.Tactic.setGoals savedGoals.tail!
    let prf1 ← Lean.instantiateMVars g1
    let prf2 := prf1.replace fun sub =>
      if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
    g.assign prf2

scoped macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

meta def r1bStripLetsSP : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsSP n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsSP n e
  | _, e => e

meta def r1bSplitSepSP : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsSP 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepSP fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepSP fuel sepSample (e.getArg! (ar - 1))
    else #[e]

meta def r1bIsDefEqPureSP (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsSP 64 x; let a := r1bStripLetsSP 64 a
  let xf := x.getAppFn; let af := a.getAppFn
  if xf.constName? != af.constName? then return false
  let n := x.getAppNumArgs
  if n != a.getAppNumArgs then return false
  let st ← Lean.saveState
  let mut ok ← if xf.constName?.isNone then
      if xf.isFVar != af.isFVar || xf.isProj != af.isProj then pure false
      else Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq xf af
    else pure true
  for i in [0:n] do
    if ok then
      ok ← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (x.getArg! i) (a.getArg! i)
  st.restore
  return ok

meta def r1bComputeRestSP (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepSP 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepSP 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureSP x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "{ctxName}: unmatched atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let ar := sepSample.getAppNumArgs
  let mkSep (l r : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (ar - 2) ++ #[l, r])
  match rem.reverse with
  | [] => return empExpr
  | last :: rest => return rest.foldl (fun acc x => mkSep x acc) last

scoped elab (priority := high) "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsSP 64 exp
  let p := expS.getArg! (ear - 2); let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2); let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestSP "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  if ← r1bIsDefEqPureSP r empExpr then
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p a1))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq a2 q))
    Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
  else
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p (mkSep a1 r)))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq (mkSep a2 r) q))
    Lean.Meta.mkAppOptM ``r1b_entails_frame_core
      #[some a1, some a2, some r, some p, some q, h1Expr, hExpr, h2Expr]

scoped elab (priority := high) "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsSP 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2); let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestSP "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  if ← r1bIsDefEqPureSP r empExpr then
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p a1))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq a2 a2))
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, a2, q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    let hent ← Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
    Lean.Meta.mkAppM ``sepWPp_weaken_pre #[hent, hkExpr]
  else
    let a2IsEmp ← r1bIsDefEqPureSP a2 empExpr
    let p' := if a2IsEmp then r else mkSep a2 r
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p (mkSep a1 r)))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq (mkSep a2 r) p'))
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, p', q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    Lean.Meta.mkAppOptM ``r1b_sepWPp_frame_core
      #[some prog, some ret, some st, some a1, some a2, some r, some p, some p',
        some q, some qp, some oom, h1Expr, hExpr, h2Expr, hkExpr]

scoped elab:10 (priority := high) "r1b_call_frame" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsSP 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsSP 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepSP 64 sepSample p).toList
  let p's := (r1bSplitSepSP 64 sepSample p').toList
  let mut mvarFOpt : Option Lean.Expr := none
  let mut a1s : List Lean.Expr := []
  for a in p's do
    let ai ← Lean.instantiateMVars a
    if mvarFOpt.isNone && ai.isMVar then mvarFOpt := some ai
    else a1s := a1s.concat ai
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureSP x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "r1b_call_frame: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with
    | [] => empExpr
    | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then
    discard <| Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq mf remProd
  let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some eqTy)
  let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[ent, hExpr]

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudgetFd
