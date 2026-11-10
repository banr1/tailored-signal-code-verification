/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout

/-!
# Budget-Threaded Allocator and I/O Callee `SepWPp` Wrappers for Arm `R1b`

Budget-threaded `SepWPp` call wrappers on Block `579` for the allocator shim, `__rust_alloc`,
`memcpy`, `try_allocate_in` (Block `588`), `Dir::path` (Block `596`), `read_file`, and
`read_bundle::{closure#0}` (Block `563`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack lsMemcpySym sessionMemcpyRegionSpec sessionShimSpec withStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (okTagVec speAt speWord strRefAt utf8 vecResultAt)
open CryptoVerification.RustHeap (LayoutOk vecU8)
open CryptoVerification.SignalSession
  (lsReadFileSym lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (getResultAt ioVecAt)
open CryptoVerification.SignalSession.Cli.BundleRead.Helpers (stackAt_split_sub)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliWrOk ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (memRegion_16_cells vecU8_to_ownedBytes)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InRunPlaced PanicK r1b_CodeOk r1b_StackBounds r1b_cells2_to_region16
   r1b_ownedBytes_borrow r1b_ownedBytes_rejoin r1b_ownedRest
   r1b_sepWPp_drop_left r1b_sepWPp_with_ro_placed r1b_spAligned_of_fsp
   runFsp runPcPlaced runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents NullAllowed OomPreserved
   RustCliAllocBudget VmPreserved not_nullAllowed_of_fitsAllocEvents rustAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocBudgetSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (TryAllocateInEnv tryAllocateInSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3PlacedBudget
  (tryAllocateInRustSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_allocFs_placed_ok r1b_call_placed r1b_files_eq_of_trace_eq_placed
   r1b_memcpyRegionFs_placed_ok r1b_shimFs_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced path_placed_ok runTryAllocateIn3_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (bundleReadSpecPlaced pathSpecPlaced readFileSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocSpecWithStack)

theorem r1b_call_shim_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsRustNoAllocShimSymCli)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      VmPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (stackAt (runFsp s0) (resStack - runFrame) ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (stackAt (runFsp s0) (resStack - runFrame) ∗ F) Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hsplit := stackAt_split_sub (runFsp s0)
    (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64
  rw [hsplit, sepConj_assoc]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - extHookStack)
  refine r1b_call_placed () (r1b_shimFs_placed_ok hh) hinv hpc hrun hal_bl hlr hpanicK
    (F := subFrame ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec, sessionShimSpec]
    simp only [hsp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec, sessionShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f =>
      SepWPp.pure_elim fun hvm_f =>
      SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    refine sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hvm_f hfs_f htr_f)
    rw [hsp, hsplit]
    dsimp +zetaDelta only [subFrame]
    exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_shim_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsRustNoAllocShimSymCli)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sf ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F) Q Qp oom :=
  r1b_call_shim_placed hh hbnd hinv hpc hrun hsp hfp hvregs hsp0 hlr hpanicK
    fun sf hin_f hcs_f hvm_f hfs_f htr_f => by
      rw [← A.pool_of_vmPreserved hvm_f]
      exact hnext sf hin_f hcs_f hfs_f htr_f

theorem r1b_call_alloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff size align : Nat}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsRustAllocSymCli)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : (st_bl.readReg64 .x0).toNat = size)
    (hx1 : (st_bl.readReg64 .x1).toNat = align)
    (_hpos : 0 < size)
    (hlay : LayoutOk size align)
    (hal : align ≤ 2 ^ 31 := by decide)
    (hfit : FitsEvents M lim st (rustAllocEvents size align))
    (hpanicK : PanicK g s0 Qp)
    (hok : ∀ (sf : State) (buf : BitVec 64),
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.readReg64 .x0 = buf →
      buf ≠ 0#64 →
      buf.toNat % align = 0 →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (A.live buf size align ∗ memRegion buf size ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗ F) Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff) := by
      first | assumption | simp (config := { decide := true })
        [CryptoVerification.SignalSession.Cli.RunCompose.runPcPlaced, wp_norm, arm64_norm,
         LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F) Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hsplit := stackAt_split_sub (runFsp s0)
    (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64
  rw [hsplit]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - extHookStack)
  refine r1b_call_placed (size, align, st) (r1b_allocFs_placed_ok hh) hinv hpc hrun hal_bl hlr hpanicK
    (F := subFrame ∗ F) ?_ (hoom := ?_) (hnext := ?_)
  · dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    rw [hsp]
    conv => rhs; rw [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, ⟨hlay, hal⟩, hlr ▸ hlr_ls⟩
    dsimp +zetaDelta only [subFrame]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro _ _ _ ho
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at ho
    rw [satisfies_pure_sepConj] at ho
    exact (ho.1.1 hfit).elim
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp +zetaDelta only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => SepWPp.pure_elim fun hacp => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte]
      have hcomm :
          (A.pool lim st sf ∗ stackAt st_bl.sp extHookStack ∗
            ⌜NullAllowed size align⌝ ∗ subFrame ∗ F) =
          (⌜NullAllowed size align⌝ ∗
            (A.pool lim st sf ∗ stackAt st_bl.sp extHookStack ∗ subFrame ∗ F)) := by
        sep_ac_rfl
      rw [hcomm]
      exact SepWPp.pure_elim fun hna =>
        (not_nullAllowed_of_fitsAllocEvents ⟨hlay, hal⟩ hfit hna).elim
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := fun heq => h0 (by simpa using heq)
      have hcomm :
          (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt st_bl.sp extHookStack ∗
            ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            A.live (sf.readReg64 .x0) size align ∗
            memRegion (sf.readReg64 .x0) size ∗ subFrame ∗ F) =
          (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt st_bl.sp extHookStack ∗
              A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size ∗ subFrame ∗ F)) := by
        sep_ac_rfl
      rw [hcomm]
      refine SepWPp.pure_elim fun hmod => ?_
      refine sepWPp_weaken_pre ?_
        (hok sf (sf.readReg64 .x0) hin_f hcs_f rfl hne0 hmod hfs_f hacp.2.1)
      rw [hsp, hsplit]
      dsimp +zetaDelta only [subFrame]
      exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_alloc_cond_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff size align : Nat}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsRustAllocSymCli)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : (st_bl.readReg64 .x0).toNat = size)
    (hx1 : (st_bl.readReg64 .x1).toNat = align)
    (_hpos : 0 < size)
    (hlay : LayoutOk size align)
    (hal : align ≤ 2 ^ 31 := by decide)
    (hpanicK : PanicK g s0 Qp)
    (hoomK : ∀ sf R', sf.status = .OutOfMemory →
      ¬ FitsEvents M lim st (rustAllocEvents size align) →
      OomPreserved st_bl sf →
      (sf.mem ⊨ memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
        (resStack - runFrame - extHookStack) ∗ F ∗ R') →
      (sf.mem ⊨ oom sf ∗ R'))
    (hnull : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      NullAllowed size align →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sf ∗ F) Q Qp oom)
    (hok : ∀ (sf : State) (buf : BitVec 64),
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.readReg64 .x0 = buf →
      buf ≠ 0#64 →
      buf.toNat % align = 0 →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (A.live buf size align ∗ memRegion buf size ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗ F) Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff) := by
      first | assumption | simp (config := { decide := true })
        [CryptoVerification.SignalSession.Cli.RunCompose.runPcPlaced, wp_norm, arm64_norm,
         LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F) Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hsplit := stackAt_split_sub (runFsp s0)
    (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64
  rw [hsplit]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - extHookStack)
  refine r1b_call_placed (size, align, st) (r1b_allocFs_placed_ok hh) hinv hpc hrun hal_bl hlr hpanicK
    (F := subFrame ∗ F) ?_ (hoom := ?_) (hnext := ?_)
  · dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    rw [hsp]
    conv => rhs; rw [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, ⟨hlay, hal⟩, hlr ▸ hlr_ls⟩
    dsimp +zetaDelta only [subFrame]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf R' hoom_s ho
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at ho
    rw [satisfies_pure_sepConj] at ho
    exact hoomK sf R' hoom_s ho.1.1 ho.1.2 (by simpa only [sepConj_assoc, subFrame] using ho.2)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp +zetaDelta only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => SepWPp.pure_elim fun hacp => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte]
      have heq0 : sf.readReg64 .x0 = 0#64 := by simpa using h0
      have hcomm :
          (A.pool lim st sf ∗ stackAt st_bl.sp extHookStack ∗
            ⌜NullAllowed size align⌝ ∗ subFrame ∗ F) =
          (⌜NullAllowed size align⌝ ∗
            (A.pool lim st sf ∗ stackAt st_bl.sp extHookStack ∗ subFrame ∗ F)) := by
        sep_ac_rfl
      rw [hcomm]
      refine SepWPp.pure_elim fun hna => ?_
      refine sepWPp_weaken_pre ?_ (hnull sf hin_f hcs_f hna heq0 hfs_f hacp.2.1)
      rw [hsp, hsplit]
      dsimp +zetaDelta only [subFrame]
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := fun heq => h0 (by simpa using heq)
      have hcomm :
          (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt st_bl.sp extHookStack ∗
            ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            A.live (sf.readReg64 .x0) size align ∗
            memRegion (sf.readReg64 .x0) size ∗ subFrame ∗ F) =
          (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt st_bl.sp extHookStack ∗
              A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size ∗ subFrame ∗ F)) := by
        sep_ac_rfl
      rw [hcomm]
      refine SepWPp.pure_elim fun hmod => ?_
      refine sepWPp_weaken_pre ?_
        (hok sf (sf.readReg64 .x0) hin_f hcs_f rfl hne0 hmod hfs_f hacp.2.1)
      rw [hsp, hsplit]
      dsimp +zetaDelta only [subFrame]
      exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_memcpy_ro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {g : RunCall} {s0 st_bl : State} {retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hinv : r1b_CodeOk st_bl.mem)
    (hro : ∀ {m : Memory} {R : SepProp}, r1b_CodeOk m → (m ⊨ R) → (m ⊨ (src ↦ᵣ bs) ∗ R))
    (hpc : st_bl.pc = lsρ lsMemcpySym)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = dst)
    (hx1 : st_bl.readReg64 .x1 = src)
    (hx2 : (st_bl.readReg64 .x2).toNat = bs.length)
    (hlen : bs.length ≤ 2 ^ 64)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      VmPreserved st_bl sf →
      sf.readReg64 .x0 = dst →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((dst ↦ₛ bs) ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion dst bs.length ∗ F) Q Qp oom := by
  refine r1b_sepWPp_with_ro_placed hinv hro ?_
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hmc_ok : subroutine_ok (runProgPlaced H) (lsρ lsMemcpySym)
      (withLsCodeRoLoaded lsmpl (withVmPreserved sessionMemcpyRegionROSpec)) :=
    subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem (prog := runProgPlaced H) (i := 579)
        hh.memcpyRO (by decide) (by decide) (by decide))
  refine r1b_call_placed (dst, src, bs) hmc_ok hinv hpc hrun hal_bl hlr hpanicK
    (F := F) ?_ (hnext := ?_)
  · change _ ⊢
      (⌜st_bl.readReg64 .x0 = dst ∧ st_bl.readReg64 .x1 = src ∧
          (st_bl.readReg64 .x2).toNat = bs.length ∧ bs.length ≤ 2 ^ 64⌝ ∗
        memRegion dst bs.length ∗ (src ↦ᵣ bs)) ∗ (F ∗ emp)
    simp only [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlen⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    change SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
      ((⌜VmPreserved st_bl sf⌝ ∗
        (⌜sf.readReg64 .x0 = dst ∧ sf.trace = st_bl.trace⌝ ∗
          (dst ↦ₛ bs) ∗ (src ↦ᵣ bs))) ∗ F) Q Qp oom
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hvm_f => SepWPp.pure_elim fun hp => ?_
    rcases hp with ⟨hr0, htr_f⟩
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
    refine sepWPp_weaken_pre (P' := (src ↦ᵣ bs) ∗ ((dst ↦ₛ bs) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    exact r1b_sepWPp_drop_left (hnext sf hin_f hcs_f hvm_f hr0 hfiles_f htr_f)

theorem r1b_call_memcpy_ro_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {g : RunCall} {s0 st_bl : State} {retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hinv : r1b_CodeOk st_bl.mem)
    (hro : ∀ {m : Memory} {R : SepProp}, r1b_CodeOk m → (m ⊨ R) → (m ⊨ (src ↦ᵣ bs) ∗ R))
    (hpc : st_bl.pc = lsρ lsMemcpySym)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = dst)
    (hx1 : st_bl.readReg64 .x1 = src)
    (hx2 : (st_bl.readReg64 .x2).toNat = bs.length)
    (hlen : bs.length ≤ 2 ^ 64)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.readReg64 .x0 = dst →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((dst ↦ₛ bs) ∗ A.pool lim st sf ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion dst bs.length ∗ A.pool lim st st_bl ∗ F) Q Qp oom :=
  r1b_call_memcpy_ro_placed hh hinv hro hpc hrun hsp hfp hvregs hsp0 hlr
    hx0 hx1 hx2 hlen hpanicK fun sf hin_f hcs_f hvm_f hr0 hfiles_f htr_f => by
      rw [← A.pool_of_vmPreserved hvm_f]
      exact hnext sf hin_f hcs_f hr0 hfiles_f htr_f

theorem r1b_call_memcpy_region_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsMemcpySym)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = dst)
    (hx1 : st_bl.readReg64 .x1 = src)
    (hx2 : (st_bl.readReg64 .x2).toNat = bs.length)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      VmPreserved st_bl sf →
      sf.readReg64 .x0 = dst →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ F) Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hsplit := stackAt_split_sub (runFsp s0)
    (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64
  rw [hsplit]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - extHookStack)
  refine r1b_call_placed (dst, src, bs) (r1b_memcpyRegionFs_placed_ok hh) hinv hpc hrun hal_bl hlr hpanicK
    (F := subFrame ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2⟩
    dsimp +zetaDelta only [subFrame]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f =>
      SepWPp.pure_elim fun hvm_f =>
      SepWPp.pure_elim fun hp => ?_
    rcases hp with ⟨hr0, htr_f⟩
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    refine sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hvm_f hr0 hfs_f htr_f)
    rw [hsp, hsplit]
    dsimp +zetaDelta only [subFrame]
    exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_memcpy_region_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsMemcpySym)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = dst)
    (hx1 : st_bl.readReg64 .x1 = src)
    (hx2 : (st_bl.readReg64 .x2).toNat = bs.length)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.readReg64 .x0 = dst →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sf ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F) Q Qp oom :=
  r1b_call_memcpy_region_placed hh hbnd hinv hpc hrun hsp hfp hvregs hsp0 hlr
    hx0 hx1 hx2 hpanicK fun sf hin_f hcs_f hvm_f hr0 hfs_f htr_f => by
      rw [← A.pool_of_vmPreserved hvm_f]
      exact hnext sf hin_f hcs_f hr0 hfs_f htr_f

theorem r1b_call_tryAlloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {out new align stride : BitVec 64}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 588)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = out)
    (hx1 : st_bl.readReg64 .x1 = new)
    (hx2 : st_bl.readReg64 .x2 = align)
    (hx3 : st_bl.readReg64 .x3 = stride)
    (hnew : 0 < new.toNat)
    (hstr : 0 < stride.toNat)
    (hlay : LayoutOk (new.toNat * stride.toNat) align.toNat)
    (hal : align.toNat ≤ 2 ^ 31 := by decide)
    (hfit : FitsEnv M lim st (TryAllocateInEnv ⟨out, new, align, stride⟩))
    (hpanicK : PanicK g s0 Qp)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (buf : BitVec 64),
      TryAllocateInEnv ⟨out, new, align, stride⟩ evs →
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      buf ≠ 0#64 →
      buf.toNat % align.toNat = 0 →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ new) ∗ ((out + 16#64) ↦₆₄ buf) ∗
          A.live buf (new.toNat * stride.toNat) align.toNat ∗
          memRegion buf (new.toNat * stride.toNat) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion out 24 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (⟨out, new, align, stride⟩, st)
    (runTryAllocateIn3_placed_ok hh (resStack - runFrame) hbnd.tryAlloc hbnd.sub63)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [Spec.keepsFs, tryAllocateInRustSpecOf, tryAllocateInSpecOf]
    simp only [hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnew, hstr, ⟨hlay, hal⟩, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.keepsFs, tryAllocateInRustSpecOf, tryAllocateInSpecOf]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun buf => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hcomm :
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ new) ∗ ((out + 16#64) ↦₆₄ buf) ∗
          ⌜buf ≠ 0#64 ∧ buf.toNat % align.toNat = 0 ∧ sf.trace = st_bl.trace ∧
            TryAllocateInEnv ⟨out, new, align, stride⟩ evs⌝ ∗
          A.live buf (new.toNat * stride.toNat) align.toNat ∗
          memRegion buf (new.toNat * stride.toNat) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt st_bl.sp (resStack - runFrame) ∗ F) =
        (⌜buf ≠ 0#64 ∧ buf.toNat % align.toNat = 0 ∧ sf.trace = st_bl.trace ∧
            TryAllocateInEnv ⟨out, new, align, stride⟩ evs⌝ ∗
          ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ new) ∗ ((out + 16#64) ↦₆₄ buf) ∗
            A.live buf (new.toNat * stride.toNat) align.toNat ∗
            memRegion buf (new.toNat * stride.toNat) ∗
            stackAt st_bl.sp (resStack - runFrame) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ F)) := by
      sep_ac_rfl
    rw [hcomm]
    refine SepWPp.pure_elim fun hp => ?_
    rcases hp with ⟨hne, hmod, htr_f, hevs⟩
    rw [hsp]
    exact hok sf evs buf hevs hin_f hcs_f hne hmod hfs_f htr_f

theorem r1b_call_path_ro_placed [LibsignalPlacement] {M : AllocCostModel}
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
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (pCap pPtr : BitVec 64),
      PathEnv dir name evs →
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
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
  refine r1b_call_placed
    (x := ({ dirA := dirPtr, dir := dir, dirRo := false,
             nameA := nameA, name := name, nameRo := true, ret := ret }, st))
    (path_placed_ok hh hbnd.path) hinv hpc hrun hal_bl hlr hpanicK
    (F := r1b_ownedRest A.repAlloc dirCap dirPtr dir.length ∗ F)
    ?_ (hnext := ?_)
  · dsimp only [pathSpecPlaced, withLsCodeRoLoaded, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hdir_lt, hname_lt, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [pathSpecPlaced, withLsCodeRoLoaded, bytesAt]
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
      simpa only [List.append_assoc] using hnext sf evs pCap pPtr hevs hin_f hcs_f hfiles_f htr_f

theorem r1b_call_readFile_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {pathCap pathPtr ret : BitVec 64} {path : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsReadFileSym) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = pathPtr) (hx1 : (st_bl.readReg64 .x1).toNat = path.length)
    (hx8 : st_bl.readReg64 .x8 = ret) (hlen : path.length < 2 ^ 32)
    (hok_p : cliWrOk path)
    (hfit : FitsEnv M lim st (cEnvs.readFile st_bl.fs.files path))
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (w1 w2 : BitVec 64),
      cEnvs.readFile st_bl.fs.files path evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      (cliIo.rd st_bl.fs.files path = .error () ∧
        sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace) →
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
  · dsimp only [readFileSpecPlaced]
    simp only [hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx8, hlen, hok_p, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [readFileSpecPlaced]
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
        exact herr sf evs w1 w2 hevs hin_f hcs_f hout
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
        exact hok sf evs rCap rPtr bs hevs hin_f hcs_f hrd.symm hfiles_f htr_f

theorem r1b_call_bundleRead_ro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret dirCap dirPtr nameA : BitVec 64} {dir name : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlaced A lim cEnvs H B σ)
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
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      cEnvs.bundleRead st_bl.fs.files dir name evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      (cliIo.rd st_bl.fs.files (dir ++ [0x2f#8] ++ name) = .error () ∧
        sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace) →
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
  refine r1b_call_placed
    (x := ({ ret := ret, dirA := dirPtr, dir := dir, dirRo := false,
             nameA := nameA, name := name, nameRo := true }, st))
    (hc.bundleRead hbnd.bundleRead) hinv hpc hrun hal_bl hlr hpanicK
    (F := r1b_ownedRest A.repAlloc dirCap dirPtr dir.length ∗ F)
    ?_ (hnext := ?_)
  · dsimp only [bundleReadSpecPlaced, withLsCodeRoLoaded, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hdir_lt, hname_lt, hok_p, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [bundleReadSpecPlaced, withLsCodeRoLoaded, bytesAt]
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
        · exact r1b_sepWPp_drop_left (herr sf evs eCap ePtr eBs hevs hin_f hcs_f hout)
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
          (hok sf evs rCap rPtr bs hevs hin_f hcs_f hrd.symm hfiles_f htr_f)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
