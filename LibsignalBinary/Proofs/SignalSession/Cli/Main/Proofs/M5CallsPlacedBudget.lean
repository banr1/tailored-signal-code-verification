/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common

/-!
# Budget-Threaded `.keepsFs` Call Wrappers for `main` Hop M5 (Block `617`)

Budget-threaded `SepWPp` call wrappers on Block `617` under `RustCliAllocBudget M`, synchronizing
`A.pool` across the allocator shim, `__rust_alloc`, writable and read-only `memcpy`,
`do_reserve_and_handle`, `write_file`, and `__rust_dealloc`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall extHookStack memcpyName reserveCap sessionMemcpyRegionSpec sessionShimSpec
   withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (LayoutOk vecU8At)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsWriteFileSym)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (InMainPlaced IoModel LsCodeInv WriteFileGhost mPcPlaced mainFrameSize main_call_rocl)
open CryptoVerification.SignalSession.Cli.Path.Helpers (stackAt_split_ge)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents NullAllowed
   OomPreserved RustCliAllocBudget RustLayoutOk VmPreserved not_nullAllowed_of_fitsAllocEvents
   rustAllocEvents rustDeallocEvents rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Heap.SpecBudget (WriteFileEnv withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced mainIoBoundedPlaced_iff_mainIoPlaced main_writeFile_of_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
  (main_alloc_fs_placed_ok main_dealloc_fs_placed_ok main_reserve1_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlacedBudget
  (main_writeFile_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget (MainMemcpyROFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced writeFileSpecPlaced)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (DoReserveEnv doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack)

namespace LoopDrop

/-- Call `__rust_no_alloc_shim_is_unstable_v2` with full sub-stack
`stackAt fsp (stk - mainFrameSize)`, exposing `VmPreserved s sm` to the continuation. -/
theorem m5_call_shim_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk retOff : Nat}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ lsRustNoAllocShimSymCli)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hP : P ⊢ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      VmPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := ())
    (AllocFsSitesPlacedBudget.AllocContractsFsPlaced.shim_rocl hA (prog := lsProg_617 H) (i := 617)
      extHookStack (by decide) (by decide))
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec, sessionShimSpec]
    rw [emp_sepConj, hsp]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec, sessionShimSpec]
    rw [hsp]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun hvm => ?_
    refine SepWPp.pure_elim fun htr => ?_
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hvm hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by sep_ac_rfl)

theorem m5_call_shim_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {stk retOff : Nat}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ lsRustNoAllocShimSymCli)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hP : P ⊢ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      VmPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  refine m5_call_shim_placed hA hstk hstk64 hpc hrun hinv hsp hfp hvregs hs0_align hlr
    (F := A.pool lim st s ∗ F)
    (Entails.trans hP (Entails.of_eq (by sep_ac_rfl)))
    fun sm hbase hvm hfs htr hcsm => ?_
  refine SepWPp.weaken_pre ?_ (hnext sm hbase hvm hfs htr hcsm)
  rw [← A.pool_transport lim st s sm hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Call `__rust_alloc(size, 1)` under `FitsEvents M lim st (rustAllocEvents size 1)` with full
sub-stack `stackAt fsp (stk - mainFrameSize)`, ruling out both `.OutOfMemory` and null return and
advancing `A.pool lim st s` to `A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sm`. -/
theorem m5_call_alloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {stk size retOff : Nat}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hlay : LayoutOk size 1)
    (hfit : FitsEvents M lim st (rustAllocEvents size 1))
    (hpc : s.pc = lsρ lsRustAllocSymCli)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : (s.readReg64 .x0).toNat = size)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hP : P ⊢ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (halloc_next : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.readReg64 .x0 ≠ 0#64 →
      AllocCallPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗ F)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (mPcPlaced retOff) := by
      dsimp only [mPcPlaced]; simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hrlay : RustLayoutOk size 1 := ⟨hlay, by decide⟩
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (size, 1, st)) (main_alloc_fs_placed_ok hA)
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hoom := ?_) (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hrlay, by rwa [hlr]⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf R' _ ho
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at ho
    rw [satisfies_pure_sepConj] at ho
    exact (ho.1.1 hfit).elim
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    rw [hsp]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun hacp => ?_
    by_cases h0 : sm.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte, sepConj_assoc]
      have hpure :
          A.pool lim st sm ∗ stackAt fsp extHookStack ∗ ⌜NullAllowed size 1⌝ ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - extHookStack) ∗ F =
          ⌜NullAllowed size 1⌝ ∗
            (A.pool lim st sm ∗ stackAt fsp extHookStack ∗
              memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                (stk - mainFrameSize - extHookStack) ∗ F) := by
        sep_ac_rfl
      dsimp only [fsp] at hpure
      rw [hpure]
      refine SepWPp.pure_elim fun hna => ?_
      exact (not_nullAllowed_of_fitsAllocEvents hrlay hfit hna).elim
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hpure :
          A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sm ∗ stackAt fsp extHookStack ∗
            ⌜(sm.readReg64 .x0).toNat % 1 = 0⌝ ∗ A.live (sm.readReg64 .x0) size 1 ∗
            memRegion (sm.readReg64 .x0) size ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - extHookStack) ∗ F =
          ⌜(sm.readReg64 .x0).toNat % 1 = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sm ∗
              stackAt fsp (stk - mainFrameSize) ∗
              A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗ F) := by
        rw [hsplit]; sep_ac_rfl
      dsimp only [fsp] at hpure
      rw [hpure]
      refine SepWPp.pure_elim fun _ => ?_
      exact halloc_next sm hbase h0 hacp hfs hacp.2.1 hcsm

/-- Raw conditional-OOM `__rust_alloc(size, 1)` wrapper exposing both `.OutOfMemory` (`hoom`) and
`NullAllowed size 1` (`hnull_next`) branches without requiring `FitsEvents` up front. -/
theorem m5_call_alloc_raw_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {stk size retOff : Nat}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hlay : LayoutOk size 1)
    (hpc : s.pc = lsρ lsRustAllocSymCli)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : (s.readReg64 .x0).toNat = size)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hP : P ⊢ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      ¬ FitsEvents M lim st (rustAllocEvents size 1) →
      OomPreserved s sf →
      (sf.mem ⊨ (memRegion
        ((s0.sp - BitVec.ofNat 64 mainFrameSize) - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - extHookStack) ∗ F) ∗ R') →
      sf.mem ⊨ oom sf ∗ R')
    (hnull_next : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.readReg64 .x0 = 0#64 →
      NullAllowed size 1 →
      AllocCallPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom)
    (halloc_next : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.readReg64 .x0 ≠ 0#64 →
      AllocCallPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗ F)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (mPcPlaced retOff) := by
      dsimp only [mPcPlaced]; simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hrlay : RustLayoutOk size 1 := ⟨hlay, by decide⟩
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (size, 1, st)) (main_alloc_fs_placed_ok hA)
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hoom := ?_) (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hrlay, by rwa [hlr]⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf R' hst ho
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at ho
    rw [satisfies_pure_sepConj] at ho
    exact hoom sf R' hst ho.1.1 ho.1.2 ho.2
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    rw [hsp]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun hacp => ?_
    by_cases h0 : sm.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte, sepConj_assoc]
      have hpure :
          A.pool lim st sm ∗ stackAt fsp extHookStack ∗ ⌜NullAllowed size 1⌝ ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - extHookStack) ∗ F =
          ⌜NullAllowed size 1⌝ ∗
            (A.pool lim st sm ∗ stackAt fsp (stk - mainFrameSize) ∗ F) := by
        rw [hsplit]; sep_ac_rfl
      dsimp only [fsp] at hpure
      rw [hpure]
      refine SepWPp.pure_elim fun hna => ?_
      exact hnull_next sm hbase h0 hna hacp hfs hacp.2.1 hcsm
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hpure :
          A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sm ∗ stackAt fsp extHookStack ∗
            ⌜(sm.readReg64 .x0).toNat % 1 = 0⌝ ∗ A.live (sm.readReg64 .x0) size 1 ∗
            memRegion (sm.readReg64 .x0) size ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - extHookStack) ∗ F =
          ⌜(sm.readReg64 .x0).toNat % 1 = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sm ∗
              stackAt fsp (stk - mainFrameSize) ∗
              A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗ F) := by
        rw [hsplit]; sep_ac_rfl
      dsimp only [fsp] at hpure
      rw [hpure]
      refine SepWPp.pure_elim fun _ => ?_
      exact halloc_next sm hbase h0 hacp hfs hacp.2.1 hcsm

/-- Call `memcpy(dst, src, bs.length)` with writable `(src ↦ₛ bs)`, `.keepsFs`, and
`VmPreserved s sm`. -/
theorem m5_call_memcpy_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {stk retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ memcpyName)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      VmPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (dst, src, bs))
    (AllocFsSitesPlacedBudget.AllocContractsFsPlaced.session_memcpy_region_rocl hA
      (prog := lsProg_617 H) (i := 617) extHookStack (by decide) (by decide))
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec]
    rw [hsp]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun hvm => ?_
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hvm hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by sep_ac_rfl)

theorem m5_call_memcpy_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {stk retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ memcpyName)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      VmPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  refine m5_call_memcpy_placed hA hstk hstk64 hpc hrun hinv hsp hfp hvregs hs0_align hlr
    hx0 hx1 hx2 (F := A.pool lim st s ∗ F)
    (Entails.trans hP (Entails.of_eq (by sep_ac_rfl)))
    fun sm hbase hvm hfs htr hcsm => ?_
  refine SepWPp.weaken_pre ?_ (hnext sm hbase hvm hfs htr hcsm)
  rw [← A.pool_transport lim st s sm hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Call `memcpy(dst, src, bs.length)` with read-only `(src ↦ᵣ bs)` (`MainMemcpyROFsPlaced`) at
`M+0x894`, exposing `VmPreserved s sm`. -/
theorem m5_call_memcpy_ro_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {stk retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : MainMemcpyROFsPlaced H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ memcpyName)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hlen : bs.length ≤ 2 ^ 64)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      VmPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (dst, src, bs)) hro
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, withStack, withVmPreserved, sessionMemcpyRegionROSpec]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlen⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, withStack, withVmPreserved, sessionMemcpyRegionROSpec]
    rw [hsp]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun hvm => ?_
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hvm hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by sep_ac_rfl)

theorem m5_call_memcpy_ro_pool_placed [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {stk retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : MainMemcpyROFsPlaced H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ memcpyName)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hlen : bs.length ≤ 2 ^ 64)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      VmPreserved s sm →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ A.pool lim st sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  refine m5_call_memcpy_ro_placed hro hstk hstk64 hpc hrun hinv hsp hfp hvregs hs0_align hlr
    hx0 hx1 hx2 hlen (F := A.pool lim st s ∗ F)
    (Entails.trans hP (Entails.of_eq (by sep_ac_rfl)))
    fun sm hbase hvm hfs htr hcsm => ?_
  refine SepWPp.weaken_pre ?_ (hnext sm hbase hvm hfs htr hcsm)
  rw [← A.pool_transport lim st s sm hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Call `do_reserve_and_handle` (`hc.reserve1`, `.keepsFs` at `lsmpl.base 561`) under
`FitsEnv M lim st (DoReserveEnv ...)`, advancing `A.pool lim st s` to
`A.pool lim (M.stepEvents (doReserveEvents ...) st) sm`. -/
theorem m5_call_reserve1_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack stk additional retOff : Nat}
    {v curCap curPtr : BitVec 64} {curBs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs additional)))
    (hpc : s.pc = lsmpl.base 561)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P ⊢ vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      InMainPlaced CodeOk s0 sm retOff →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional))
          newPtr curBs ∗
          A.pool lim
            (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) st)
            sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := resStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (DoReserveCall.mk v curCap curPtr curBs additional, st))
    (main_reserve1_placed_ok hc) hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - resStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, doReserveSpecOf]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, doReserveSpecOf]
    rw [hsp]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun htr => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm newPtr hbase hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by sep_ac_rfl)

/-- `{StdinEnv ReadEnv}`-parametric `MainIoOfPlaced` call wrapper for `write_file(pathA, path, buf, bs)`
under `FitsEnv M lim st (WriteFileEnv path.length)`, advancing `A.pool lim st s` to
`A.pool lim (M.stepEvents evs st) sm` for some `WriteFileEnv path.length evs`. -/
theorem m5_call_write_file_of_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {hookStack stk retOff : Nat}
    {pathA buf : BitVec 64} {path bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv)
    (hstk : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ lsWriteFileSym)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = pathA)
    (hx1 : (s.readReg64 .x1).toNat = path.length)
    (hx2 : s.readReg64 .x2 = buf)
    (hx3 : (s.readReg64 .x3).toNat = bs.length)
    (hlen : path.length < 2 ^ 32)
    (hok : io.pathOk path)
    (hfit : FitsEnv M lim st (WriteFileEnv path.length))
    (hP : P ⊢ (pathA ↦ₛ path) ∗ (buf ↦ₛ bs) ∗ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      InMainPlaced CodeOk s0 sm retOff →
      WriteFileEnv path.length evs →
      (match io.wr s.fs.files path bs with
       | some F' => sm.readReg64 .x0 = 0#64 ∧ sm.fs.files = F'
       | none => sm.readReg64 .x0 = 1#64 ∧ sm.fs.files = s.fs.files) →
      s.trace <+: sm.trace →
      ProcessOutcome.traceStreamBytes .stdout sm.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((pathA ↦ₛ path) ∗ (buf ↦ₛ bs) ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := hookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (WriteFileGhost.mk pathA path buf bs, st))
    (main_writeFile_of_placed_ok hio) hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - hookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [writeFileSpecPlaced]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hlen, hok, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [writeFileSpecPlaced]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => ?_
    refine SepWPp.pure_elim fun ⟨hevs, hwr, htr, hout⟩ => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm evs hbase hevs hwr htr hout hcsm)
    rw [hsplit]
    exact Entails.of_eq (by sep_ac_rfl)

abbrev m5_call_write_file_of_pool_placed [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :=
  @m5_call_write_file_of_placed _ CodeOk _

/-- Call `write_file(pathA, path, buf, bs)` (`hio.writeFile`) under
`FitsEnv M lim st (WriteFileEnv path.length)`, advancing `A.pool lim st s` to
`A.pool lim (M.stepEvents evs st) sm` for some `WriteFileEnv path.length evs`. -/
theorem m5_call_write_file_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {io : IoModel}
    {hookStack stk retOff : Nat}
    {pathA buf : BitVec 64} {path bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hio : MainIoPlaced A lim H io hookStack)
    (hstk : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ lsWriteFileSym)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = pathA)
    (hx1 : (s.readReg64 .x1).toNat = path.length)
    (hx2 : s.readReg64 .x2 = buf)
    (hx3 : (s.readReg64 .x3).toNat = bs.length)
    (hlen : path.length < 2 ^ 32)
    (hok : io.pathOk path)
    (hfit : FitsEnv M lim st (WriteFileEnv path.length))
    (hP : P ⊢ (pathA ↦ₛ path) ∗ (buf ↦ₛ bs) ∗ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      InMainPlaced CodeOk s0 sm retOff →
      WriteFileEnv path.length evs →
      (match io.wr s.fs.files path bs with
       | some F' => sm.readReg64 .x0 = 0#64 ∧ sm.fs.files = F'
       | none => sm.readReg64 .x0 = 1#64 ∧ sm.fs.files = s.fs.files) →
      s.trace <+: sm.trace →
      ProcessOutcome.traceStreamBytes .stdout sm.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((pathA ↦ₛ path) ∗ (buf ↦ₛ bs) ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom :=
  m5_call_write_file_of_placed
    ((mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack).mpr hio)
    hstk hstk64 hpc hrun hinv hsp hfp hvregs hs0_align hlr hx0 hx1 hx2 hx3
    hlen hok hfit hP hnext

abbrev m5_call_write_file_pool_placed [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk] :=
  @m5_call_write_file_placed _ CodeOk _

/-- Call `__rust_dealloc(ptr, size, align)` (`hA.dealloc`, `.keepsFs`), advancing `A.pool lim st s`
to `A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sm`. -/
theorem m5_call_dealloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {stk size align retOff : Nat}
    {ptr : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hlay : LayoutOk size align)
    (hal_le : align ≤ 2 ^ 31 := by decide)
    (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hP : P ⊢ A.live ptr size align ∗ memRegion ptr size ∗ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (mPcPlaced retOff) := by
      dsimp only [mPcPlaced]; simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hrlay : RustLayoutOk size align := ⟨hlay, hal_le⟩
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (ptr, size, align, st)) (main_dealloc_fs_placed_ok hA)
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hrlay, by rwa [hlr]⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [hsp]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun htr => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by sep_ac_rfl)

end LoopDrop

export LoopDrop
  (m5_call_shim_placed m5_call_shim_pool_placed
   m5_call_alloc_placed m5_call_alloc_raw_placed
   m5_call_memcpy_placed m5_call_memcpy_pool_placed
   m5_call_memcpy_ro_placed m5_call_memcpy_ro_pool_placed
   m5_call_reserve1_placed
   m5_call_write_file_of_placed m5_call_write_file_of_pool_placed
   m5_call_write_file_placed m5_call_write_file_pool_placed
   m5_call_dealloc_placed)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5CallsPlacedBudget
