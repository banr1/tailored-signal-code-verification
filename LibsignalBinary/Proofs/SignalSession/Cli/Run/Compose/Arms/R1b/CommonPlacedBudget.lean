/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout

/-!
# Budget-Threaded Shared Call and Cleanup Helpers for Arm `R1b`

Budget-threaded `.keepsFs` allocator and `memcpy` callee helpers, `SepWPp` call combinator
`r1b_call_placed`, `ownedBytes` deallocation, and `SignalProtocolError` drop helpers on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (NoFsEv withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack lsMemcpySym withStack)
open CryptoVerification.RustHeap (LayoutOk allocFailedIn)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.BundleRead.Helpers (stackAt_split_sub)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (ownedBytes_pure ownedBytes_to_dealloc)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InRunPlaced PanicK RunNeeds RunSem r1b_CodeOk r1b_StackBounds r1b_lscro_of_rocl
   r1b_spAligned_of_fsp runFsp runPanicProp runPcPlaced runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_panicAt_of_cliPanic satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.alloc_rocl AllocContractsFsPlaced.dealloc_rocl
   AllocContractsFsPlaced.session_memcpy_region_rocl AllocContractsFsPlaced.session_memcpy_rocl
   AllocContractsFsPlaced.shim2_rocl AllocContractsFsPlaced.shim_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock dropSpeOwnedSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget (dropSpeOwnedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack)

theorem r1b_shimFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec extHookStack).keepsFs) :=
  r1b_lscro_of_rocl
    (AllocContractsFsPlaced.shim_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_shim2Fs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl session2ShimBudgetSpecX.keepsFs) :=
  r1b_lscro_of_rocl
    (AllocContractsFsPlaced.shim2_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_allocFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack M A lim false extHookStack).keepsFs) :=
  r1b_lscro_of_rocl
    (AllocContractsFsPlaced.alloc_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_deallocFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) :=
  r1b_lscro_of_rocl
    (AllocContractsFsPlaced.dealloc_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_memcpyFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (runProgPlaced H) (lsρ lsMemcpySym)
      (withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec extHookStack).keepsFs) :=
  r1b_lscro_of_rocl
    (AllocContractsFsPlaced.session_memcpy_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_memcpyRegionFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (runProgPlaced H) (lsρ lsMemcpySym)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec extHookStack).keepsFs) :=
  r1b_lscro_of_rocl
    (AllocContractsFsPlaced.session_memcpy_region_rocl (prog := runProgPlaced H) (i := 579)
      hh.allocFs)

theorem r1b_panic_handle_error_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    (runProgPlaced H).externAt? (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Rust.panicked :=
  ls_panicAt_of_cliPanic (prog := runProgPlaced H) (i := 579) hh.panics
    (sym := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")

theorem r1b_files_eq_of_trace_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H)
    {s sf : State} (hsteps : Steps (runProgPlaced H) s sf)
    (htr : sf.trace = s.trace) :
    sf.fs.files = s.fs.files :=
  (hh.fs (runProgPlaced H) 579).files_eq hsteps
    (by simp [htr] : sf.trace = s.trace ++ []) NoFsEv.nil

theorem r1b_stackBounds_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {sEnvs : RunSlotEnvs}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres63 : resStack ≤ 2 ^ 63) :
    r1b_StackBounds B resStack := by
  have hb := runNeed_bounds_placed hres hres63
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem r1b_call_placed [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {callee ret_pc ret : BitVec 64} {spec : Spec α} {g : RunCall} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok (runProgPlaced H) callee (withLsCodeRoLoaded lsmpl spec))
    (hinv : r1b_CodeOk s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpanicK : PanicK g s0 Qp)
    (hP : P ⊢ spec.pre x s ∗ (F ∗ emp))
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
      runPanicProp g s0 sf := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      Steps (runProgPlaced H) s sf →
      r1b_CodeOk sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) ret s P Q Qp oom := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    have h1 := Satisfies.mono (sepConj_mono_left hP) hm
    simpa only [sepConj_emp, sepConj_assoc] using h1
  have hpre :
      s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) :=
    satisfies_lscro_pre hinv hm_pre
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanicK sm _ (hpanic sm (F ∗ R) hpan hpost)⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

theorem r1b_handle_error_panic_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {ret : BitVec 64} {g : RunCall} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hpc : s.pc = lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    (hrun : s.status = .Running)
    (hpanicK : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (runProgPlaced H) ret s P Q Qp oom := by
  intro R hm _
  let s1 := Rust.panicked s
  have hstep : Step (runProgPlaced H) s s1 :=
    Step.extern hrun (hpc ▸ r1b_panic_handle_error_placed hh) (Memory.KeepsFrozen.refl s.mem) rfl
  exact ⟨s1, Steps.step hstep (Steps.refl s1), Or.inr (Or.inl ⟨rfl, P, hm,
    hpanicK s1 P (Or.inr hfail)⟩)⟩

theorem r1b_call_dealloc_ownedBytes_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {s0 st_bl : State}
    {resStack retOff : Nat}
    {cap ptr len : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsRustDeallocSymCli)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : st_bl.readReg64 .x1 = cap)
    (hx2 : st_bl.readReg64 .x2 = 1#64)
    (hcap : cap ≠ 0#64)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sf ∗ F)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff) := by
      first | assumption | simp (config := { decide := true })
        [_root_.CryptoVerification.SignalSession.Cli.RunCompose.runPcPlaced, wp_norm, arm64_norm,
         _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (ownedBytes A.repAlloc cap ptr len bs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  rw [ownedBytes_pure A.repAlloc cap ptr len bs, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, _, hlt_cap, _⟩ => ?_
  set fsp := runFsp s0
  refine r1b_call_placed (ptr, cap.toNat, 1, st) (r1b_deallocFs_placed_ok hh)
    hinv hpc hrun hal_bl hlr hpanicK
    (F := memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
      (resStack - runFrame - extHookStack) ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    have hlay : LayoutOk cap.toNat 1 :=
      ⟨Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq (by simpa using h0)),
        ⟨0, rfl⟩, by omega⟩
    have hpure : st_bl.readReg64 .x0 = ptr ∧ (st_bl.readReg64 .x1).toNat = cap.toNat ∧
        (st_bl.readReg64 .x2).toNat = 1 ∧ RustLayoutOk cap.toNat 1 ∧
        LsRetAddr624 (st_bl.readReg64 .lr) := by
      exact ⟨hx0, by rw [hx1], by rw [hx2]; decide, ⟨hlay, by decide⟩, hlr ▸ hlr_ls⟩
    rw [hsp]
    change ownedBytes A.repAlloc cap ptr len bs ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F ⊢ _
    rw [stackAt_split_sub fsp (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64]
    refine Entails.trans (sepConj_mono_left (ownedBytes_to_dealloc A.repAlloc hcap)) ?_
    change (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
      ((memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗ stackAt fsp extHookStack) ∗
        A.pool lim st st_bl ∗ F) ⊢ _
    conv => rhs; rw [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hpure
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    refine sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfs_f htr_f)
    rw [hsp, stackAt_split_sub fsp (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64]
    exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_dropSpeOwned_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {s0 st_bl : State}
    {resStack retOff : Nat}
    {a : BitVec 64} {k : SpeOwned} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 553)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = a)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion a 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff) := by
      first | assumption | simp (config := { decide := true }) [runPcPlaced, wp_norm, arm64_norm, lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (speOwnedAt A.repAlloc a k ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (⟨a, k⟩, st) (hdrop (resStack - runFrame) hbnd.dropSpe hbnd.sub64)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [dropSpeOwnedSpecPlaced, dropSpeOwnedSpec]
    rw [hsp]
    conv => rhs; rw [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hlr ▸ hlr_ls⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [dropSpeOwnedSpecPlaced, dropSpeOwnedSpec]
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr_f, hevs⟩ => ?_
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
    refine sepWPp_weaken_pre ?_ (hnext sf evs hevs hin_f hcs_f hfiles_f htr_f)
    rw [hsp]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
