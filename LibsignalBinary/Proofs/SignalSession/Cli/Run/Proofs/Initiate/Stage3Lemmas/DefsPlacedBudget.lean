/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.Hoare.Safety

/-!
# Budget-Threaded Relocatable Stage 3 Call Combinators and Memory Helpers

Provides `RustCliAllocBudget M` and `VmPreserved` Stage 3 stepping, `withLsCodeRoLoaded` call,
`__rust_alloc` / `__rust_dealloc`, shim, and `memcpy` combinators on `initProgPlaced`, while
re-exporting allocator-free stack-split helpers from `Stage3Lemmas/Defs` and `DefsPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement ls_externAt?_of_mem ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (lsProg_521)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives kemEncapsHook)
open CryptoVerification.E2E.Pqxdh.Initiator
  (initiatorModelPrims kemEncapsHook_ok_initiatorModelPrims kyberEncapsStubSpec)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded NoFsEv TraceFsSound subroutine_ok_withLsCodeRoLoaded_of_plain
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName session2MemcpySpecX session2ShimSpecX sessionMemcpyRegionSpec
   sessionShimSpec withStack)
open CryptoVerification.RustHeap (allocFailedEvent allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InInitiatePlaced initPcPlaced initProgPlaced lsKemEncapsSym satisfies_withLsCodeRoLoaded_pre
   transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
  (lay32 lay192 lay1568 lsAllocErrorSymS3 lsRawVecHandleErrorSymS3 sepWPp_conseq_oom
   sepWPp_pure_elim_oom)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents NullAllowed OomPreserved
   RustCliAllocBudget RustLayoutOk VmPreserved not_nullAllowed_of_fitsAllocEvents rustAllocEvents
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (perm_writeBytes_norm rustCliAllocBudgetSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## `RustLayoutOk` witnesses for Stage 3 heap sizes -/

theorem rustLay32 : RustLayoutOk 32 1 := ⟨lay32, by decide⟩

theorem rustLay192 : RustLayoutOk 192 1 := ⟨lay192, by decide⟩

theorem rustLay1568 : RustLayoutOk 1568 1 := ⟨lay1568, by decide⟩

theorem rustLay1569 : RustLayoutOk 1569 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩

/-! ## Relative call and hook targets on `initProgPlaced` -/

theorem shim_ok_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withVmPreserved session2ShimSpecX)) := by
  have h := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (hh.alloc.shim extHookStack (by decide) (by decide))
  refine subroutine_ok_mono h (fun _ _ _ hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · dsimp only [withLsCodeRoLoaded, withStack, sessionShimBudgetSpec,
      sessionShimSpec, withVmPreserved, session2ShimSpecX] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  · dsimp only [withLsCodeRoLoaded, withStack, sessionShimBudgetSpec,
      sessionShimSpec, withVmPreserved, session2ShimSpecX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem shim_plain_ok_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl session2ShimSpecX) := by
  refine subroutine_ok_mono (shim_ok_at_init_placed hh) (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeRoLoaded, withVmPreserved] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

theorem alloc_ok_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.alloc

theorem dealloc_ok_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.dealloc

theorem memcpy_ok_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved session2MemcpySpecX)) := by
  have h := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (hh.alloc.session_memcpy_region extHookStack (by decide) (by decide))
  refine subroutine_ok_mono h (fun _ _ _ hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, withVmPreserved, session2MemcpySpecX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, withVmPreserved, session2MemcpySpecX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem memcpy_plain_ok_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl session2MemcpySpecX) := by
  refine subroutine_ok_mono (memcpy_ok_at_init_placed hh) (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeRoLoaded, withVmPreserved] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

private theorem kemEncapsHook_vmPreserved
    (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (s : State) :
    VmPreserved s (kemEncapsHook encaps s) := by
  unfold kemEncapsHook returnToLinkRegister
  dsimp only
  refine ⟨⟨by cases s; rfl, by cases s; rfl, by cases s; rfl⟩, by cases s; rfl, fun a => ?_,
    fun _ _ _ => by cases s; rfl⟩
  cases s
  exact (congrFun (perm_writeBytes_norm _ _ _) a).trans (congrFun (perm_writeBytes_norm _ _ _) a)

theorem kyberEncaps_ok_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsKemEncapsSym)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (kyberEncapsStubSpec (initiatorModelPrims X ⟨W.C, W.Q⟩)))) := by
  have hsat0 : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsKemEncapsSym
      (kyberEncapsStubSpec (initiatorModelPrims X ⟨W.C, W.Q⟩)) :=
    ⟨kemEncapsHook W.Q.encaps, hh.kemEncaps,
      kemEncapsHook_ok_initiatorModelPrims X ⟨W.C, W.Q⟩⟩
  have hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsKemEncapsSym
      (withVmPreserved (kyberEncapsStubSpec (initiatorModelPrims X ⟨W.C, W.Q⟩))) :=
    hookSat_withVmPreserved hsat0 fun f hf s => by
      have hfeq : f = kemEncapsHook W.Q.encaps := Option.some.inj (hf.symm.trans hh.kemEncaps)
      rw [hfeq]
      exact kemEncapsHook_vmPreserved W.Q.encaps s
  have hraw : subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsKemEncapsSym)
      (withVmPreserved (kyberEncapsStubSpec (initiatorModelPrims X ⟨W.C, W.Q⟩))) := by
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    exact ls_hook_ok_ultra_of_mem hsat
  exact subroutine_ok_withLsCodeRoLoaded_of_plain hraw

theorem kyberEncaps_plain_ok_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsKemEncapsSym)
      (withLsCodeRoLoaded lsmpl (kyberEncapsStubSpec (initiatorModelPrims X ⟨W.C, W.Q⟩))) := by
  refine subroutine_ok_mono (kyberEncaps_ok_at_init_placed mmpl gh W X hh)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeRoLoaded, withVmPreserved] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

theorem panic_raw_vec_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    (initProgPlaced mmpl gh W).externAt? (lsρ lsRawVecHandleErrorSymS3) = some Rust.panicked := by
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  exact (ls_externAt?_of_mem (sym := lsRawVecHandleErrorSymS3)).trans hh.panic_raw

theorem panic_alloc_error_at_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    (initProgPlaced mmpl gh W).externAt? (lsρ lsAllocErrorSymS3) = some Rust.panicked := by
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  exact (ls_externAt?_of_mem (sym := lsAllocErrorSymS3)).trans hh.panic_alloc

/-! ## Budget-threaded `SepWPp` stepping and call combinators -/

theorem inInitiatePlaced_of_call_s3 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {s0 s sm : State} {k_in k_out : Nat}
    (h : InInitiatePlaced s0 s k_in)
    (hsteps : Steps (initProgPlaced mmpl gh W) s sm)
    (hpcm : sm.pc = initPcPlaced k_out)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s.sp)
    (hcsm : CalleeSavedPreserved s sm)
    (htrm : sm.trace = s.trace) :
    InInitiatePlaced s0 sm k_out := by
  rcases hcsm with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  have hfs_eq : sm.fs.files = s.fs.files :=
    TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
      (by simpa using htrm) NoFsEv.nil
  exact
    { pc := hpcm
      run := hrunm
      sp := hspm.trans h.sp
      fp := hfp.trans h.fp
      x19 := hx19.trans h.x19
      files0 := hfs_eq.trans h.files0
      inv := h.inv.of_keepsFrozen hsteps.keepsFrozen
      vregs := hvregs.trans h.vregs
      spAligned := h.spAligned }

/-- Steps a trace-preserving basic block `s → mid` while lifting `LibsignalCodeRoLoaded` and `fs.files`. -/
theorem s3_step_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP (initProgPlaced mmpl gh W) mid s P (fun sm Pm =>
      sm.trace = s.trace ∧
      (LibsignalCodeRoLoaded lsmpl sm.mem →
        sm.fs.files = s.fs.files →
        SepWPp (initProgPlaced mmpl gh W) ret sm Pm Q Qp oom))) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, htrm, hnext⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hinv.of_keepsFrozen hsteps.keepsFrozen) hfs_eq R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

/-- Steps a `VmPreserved` and trace-preserving basic block `s → mid`. -/
theorem s3_step_to_vm_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP (initProgPlaced mmpl gh W) mid s P (fun sm Pm =>
      VmPreserved s sm ∧ sm.trace = s.trace ∧
      (VmPreserved s sm →
        LibsignalCodeRoLoaded lsmpl sm.mem →
        sm.fs.files = s.fs.files →
        SepWPp (initProgPlaced mmpl gh W) ret sm Pm Q Qp oom))) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvm, htrm, hnext⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    obtain ⟨sf, hsteps', hout⟩ :=
      hnext hvm (hinv.of_keepsFrozen hsteps.keepsFrozen) hfs_eq R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem initPanicPostPlaced_of_allocFailed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat} {s0 sf : State} (Pf : SepProp)
    (h : allocFailedIn s0 sf) :
    InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf := by
  dsimp only [InitPanicPostPlaced, initSlotSpecPlaced, withLsCodeRoLoaded]
  exact Entails.pure_right (Or.inr h) (entails_anyHeap Pf)

/-- `withLsCodeRoLoaded lsmpl spec` call combinator propagating `.OutOfMemory` into `oom`. -/
theorem s3_call_oom_placed [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callee : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee (withLsCodeRoLoaded lsmpl spec))
    (g : α) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ spec.pre g s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic g s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit g code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      sm.status = .OutOfMemory →
      (sm.mem ⊨ spec.onOom g s sm ∗ (F ∗ R')) →
      (sm.mem ⊨ oom sm ∗ R'))
    (hnext : ∀ sm : State,
      sm.pc = initPcPlaced k_out → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.trace = s.trace → InInitiatePlaced s0 sm k_out) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm (spec.post g s sm ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  refine sepWPp_conseq_oom hpre ?_
  intro R' hm hL
  have hm_pre0 : s.mem ⊨ spec.pre g s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  have hm_pre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre g s ∗ (F ∗ R') :=
    satisfies_withLsCodeRoLoaded_pre hctrl.inv hm_pre0
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F ∗ R') s hpc hctrl.run hm_pre
      (InInitiatePlaced.spAligned_cur_s3 hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hctrl.inv.of_keepsFrozen hsteps.keepsFrozen)
        (inInitiatePlaced_of_call_s3 hh hctrl hsteps hpcm hrunm hspm hcsm)
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic g s sm ∗ F) ∗ R' := by
      rwa [← sepConj_assoc] at hpost
    have halloc0 : allocFailedIn s0 sm := by
      simpa only [allocFailedIn, htr] using hpan_imp sm (F ∗ R') hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hm_pan,
      hpanic sm _ (initPanicPostPlaced_of_allocFailed _ halloc0)⟩)⟩
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom_imp sm R' hoom_st hpost⟩)⟩

/-- `withLsCodeRoLoaded lsmpl spec` call combinator when `spec.onOom` is unsatisfiable. -/
theorem s3_call_placed [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callee : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee (withLsCodeRoLoaded lsmpl spec))
    (g : α) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ spec.pre g s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic g s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit g code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom g s sm ∗ R'))
    (hnext : ∀ sm : State,
      sm.pc = initPcPlaced k_out → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.trace = s.trace → InInitiatePlaced s0 sm k_out) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm (spec.post g s sm ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_call_oom_placed hh hcall g F hctrl htr hpc hlr hpanic hpre hpan_imp hexit_imp
    (fun sm R' _ hpost => (hoom_imp sm (F ∗ R') hpost).elim) hnext

/-- Total-correctness `__rustc::__rust_alloc` call combinator under `FitsEvents M lim st (rustAllocEvents sz 1)`. -/
theorem s3_call_alloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (sz : Nat) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hpc : s.pc = lsρ lsRustAllocSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : (s.readReg64 .x0).toNat = sz)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : RustLayoutOk sz 1)
    (hFit : FitsEvents M lim st (rustAllocEvents sz 1))
    (hpre : P ⊢ A.pool lim st s ∗ stackAt s.sp extHookStack ∗ F)
    (hnext_ok : ∀ sm : State,
      InInitiatePlaced s0 sm k_out →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 ≠ 0#64 →
      AllocCallPreserved s sm →
      sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim (M.stepEvents (rustAllocEvents sz 1) st) sm ∗
          stackAt s.sp extHookStack ∗
          A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F)
        Q Qp oom)
    (hk_out : k_out < lsLen 521 := by decide) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have halloc := alloc_ok_at_init_placed hh
  have hpre' : P ⊢
      (rustCliAllocBudgetSpecWithStack M A lim false extHookStack).pre (sz, 1, st) s ∗ F := by
    refine Entails.trans hpre ?_
    dsimp only [rustCliAllocBudgetSpecWithStack]
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hlay, ⟨521, by decide, k_out, hk_out, hlr⟩⟩
      (Entails.of_eq (by sep_ac_rfl))
  refine sepWPp_conseq_oom hpre' ?_
  intro R' hm hL
  have hm_pre0 : s.mem ⊨
      (rustCliAllocBudgetSpecWithStack M A lim false extHookStack).pre (sz, 1, st) s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  have hm_pre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)).pre (sz, 1, st) s ∗ (F ∗ R') :=
    satisfies_withLsCodeRoLoaded_pre hctrl.inv hm_pre0
  obtain ⟨sm, hsteps, hout, -⟩ :=
    halloc.no_fault_before_outcome (sz, 1, st) (F ∗ R') s hpc hctrl.run hm_pre
      (InInitiatePlaced.spAligned_cur_s3 hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · rw [hlr] at hpcm
    dsimp only [withLsCodeRoLoaded, rustCliAllocBudgetSpecWithStack] at hpost
    by_cases hnull : sm.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost' : sm.mem ⊨
          ⌜NullAllowed sz 1⌝ ∗
            (⌜AllocCallPreserved s sm⌝ ∗ A.pool lim st sm ∗
              stackAt s.sp extHookStack ∗ F ∗ R') :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      exact (not_nullAllowed_of_fitsAllocEvents hlay hFit hpost'.1).elim
    · simp only [hnull, Bool.false_eq_true, ↓reduceIte] at hpost
      have hpost1 : sm.mem ⊨
          ⌜AllocCallPreserved s sm⌝ ∗
            (⌜(sm.readReg64 .x0).toNat % 1 = 0⌝ ∗
              ((A.pool lim (M.stepEvents (rustAllocEvents sz 1) st) sm ∗
                stackAt s.sp extHookStack ∗
                A.live (sm.readReg64 .x0) sz 1 ∗
                memRegion (sm.readReg64 .x0) sz ∗ F) ∗ R')) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hacp, hpost2⟩
      rw [satisfies_pure_sepConj] at hpost2
      rcases hpost2 with ⟨_, hmem_ok⟩
      have htrm : sm.trace = s.trace := hacp.2.1
      have hctrl' := inInitiatePlaced_of_call_s3 hh hctrl hsteps hpcm hrunm hspm hcsm htrm
      obtain ⟨sf, hsteps', hout'⟩ :=
        hnext_ok sm hctrl' hcsm hnull hacp htrm R' hmem_ok (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded, rustCliAllocBudgetSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded, rustCliAllocBudgetSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded, rustCliAllocBudgetSpecWithStack] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact (hpost.1.1 hFit).elim

/-- Conditional-OOM `__rustc::__rust_alloc` call combinator propagating `.OutOfMemory` via `hoom_imp`. -/
theorem s3_call_alloc_oom_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (sz : Nat) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hpc : s.pc = lsρ lsRustAllocSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : (s.readReg64 .x0).toNat = sz)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : RustLayoutOk sz 1)
    (hpre : P ⊢ A.pool lim st s ∗ stackAt s.sp extHookStack ∗ F)
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      sm.status = .OutOfMemory →
      ¬ FitsEvents M lim st (rustAllocEvents sz 1) →
      OomPreserved s sm →
      (sm.mem ⊨ F ∗ R') →
      (sm.mem ⊨ oom sm ∗ R'))
    (hnext_null : ∀ sm : State,
      InInitiatePlaced s0 sm k_out →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      NullAllowed sz 1 →
      AllocCallPreserved s sm →
      sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ stackAt s.sp extHookStack ∗ F) Q Qp oom)
    (hnext_ok : ∀ sm : State,
      InInitiatePlaced s0 sm k_out →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 ≠ 0#64 →
      AllocCallPreserved s sm →
      sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim (M.stepEvents (rustAllocEvents sz 1) st) sm ∗
          stackAt s.sp extHookStack ∗
          A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F)
        Q Qp oom)
    (hk_out : k_out < lsLen 521 := by decide) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have halloc := alloc_ok_at_init_placed hh
  have hpre' : P ⊢
      (rustCliAllocBudgetSpecWithStack M A lim false extHookStack).pre (sz, 1, st) s ∗ F := by
    refine Entails.trans hpre ?_
    dsimp only [rustCliAllocBudgetSpecWithStack]
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hlay, ⟨521, by decide, k_out, hk_out, hlr⟩⟩
      (Entails.of_eq (by sep_ac_rfl))
  refine sepWPp_conseq_oom hpre' ?_
  intro R' hm hL
  have hm_pre0 : s.mem ⊨
      (rustCliAllocBudgetSpecWithStack M A lim false extHookStack).pre (sz, 1, st) s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  have hm_pre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)).pre (sz, 1, st) s ∗ (F ∗ R') :=
    satisfies_withLsCodeRoLoaded_pre hctrl.inv hm_pre0
  obtain ⟨sm, hsteps, hout, -⟩ :=
    halloc.no_fault_before_outcome (sz, 1, st) (F ∗ R') s hpc hctrl.run hm_pre
      (InInitiatePlaced.spAligned_cur_s3 hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [hlr] at hpcm
    dsimp only [withLsCodeRoLoaded, rustCliAllocBudgetSpecWithStack] at hpost
    by_cases hnull : sm.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost1 : sm.mem ⊨
          ⌜AllocCallPreserved s sm⌝ ∗
            (⌜NullAllowed sz 1⌝ ∗
              ((A.pool lim st sm ∗ stackAt s.sp extHookStack ∗ F) ∗ R')) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hacp, hpost2⟩
      rw [satisfies_pure_sepConj] at hpost2
      rcases hpost2 with ⟨hna, hmem_null⟩
      have htrm : sm.trace = s.trace := hacp.2.1
      have hctrl' := inInitiatePlaced_of_call_s3 hh hctrl hsteps hpcm hrunm hspm hcsm htrm
      obtain ⟨sf, hsteps', hout'⟩ :=
        hnext_null sm hctrl' hcsm hnull hna hacp htrm R' hmem_null (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hnull, Bool.false_eq_true, ↓reduceIte] at hpost
      have hpost1 : sm.mem ⊨
          ⌜AllocCallPreserved s sm⌝ ∗
            (⌜(sm.readReg64 .x0).toNat % 1 = 0⌝ ∗
              ((A.pool lim (M.stepEvents (rustAllocEvents sz 1) st) sm ∗
                stackAt s.sp extHookStack ∗
                A.live (sm.readReg64 .x0) sz 1 ∗
                memRegion (sm.readReg64 .x0) sz ∗ F) ∗ R')) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hacp, hpost2⟩
      rw [satisfies_pure_sepConj] at hpost2
      rcases hpost2 with ⟨_, hmem_ok⟩
      have htrm : sm.trace = s.trace := hacp.2.1
      have hctrl' := inInitiatePlaced_of_call_s3 hh hctrl hsteps hpcm hrunm hspm hcsm htrm
      obtain ⟨sf, hsteps', hout'⟩ :=
        hnext_ok sm hctrl' hcsm hnull hacp htrm R' hmem_ok (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded, rustCliAllocBudgetSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded, rustCliAllocBudgetSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded, rustCliAllocBudgetSpecWithStack] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st,
      hoom_imp sm R' hoom_st hpost.1.1 hpost.1.2 hpost.2⟩)⟩

/-- `__rustc::__rust_dealloc` call combinator advancing `A.pool` by `rustDeallocEvents sz 1`. -/
theorem s3_dealloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (p : BitVec 64) (sz : Nat) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = 1)
    (hlay : RustLayoutOk sz 1)
    (hpre : P ⊢ A.pool lim st s ∗ A.live p sz 1 ∗ memRegion p sz ∗ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out →
      CalleeSavedPreserved s sm →
      sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim (M.stepEvents (rustDeallocEvents sz 1) st) sm ∗
          stackAt s.sp extHookStack ∗ F)
        Q Qp oom)
    (hk_out : k_out < lsLen 521 := by decide) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have hdealloc := dealloc_ok_at_init_placed hh
  have hpre' : P ⊢
      (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack).pre (p, sz, 1, st) s ∗ F := by
    refine Entails.trans hpre ?_
    dsimp only [rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlay, ⟨521, by decide, k_out, hk_out, hlr⟩⟩
      (Entails.of_eq (by sep_ac_rfl))
  refine sepWPp_conseq_oom hpre' ?_
  intro R' hm hL
  have hm_pre0 : s.mem ⊨
      (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack).pre (p, sz, 1, st) s ∗
        (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  have hm_pre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)).pre (p, sz, 1, st) s ∗
        (F ∗ R') :=
    satisfies_withLsCodeRoLoaded_pre hctrl.inv hm_pre0
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hdealloc.no_fault_before_outcome (p, sz, 1, st) (F ∗ R') s hpc hctrl.run hm_pre
      (InInitiatePlaced.spAligned_cur_s3 hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · rw [hlr] at hpcm
    dsimp only [withLsCodeRoLoaded, rustCliDeallocBudgetExternSpecWithStack] at hpost
    have hpost1 : sm.mem ⊨
        ⌜sm.trace = s.trace⌝ ∗
          ((A.pool lim (M.stepEvents (rustDeallocEvents sz 1) st) sm ∗
            stackAt s.sp extHookStack ∗ F) ∗ R') :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨htrm, hmem_ok⟩
    have hctrl' := inInitiatePlaced_of_call_s3 hh hctrl hsteps hpcm hrunm hspm hcsm htrm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hctrl' hcsm htrm R' hmem_ok (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded, rustCliDeallocBudgetExternSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded, rustCliDeallocBudgetExternSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded, rustCliDeallocBudgetExternSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Discharges `Rust.panicked` once `allocFailedIn s0 s` holds. -/
theorem s3_panic_at_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hext : (initProgPlaced mmpl gh W).externAt? s.pc = some Rust.panicked)
    (hrun : s.status = .Running)
    (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  SepWPp.panic (P := P) (hrun := hrun) (hext := hext)
    (hqp := hpanic (Rust.panicked s) P
      (initPanicPostPlaced_of_allocFailed P
        (by simpa only [allocFailedIn, Rust.panicked] using hfail)))

/-- `__rust_no_alloc_shim_is_unstable_v2` call combinator exposing `VmPreserved`. -/
theorem s3_shim_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsρ lsRustNoAllocShimSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      VmPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (stackAt s.sp extHookStack ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpre' : P ⊢ (withVmPreserved session2ShimSpecX).pre () s ∗ F := hpre
  refine s3_call_placed hh (shim_ok_at_init_placed hh) () F hctrl htr hpc hlr hpanic hpre'
    ?_ ?_ ?_ ?_
  · intro _ _ h; simp [withVmPreserved, session2ShimSpecX] at h
  · intro _ _ _ h; simp [withVmPreserved, session2ShimSpecX] at h
  · intro _ _ h; simp [withVmPreserved, session2ShimSpecX] at h
  · intro sm _ _ _ hcsm _ hof
    dsimp only [withVmPreserved, session2ShimSpecX]
    simp only [sepConj_assoc]
    exact sepWPp_pure_elim_oom fun hvm =>
      sepWPp_pure_elim_oom fun htrm =>
        sepWPp_conseq_oom (Entails.of_eq (by sep_ac_rfl)) (hnext sm (hof htrm) hcsm hvm htrm)

/-- `__rust_no_alloc_shim_is_unstable_v2` call combinator transporting `A.pool` via `VmPreserved`. -/
theorem s3_shim_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsρ lsRustNoAllocShimSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ A.pool lim st s ∗ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ stackAt s.sp extHookStack ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpre' : P ⊢ stackAt s.sp extHookStack ∗ (A.pool lim st s ∗ F) :=
    Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))
  refine s3_shim_placed hh (A.pool lim st s ∗ F) hctrl htr hpc hlr hpanic hpre' ?_
  intro sm hctrl' hcsm hvm htrm
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' hcsm htrm)

/-- `memcpy` call combinator exposing `VmPreserved`. -/
theorem s3_memcpy_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsρ memcpyName)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      VmPreserved s sm → sm.readReg64 .x0 = dst → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpre' : P ⊢ (withVmPreserved session2MemcpySpecX).pre (dst, src, bs) s ∗ F :=
    Entails.trans hpre (by
      dsimp only [withVmPreserved, session2MemcpySpecX]
      simp only [sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.of_eq (by sep_ac_rfl)))
  refine s3_call_placed hh (memcpy_ok_at_init_placed hh) (dst, src, bs) F hctrl htr hpc hlr
    hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [withVmPreserved, session2MemcpySpecX] at h
  · intro _ _ _ h; simp [withVmPreserved, session2MemcpySpecX] at h
  · intro _ _ h; simp [withVmPreserved, session2MemcpySpecX] at h
  · intro sm _ _ _ hcsm _ hof
    dsimp only [withVmPreserved, session2MemcpySpecX]
    simp only [sepConj_assoc]
    exact sepWPp_pure_elim_oom fun hvm =>
      sepWPp_pure_elim_oom fun ⟨hx0m, htrm⟩ =>
        sepWPp_conseq_oom (Entails.of_eq (by sep_ac_rfl))
          (hnext sm (hof htrm) hcsm hvm hx0m htrm)

/-- `memcpy` call combinator transporting `A.pool` via `VmPreserved`. -/
theorem s3_memcpy_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (dst src : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsρ memcpyName)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ A.pool lim st s ∗ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
      stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = dst → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpre' : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗
      (A.pool lim st s ∗ F) :=
    Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))
  refine s3_memcpy_placed hh dst src bs (A.pool lim st s ∗ F) hctrl htr hpc hlr
    hx0 hx1 hx2 hpanic hpre' ?_
  intro sm hctrl' hcsm hvm hx0m htrm
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' hcsm hx0m htrm)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
