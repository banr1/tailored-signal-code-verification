/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable Stage 3 Framing, OOM Panic Handlers, and Stack Collapse Helpers

Provides `RustCliAllocBudget M` and `VmPreserved` basic-block, `dealloc`, OOM panic, and stack
collapse combinators on `initProgPlaced`, while re-exporting allocator-free collapse lemmas from
`Stage3Lemmas/CollapsePlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.LibsignalPublicApi.StoreKit (NoFsEv TraceFsSound)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (LayoutOk allocFailedIn)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.RunCompose (BundleV InitGhost RunSem initResAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InInitiatePlaced initEntryPlaced initPcPlaced initProgPlaced stage3KeySlotsAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
  (inInitiatePlaced_at_any_pc lsAllocErrorSymS3 lsRawVecHandleErrorSymS3 sepWP_bind_oom
   sret_err_speOwned stage3KeySlotsAt_collapse)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget RustLayoutOk VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (initPanicPostPlaced_of_allocFailed panic_alloc_error_at_init_placed
   panic_raw_vec_at_init_placed s3_dealloc_placed)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `SepWPp` framing and `by_vm_steps` terminal helpers -/

/-- Frames `F` across `SepWPp` for any `oom` assertion that absorbs `F` on `.OutOfMemory`. -/
theorem sepWPp_frame_oom_any {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hoom_imp : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R'))
    (hw : SepWPp prog ret s P
      (fun sf Pf => Q sf (Pf ∗ F))
      (fun sf Pf => Qp sf (Pf ∗ F))
      oom) :
    SepWPp prog ret s (P ∗ F) Q Qp oom := fun R hm hL => by
  have hm' : s.mem ⊨ P ∗ (F ∗ R) := by rwa [sepConj_assoc] at hm
  obtain ⟨sf, hsteps,
      ⟨hpc, hrun, Pf, hm_f, hq⟩ | ⟨hpan, Pf, hm_f, hqp⟩ | ⟨hoom, hm_oom⟩⟩ :=
    hw (F ∗ R) hm' hL
  · rw [← sepConj_assoc] at hm_f
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf ∗ F, hm_f, hq⟩⟩
  · rw [← sepConj_assoc] at hm_f
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, Pf ∗ F, hm_f, hqp⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom, hoom_imp sf R hoom hm_oom⟩)⟩

theorem s3_done_in_vm {prog : Program} {target : BitVec 64} {s sm : State}
    {P P' : SepProp} {Φ : State → Prop}
    (hrun : sm.status = .Running) (hent : P ⊢ P') (hphi : Φ sm)
    (hpc : sm.pc = target := by wp_norm_goal)
    (htp : sm.tpidrEl0 = s.tpidrEl0 := by simp only [arm64_norm, wp_norm])
    (htr : sm.trace = s.trace := by simp only [arm64_norm, wp_norm])
    (hsp : sm.sp = s.sp := by wp_norm_goal)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp := by wp_norm_goal)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by wp_norm_goal)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s := by
      simp only [calleeSavedVRegs, arm64_norm, wp_norm]) :
    SepWP prog target sm P (fun s' P'' =>
      s'.tpidrEl0 = s.tpidrEl0 ∧ s'.trace = s.trace ∧ (P'' ⊢ P') ∧ s'.sp = s.sp ∧
      s'.readReg64 .fp = s.readReg64 .fp ∧ s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs s' = calleeSavedVRegs s ∧ Φ s') :=
  SepWP.done hpc hrun ⟨htp, htr, hent, hsp, hfp, hx19, hvregs, hphi⟩

theorem s3_done_call_vm {prog : Program} {callee lr_out : BitVec 64} {s sm : State}
    {P P' : SepProp} {Φ : State → Prop}
    (hrun : sm.status = .Running) (hent : P ⊢ P') (hphi : Φ sm)
    (hpc : sm.pc = callee := by wp_norm_goal)
    (htp : sm.tpidrEl0 = s.tpidrEl0 := by simp only [arm64_norm, wp_norm])
    (htr : sm.trace = s.trace := by simp only [arm64_norm, wp_norm])
    (hsp : sm.sp = s.sp := by wp_norm_goal)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp := by wp_norm_goal)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by wp_norm_goal)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s := by
      simp only [calleeSavedVRegs, arm64_norm, wp_norm])
    (hlr : sm.readReg64 .lr = lr_out := by wp_norm_goal) :
    SepWP prog callee sm P (fun s' P'' =>
      s'.tpidrEl0 = s.tpidrEl0 ∧ s'.trace = s.trace ∧ (P'' ⊢ P') ∧ s'.sp = s.sp ∧
      s'.readReg64 .fp = s.readReg64 .fp ∧ s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs s' = calleeSavedVRegs s ∧ s'.readReg64 .lr = lr_out ∧ Φ s') :=
  SepWP.done hpc hrun ⟨htp, htr, hent, hsp, hfp, hx19, hvregs, hlr, hphi⟩

/-! ## `InInitiatePlaced` basic-block and `dealloc` combinators -/

/-- Steps an isolated basic block to `initPcPlaced k_out` while preserving `InInitiatePlaced`. -/
theorem s3_block_in_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {Φ : State → Prop}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hwp : SepWP (initProgPlaced mmpl gh W) ((blkPl_521).base + BitVec.ofNat 64 k_out) s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧ Φ sm))
    (hcont : ∀ sm : State,
      sm.trace = s.trace →
      InInitiatePlaced s0 sm k_out →
      Φ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm P' Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    have hctrl' : InInitiatePlaced s0 sm k_out :=
      { pc := hpcm
        run := hrunm
        sp := hsp.trans hctrl.sp
        fp := hfp.trans hctrl.fp
        x19 := hx19.trans hctrl.x19
        files0 := hfs_eq.trans hctrl.files0
        inv := hctrl.inv.of_keepsFrozen hsteps.keepsFrozen
        vregs := hvregs.trans hctrl.vregs
        spAligned := hctrl.spAligned }
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm htrm hctrl' hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

/-- `VmPreserved`-preserving basic-block combinator landing at `initPcPlaced k_out`. -/
theorem s3_block_in_vm_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {Φ : State → Prop}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hwp : SepWP (initProgPlaced mmpl gh W) ((blkPl_521).base + BitVec.ofNat 64 k_out) s P (fun sm Pm =>
      VmPreserved s sm ∧ sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧ Φ sm))
    (hcont : ∀ sm : State,
      VmPreserved s sm →
      sm.trace = s.trace →
      InInitiatePlaced s0 sm k_out →
      Φ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm P' Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps,
        ⟨hpcm, hrunm, Pm, hmm, hvm, htrm, hent, hsp, hfp, hx19, hvregs, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    have hctrl' : InInitiatePlaced s0 sm k_out :=
      { pc := hpcm
        run := hrunm
        sp := hsp.trans hctrl.sp
        fp := hfp.trans hctrl.fp
        x19 := hx19.trans hctrl.x19
        files0 := hfs_eq.trans hctrl.files0
        inv := hctrl.inv.of_keepsFrozen hsteps.keepsFrozen
        vregs := hvregs.trans hctrl.vregs
        spAligned := hctrl.spAligned }
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm hvm htrm hctrl' hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

/-- Steps an isolated basic block to `BL callee` with return address `initPcPlaced k_out`. -/
theorem s3_block_to_call_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (callee : BitVec 64) {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {Φ : State → Prop}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hwp : SepWP (initProgPlaced mmpl gh W) callee s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧ Φ sm))
    (hcont : ∀ sm : State,
      InInitiatePlaced s0 sm ((sm.pc - initEntryPlaced).toNat) →
      sm.pc = callee →
      sm.readReg64 .lr = initPcPlaced k_out →
      sm.trace = s.trace →
      Φ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm P' Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps,
        ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hlrm, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    have hctrl' := inInitiatePlaced_at_any_pc hctrl hrunm hsp hfp hx19 hfs_eq
      (hctrl.inv.of_keepsFrozen hsteps.keepsFrozen) hvregs
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm hctrl' hpcm hlrm htrm hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

/-- `VmPreserved`-preserving basic-block combinator stepping to `BL callee` with return address `initPcPlaced k_out`. -/
theorem s3_block_to_call_vm_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (callee : BitVec 64) {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {Φ : State → Prop}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hwp : SepWP (initProgPlaced mmpl gh W) callee s P (fun sm Pm =>
      VmPreserved s sm ∧ sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧ Φ sm))
    (hcont : ∀ sm : State,
      VmPreserved s sm →
      InInitiatePlaced s0 sm ((sm.pc - initEntryPlaced).toNat) →
      sm.pc = callee →
      sm.readReg64 .lr = initPcPlaced k_out →
      sm.trace = s.trace →
      Φ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm P' Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps,
        ⟨hpcm, hrunm, Pm, hmm, hvm, htrm, hent, hsp, hfp, hx19, hvregs, hlrm, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    have hctrl' := inInitiatePlaced_at_any_pc hctrl hrunm hsp hfp hx19 hfs_eq
      (hctrl.inv.of_keepsFrozen hsteps.keepsFrozen) hvregs
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm hvm hctrl' hpcm hlrm htrm hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem rustLayoutOk_of_layoutOk1 {sz : Nat} (h : LayoutOk sz 1) : RustLayoutOk sz 1 :=
  ⟨h, by decide⟩

/-- Invokes `__rustc::__rust_dealloc(ptr, sz, 1)` in `stackAt`-first spatial order on `initProgPlaced`. -/
theorem s3_dealloc_stack_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ptr : BitVec 64) (sz : Nat) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = 1)
    (hlay : LayoutOk sz 1)
    (hpre : P ⊢ A.pool lim st s ∗ stackAt s.sp extHookStack ∗
      A.live ptr sz 1 ∗ memRegion ptr sz ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim (M.stepEvents (rustDeallocEvents sz 1) st) sm ∗
          stackAt s.sp extHookStack ∗ F)
        Q Qp oom)
    (hk_out : k_out < lsLen 521 := by decide) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_dealloc_placed hh ptr sz st F hctrl hpc hlr hx0 hx1 hx2
    (rustLayoutOk_of_layoutOk1 hlay)
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl)))
    hnext hk_out

/-! ## Allocator OOM panic handlers (`+0x1918`, `+0x1930`, `+0x193c`) -/

theorem oom_1918_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpc : s.pc = initPcPlaced 0x1918) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have hext := panic_raw_vec_at_init_placed hh
  refine sepWP_bind_oom (mid := lsρ lsRawVecHandleErrorSymS3) ?_
  have hpc' : s.pc = (blkPl_521).base + 6424#64 := hpc
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPostPlaced_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

theorem oom_1930_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpc : s.pc = initPcPlaced 0x1930) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have hext := panic_alloc_error_at_init_placed hh
  refine sepWP_bind_oom (mid := lsρ lsAllocErrorSymS3) ?_
  have hpc' : s.pc = (blkPl_521).base + 6448#64 := hpc
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPostPlaced_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

theorem oom_193c_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpc : s.pc = initPcPlaced 0x193c) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  have hext := panic_alloc_error_at_init_placed hh
  refine sepWP_bind_oom (mid := lsρ lsAllocErrorSymS3) ?_
  have hpc' : s.pc = (blkPl_521).base + 6460#64 := hpc
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPostPlaced_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

/-! ## Budget-threaded stack and return-slot collapse wrappers -/

theorem sret_err_speOwned_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (peer : AddrVal) (ret : BitVec 64) (w1 w2 w3 w4 w5 : BitVec 64) :
    (ret ↦₆₄ speWord 10) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
      ((ret + 24#64) ↦₆₄ w3) ∗ ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) ⊢
      initResAt A.repAlloc ret (.error (.untrustedIdentity peer)) :=
  sret_err_speOwned A.repAlloc peer ret w1 w2 w3 w4 w5

theorem stage3KeySlotsAt_collapse_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (fsp : BitVec 64) (b : BundleV) (kp : IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (hekPk : ekAPk.length = 32) (hekSk : ekASk.length = 32) (hkpk : b.kpk.length = 1568) :
    stage3KeySlotsAt A.repAlloc fsp b kp ekASk ekAPk pqspkPtr opkId ⊢
      memRegion (fsp + 0x298#64) 0x190 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion (fsp + 0x438#64) 0x28 :=
  stage3KeySlotsAt_collapse A.repAlloc fsp b kp ekASk ekAPk pqspkPtr opkId hekPk hekSk hkpk

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
