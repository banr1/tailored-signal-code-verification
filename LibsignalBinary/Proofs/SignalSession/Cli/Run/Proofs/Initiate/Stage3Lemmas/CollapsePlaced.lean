/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
public import ProofLib.BV.Bits
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 3 Framing, OOM Panic Handlers, and Stack Collapse Helpers

Provides `[LibsignalPlacement]` basic-block and `dealloc` combinators (`s3_block_in_placed`,
`s3_block_to_call_placed`, `s3_dealloc_placed`), OOM panic handlers, and `initArgsAtPlaced` collapse
lemmas on `initProgPlaced`, while re-exporting pure collapse lemmas from `Stage3Lemmas/Collapse`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `InInitiatePlaced` basic-block and `dealloc` combinators -/

theorem inInitiatePlaced_at_any_pc [LibsignalPlacement] {s0 s sm : State} {k_in : Nat}
    (h : InInitiatePlaced s0 s k_in)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hfs : sm.fs.files = s.fs.files)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s) :
    InInitiatePlaced s0 sm ((sm.pc - initEntryPlaced).toNat) :=
  { pc := by
      dsimp only [initPcPlaced]
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    run := hrun
    sp := hsp.trans h.sp
    fp := hfp.trans h.fp
    x19 := hx19.trans h.x19
    files0 := hfs.trans h.files0
    inv := hinv
    vregs := hvregs.trans h.vregs
    spAligned := h.spAligned }

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiatePlaced.step_ctx
    [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) (fsp : BitVec 64)
    (hf : fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by rfl) :
    (s.sp &&& 15#64 == 0#64) = true ∧
      s.readReg64 (.gpr 29#5) = s.sp + 7312#64 ∧
      fsp = s.sp := by
  have ha := h.spAligned_cur_s3; simp only [State.spAligned] at ha
  have hsp : s.sp = s0.sp - 7408#64 := h.sp
  have hfp : s.readReg64 (.gpr 29#5) = s0.sp - 96#64 := h.fp
  exact ⟨ha, by rw [hfp, hsp]; bv_omega, hf.trans h.sp.symm⟩

/-- Steps an isolated basic block to `initPcPlaced k_out` while preserving `InInitiatePlaced`. -/
theorem s3_block_in_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
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
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := fun R hm hL => by
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

/-- Steps an isolated basic block to `BL callee` with return address `initPcPlaced k_out`. -/
theorem s3_block_to_call_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (callee : BitVec 64) {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
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
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hlrm, hphi⟩ | ⟨_, hf⟩⟩
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

/-- Invokes `__rustc::__rust_dealloc(ptr, sz, 1)` on `initProgPlaced`. -/
theorem s3_dealloc_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ptr : BitVec 64) (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = 1)
    (hlay : LayoutOk sz 1)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ A.live ptr sz 1 ∗ memRegion ptr sz ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ (rustDeallocExternSpecWithStack A extHookStack).pre
      (ptr, sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [rustDeallocExternSpecWithStack, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩ (Entails.of_eq (by ac_rfl))
  refine s3_call_placed hh (dealloc_ok_at_init_placed hh) (ptr, sz, 1) F hctrl htr hpc hlr hpanic hpre'
    ?_ ?_ ?_ ?_
  · intro _ _ h; simp only [rustDeallocExternSpecWithStack] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ _ h; simp only [rustDeallocExternSpecWithStack] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ h; simp only [rustDeallocExternSpecWithStack] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro sm _ _ _ hcsm _ hof
    simp only [rustDeallocExternSpecWithStack, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun htrm =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm htrm)

/-! ## Allocator OOM panic handlers (`+0x1918`, `+0x1930`, `+0x193c`) -/

theorem oom_1918_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpc : s.pc = initPcPlaced 0x1918) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
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

theorem oom_1930_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpc : s.pc = initPcPlaced 0x1930) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
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

theorem oom_193c_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpc : s.pc = initPcPlaced 0x193c) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
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

/-! ## `initArgsAtPlaced` memory collapse -/

theorem initArgsAtPlaced_collapse [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost) (s0 : State) :
    initArgsAtPlaced fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 0x58 := by
  dsimp only [initArgsAtPlaced]
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo32_entails_memRegion _ _)
                      (sepConj_mono (Entails.refl _)
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  rw [memRegion_merge_at (fsp + 0x118#64) 8 8 (fsp + 0x120#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x114#64) 4 16 (fsp + 0x118#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x110#64) 4 20 (fsp + 0x114#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x108#64) 8 24 (fsp + 0x110#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x100#64) 8 32 (fsp + 0x108#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0xf8#64) 8 40 (fsp + 0x100#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0xf0#64) 8 48 (fsp + 0xf8#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0xe8#64) 8 56 (fsp + 0xf0#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0xe0#64) 8 64 (fsp + 0xe8#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0xd8#64) 8 72 (fsp + 0xe0#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0xd0#64) 8 80 (fsp + 0xd8#64) (by bv_omega) (by decide)]
  exact Entails.refl _

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
