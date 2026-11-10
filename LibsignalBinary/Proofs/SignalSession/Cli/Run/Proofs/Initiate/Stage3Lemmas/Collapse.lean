/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 Framing, OOM Panic Handlers, and Stack Collapse Helpers

Provides isolated basic-block and `__rust_dealloc` combinators (`s3_block_in`, `s3_block_to_call`,
`s3_dealloc`), OOM panic handlers (`+0x1918`, `+0x1930`, `+0x193c`), stack-region collapse lemmas,
and `CliExternsOk` counterparts (`Ext.*`) for Stage 3 of `initiate`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
noncomputable section
namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `SepWPp` framing, sequencing, and OOM trace helpers -/

theorem sepWPp_frame_oom {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hw : SepWPp prog ret s P
      (fun sf Pf => Q sf (Pf ∗ F))
      (fun sf Pf => Qp sf (Pf ∗ F))
      (initOom s0)) :
    SepWPp prog ret s (P ∗ F) Q Qp (initOom s0) := fun R hm hL => by
  have hm' : s.mem ⊨ P ∗ (F ∗ R) := by rwa [sepConj_assoc] at hm
  obtain ⟨sf, hsteps,
      ⟨hpc, hrun, Pf, hm_f, hq⟩ | ⟨hpan, Pf, hm_f, hqp⟩ | ⟨hoom, hm_oom⟩⟩ :=
    hw (F ∗ R) hm' hL
  · rw [← sepConj_assoc] at hm_f
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf ∗ F, hm_f, hq⟩⟩
  · rw [← sepConj_assoc] at hm_f
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, Pf ∗ F, hm_f, hqp⟩)⟩
  · dsimp only [initOom] at hm_oom
    rw [satisfies_pure_sepConj] at hm_oom
    exact hm_oom.1.elim

theorem sepWP_bind_oom {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp Qoom)) :
    SepWPp prog ret s P Q Qp Qoom := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem allocFailedIn_of_append {s0 s : State}
    (h : s.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 s := by
  simp [allocFailedIn, h]

theorem inInitiate_at_any_pc {img : Obj.Image} {W : CliHooks} {s0 s sm : State} {k_in : Nat}
    (h : InInitiate img W s0 s k_in)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hfs : sm.fs.files = s.fs.files)
    (hinv : ImgCallInv img sm)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s) :
    InInitiate img W s0 sm ((sm.pc - initEntry img W).toNat) :=
  { pc := by
      dsimp only [initPc]
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

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiate.step_ctx
    {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) (fsp : BitVec 64)
    (hf : fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by rfl) :
    (s.sp &&& 15#64 == 0#64) = true ∧
      s.readReg64 (.gpr 29#5) = s.sp + 7312#64 ∧
      fsp = s.sp := by
  have ha := h.spAligned_cur; simp only [State.spAligned] at ha
  have hsp : s.sp = s0.sp - 7408#64 := h.sp
  have hfp : s.readReg64 (.gpr 29#5) = s0.sp - 96#64 := h.fp
  exact ⟨ha, by rw [hfp, hsp]; bv_omega, hf.trans h.sp.symm⟩

/-- Steps an isolated basic block to `initPc img W k_out` while preserving `InInitiate`. -/
theorem s3_block_in {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W))
    {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hctrl : InInitiate img W s0 s k_in)
    (hwp : SepWP (initProg img W) (initPc img W k_out) s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧ Φ sm))
    (hcont : ∀ sm : State,
      sm.trace = s.trace →
      InInitiate img W s0 sm k_out →
      Φ sm →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq hh.fs hsteps (evs := []) (by simpa using htrm) NoFsEv.nil
    have hctrl' : InInitiate img W s0 sm k_out :=
      { pc := hpcm
        run := hrunm
        sp := hsp.trans hctrl.sp
        fp := hfp.trans hctrl.fp
        x19 := hx19.trans hctrl.x19
        files0 := hfs_eq.trans hctrl.files0
        inv := hctrl.inv.of_steps hsteps
        vregs := hvregs.trans hctrl.vregs
        spAligned := hctrl.spAligned }
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm htrm hctrl' hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

/-- Steps an isolated basic block to `BL callee` with return address `initPc img W k_out`. -/
theorem s3_block_to_call {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W))
    (callee : BitVec 64) {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hctrl : InInitiate img W s0 s k_in)
    (hwp : SepWP (initProg img W) callee s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .lr = initPc img W k_out ∧ Φ sm))
    (hcont : ∀ sm : State,
      InInitiate img W s0 sm ((sm.pc - initEntry img W).toNat) →
      sm.pc = callee →
      sm.readReg64 .lr = initPc img W k_out →
      sm.trace = s.trace →
      Φ sm →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hlrm, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq hh.fs hsteps (evs := []) (by simpa using htrm) NoFsEv.nil
    have hctrl' := inInitiate_at_any_pc hctrl hrunm hsp hfp hx19 hfs_eq
      (hctrl.inv.of_steps hsteps) hvregs
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm hctrl' hpcm hlrm htrm hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

/-- Invokes `__rustc::__rust_dealloc(ptr, sz, 1)` inside `initiate`. -/
theorem s3_dealloc {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hh : RunHooks img A (cliExterns W))
    (ptr : BitVec 64) (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntry img W +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    (hlr : s.readReg64 .lr = initPc img W k_out)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = 1)
    (hlay : LayoutOk sz 1)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ A.live ptr sz 1 ∗ memRegion ptr sz ∗ F)
    (hnext : ∀ sm : State,
      InInitiate img W s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
      (ptr, sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [rustDeallocExternSpecWithStack, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hctrl.inv
      (Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩ (Entails.of_eq (by ac_rfl)))
  refine s3_call hh (dealloc_ok_at_init hh) (ptr, sz, 1) F hctrl htr hpc hlr hpanic hpre'
    ?_ ?_ ?_ ?_
  · intro _ _ h; simp only [rustDeallocExternSpecWithStack, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ _ h; simp only [rustDeallocExternSpecWithStack, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ h; simp only [rustDeallocExternSpecWithStack, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro sm _ _ _ hcsm _ hof
    simp only [rustDeallocExternSpecWithStack, Spec.inImage, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun htrm =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm htrm)

/-! ## Allocator OOM panic handlers (`+0x1918`, `+0x1930`, `+0x193c`) -/

theorem oom_1918_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = initPc img W 0x1918) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hext := panic_raw_vec_at_init img W
  refine sepWP_bind_oom (mid := initEntry img W +
    bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::raw_vec::handle_error")) ?_
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1918 12
  dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
    BitVec.ofNat_eq_ofNat] at hpc hext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPost_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

theorem oom_1930_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = initPc img W 0x1930) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hext := panic_alloc_error_at_init img W
  refine sepWP_bind_oom (mid := initEntry img W +
    bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::alloc::handle_alloc_error")) ?_
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1930 12
  dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
    BitVec.ofNat_eq_ofNat] at hpc hext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPost_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

theorem oom_193c_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = initPc img W 0x193c) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hext := panic_alloc_error_at_init img W
  refine sepWP_bind_oom (mid := initEntry img W +
    bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::alloc::handle_alloc_error")) ?_
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x193c 12
  dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
    BitVec.ofNat_eq_ofNat] at hpc hext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPost_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

/-! ## Memory collapse and stack reassembly helpers -/

theorem memRegion_merge_at (b : BitVec 64) (n k : Nat) (b' : BitVec 64)
    (hb : b' = b + BitVec.ofNat 64 n) (hnk : n + k ≤ 2 ^ 64) :
    memRegion b n ∗ memRegion b' k = memRegion b (n + k) := by
  rw [hb, ← memRegion_split b n k hnk]

theorem pointsTo8_entails_memRegion1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ⊢ memRegion a 1 :=
  pointsTo8_entails_memRegion a b

theorem pointsToBytes_entails_memRegion_len {a : BitVec 64} {bs : List (BitVec 8)} {n : Nat}
    (hlen : bs.length = n) :
    (a ↦ₛ bs) ⊢ memRegion a n :=
  hlen ▸ pointsToBytes_entails_memRegion a bs

theorem sret_err_speOwned (A : RustAlloc) (peer : AddrVal) (ret : BitVec 64)
    (w1 w2 w3 w4 w5 : BitVec 64) :
    (ret ↦₆₄ speWord 10) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
      ((ret + 24#64) ↦₆₄ w3) ∗ ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) ⊢
      initResAt A ret (.error (.untrustedIdentity peer)) := by
  have h5 :
      ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
        ((ret + 24#64) ↦₆₄ w3) ∗ ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) ⊢
        memRegion (ret + 8#64) 40 := by
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ w1)
        (sepConj_mono (pointsTo64_entails_memRegion _ w2)
          (sepConj_mono (pointsTo64_entails_memRegion _ w3)
            (sepConj_mono (pointsTo64_entails_memRegion _ w4)
              (pointsTo64_entails_memRegion _ w5))))) ?_
    rw [memRegion_merge_at (ret + 32#64) 8 8 (ret + 40#64) (by bv_omega) (by decide),
      memRegion_merge_at (ret + 24#64) 8 16 (ret + 32#64) (by bv_omega) (by decide),
      memRegion_merge_at (ret + 16#64) 8 24 (ret + 24#64) (by bv_omega) (by decide),
      memRegion_merge_at (ret + 8#64) 8 32 (ret + 16#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right h5) ?_
  dsimp only [initResAt]
  exact Entails.sepExists_right (RunDrop.SpeOwned.plain 10 (by decide)) (Entails.refl _)

theorem initSaved_entails_memRegion96 (s0 : State) :
    initSaved s0 ⊢ memRegion (s0.sp - 0x60#64) 0x60 := by
  let b := s0.sp - 0x60#64
  dsimp only [initSaved]
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  rw [memRegion_merge_at (b + 0x50#64) 8 8 (b + 0x58#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x48#64) 8 16 (b + 0x50#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x40#64) 8 24 (b + 0x48#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x38#64) 8 32 (b + 0x40#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x30#64) 8 40 (b + 0x38#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x28#64) 8 48 (b + 0x30#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x20#64) 8 56 (b + 0x28#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x18#64) 8 64 (b + 0x20#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x10#64) 8 72 (b + 0x18#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x08#64) 8 80 (b + 0x10#64) (by bv_omega) (by decide),
    memRegion_merge_at (b + 0x00#64) 8 88 (b + 0x08#64) (by bv_omega) (by decide)]
  simpa only [BitVec.add_zero] using (Entails.refl (memRegion (b + 0x00#64) 96))

theorem initArgsAt_collapse (img : Obj.Image) (fsp : BitVec 64) (x : InitGhost) (s0 : State) :
    initArgsAt img fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 0x58 := by
  dsimp only [initArgsAt]
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

theorem initFreshRecAt_collapse (fsp : BitVec 64) :
    initFreshRecAt fsp ⊢ memRegion (fsp + 0x128#64) 0x20 := by
  dsimp only [initFreshRecAt]
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _)))) ?_
  rw [memRegion_merge_at (fsp + 0x138#64) 8 8 (fsp + 0x140#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x130#64) 8 16 (fsp + 0x138#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x128#64) 8 24 (fsp + 0x130#64) (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stage3KeySlotsAt_collapse (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (hekPk : ekAPk.length = 32) (hekSk : ekASk.length = 32) (hkpk : b.kpk.length = 1568) :
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId ⊢
      memRegion (fsp + 0x298#64) 0x190 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion (fsp + 0x438#64) 0x28 := by
  have hopk :
      (match b.opk with
       | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
       | none => memRegion (fsp + 0x439#64) 32) ⊢ memRegion (fsp + 0x439#64) 32 := by
    cases b.opk with
    | none => exact Entails.refl _
    | some pk => exact pointsToBytes_entails_memRegion_len pk.2.bytes.toList_length
  dsimp only [stage3KeySlotsAt]
  refine Entails.trans
    (sepConj_mono (pointsToBytes_entails_memRegion_len hekPk)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsToBytes_entails_memRegion_len kp.identityKey.publicKey.bytes.toList_length)
    (sepConj_mono (pointsToBytes_entails_memRegion_len kp.privateKey.bytes.toList_length)
    (sepConj_mono (pointsToBytes_entails_memRegion_len hekPk)
    (sepConj_mono (pointsToBytes_entails_memRegion_len hekSk)
    (sepConj_mono (pointsToBytes_entails_memRegion_len b.idKey.publicKey.bytes.toList_length)
    (sepConj_mono (pointsToBytes_entails_memRegion_len b.spk.bytes.toList_length)
    (sepConj_mono (pointsToBytes_entails_memRegion_len b.spk.bytes.toList_length)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsToBytes_entails_memRegion_len hkpk)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ _)
    (sepConj_mono hopk
    (sepConj_mono (pointsTo8_entails_memRegion1 _ _)
      (Entails.refl _)))))))))))))))))))) ?_
  rw [memRegion_merge_at (fsp + 0x459#64) 1 6 (fsp + 0x45a#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x439#64) 32 7 (fsp + 0x459#64) (by bv_omega) (by decide),
    memRegion_merge_at (fsp + 0x438#64) 1 39 (fsp + 0x439#64) (by bv_omega) (by decide)]
  have hleft :
      memRegion (fsp + 0x298#64) 32 ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
        memRegion (fsp + 0x300#64) 4 ∗ memRegion (fsp + 0x304#64) 4 ∗
        memRegion (fsp + 0x308#64) 0x40 ∗ memRegion (fsp + 0x348#64) 32 ∗
        memRegion (fsp + 0x368#64) 32 ∗ memRegion (fsp + 0x388#64) 32 ∗
        memRegion (fsp + 0x3a8#64) 32 ∗ memRegion (fsp + 0x3c8#64) 32 ∗
        memRegion (fsp + 0x3e8#64) 32 ∗ memRegion (fsp + 0x408#64) 32 =
      memRegion (fsp + 0x298#64) 0x190 := by
    rw [memRegion_merge_at (fsp + 0x3e8#64) 32 32 (fsp + 0x408#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x3c8#64) 32 64 (fsp + 0x3e8#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x3a8#64) 32 96 (fsp + 0x3c8#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x388#64) 32 128 (fsp + 0x3a8#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x368#64) 32 160 (fsp + 0x388#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x348#64) 32 192 (fsp + 0x368#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x308#64) 0x40 224 (fsp + 0x348#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x304#64) 4 288 (fsp + 0x308#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x300#64) 4 292 (fsp + 0x304#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x2b8#64) 0x48 296 (fsp + 0x300#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x298#64) 32 368 (fsp + 0x2b8#64) (by bv_omega) (by decide)]
  rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  exact Entails.of_eq (by rw [← hleft]; ac_rfl)

theorem stack_frame_reassemble {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) (s0 : State) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    memRegion fsp initLocalsSize ∗ memRegion (s0.sp - 0x60#64) 0x60 ∗
      stackAt fsp (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  dsimp only
  have hge : cliInitiateFrame ≤ stk := stk_ge_frame hstk
  have h1 :
      memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize ∗
        memRegion (s0.sp - 0x60#64) 0x60 =
      memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) cliInitiateFrame := by
    rw [memRegion_merge_at (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize 0x60
      (s0.sp - 0x60#64) (by dsimp only [cliInitiateFrame, initLocalsSize]; bv_omega) (by decide)]
  rw [← sepConj_assoc, h1, sepConj_comm]
  dsimp only [stackAt]
  have hbase :
      s0.sp - BitVec.ofNat 64 cliInitiateFrame - BitVec.ofNat 64 (stk - cliInitiateFrame) =
        s0.sp - BitVec.ofNat 64 stk := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add,
      show cliInitiateFrame + (stk - cliInitiateFrame) = stk from by omega]
  have hadd :
      s0.sp - BitVec.ofNat 64 cliInitiateFrame =
        (s0.sp - BitVec.ofNat 64 stk) + BitVec.ofNat 64 (stk - cliInitiateFrame) := by
    rw [← hbase, BitVec.sub_add_cancel]
  rw [hbase, memRegion_merge_at (s0.sp - BitVec.ofNat 64 stk) (stk - cliInitiateFrame)
    cliInitiateFrame (s0.sp - BitVec.ofNat 64 cliInitiateFrame) hadd (by omega),
    show stk - cliInitiateFrame + cliInitiateFrame = stk from by omega]
  exact Entails.refl _

/-! ## Extern-parameterized framing, block, and OOM helpers (`Ext.*`) -/

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiateExt.step_ctx
    {img : Obj.Image} {ext : String → Option (State → State)} {s0 s : State} {k : Nat}
    (h : InInitiateExt img ext s0 s k) (fsp : BitVec 64)
    (hf : fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by rfl) :
    (s.sp &&& 15#64 == 0#64) = true ∧
      s.readReg64 (.gpr 29#5) = s.sp + 7312#64 ∧
      fsp = s.sp := by
  have ha := h.spAligned_cur; simp only [State.spAligned] at ha
  have hsp : s.sp = s0.sp - 7408#64 := h.sp
  have hfp : s.readReg64 (.gpr 29#5) = s0.sp - 96#64 := h.fp
  exact ⟨ha, by rw [hfp, hsp]; bv_omega, hf.trans h.sp.symm⟩

namespace Ext

theorem inInitiate_at_any_pc {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s sm : State} {k_in : Nat}
    (h : InInitiateExt img ext s0 s k_in)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hfs : sm.fs.files = s.fs.files)
    (hinv : ImgCallInv img sm)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s) :
    InInitiateExt img ext s0 sm ((sm.pc - initEntryExt img ext).toNat) :=
  { pc := by
      dsimp only [initPcExt]
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

theorem s3_block_in {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P0 A ext)
    {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in)
    (hwp : SepWP (initProgExt img ext) (initPcExt img ext k_out) s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧ Φ sm))
    (hcont : ∀ sm : State,
      sm.trace = s.trace →
      InInitiateExt img ext s0 sm k_out →
      Φ sm →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (initProgExt_traceFsSound img hOk) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    have hctrl' : InInitiateExt img ext s0 sm k_out :=
      { pc := hpcm
        run := hrunm
        sp := hsp.trans hctrl.sp
        fp := hfp.trans hctrl.fp
        x19 := hx19.trans hctrl.x19
        files0 := hfs_eq.trans hctrl.files0
        inv := hctrl.inv.of_steps hsteps
        vregs := hvregs.trans hctrl.vregs
        spAligned := hctrl.spAligned }
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm htrm hctrl' hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem s3_block_to_call {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P0 A ext)
    (callee : BitVec 64) {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in)
    (hwp : SepWP (initProgExt img ext) callee s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .lr = initPcExt img ext k_out ∧ Φ sm))
    (hcont : ∀ sm : State,
      InInitiateExt img ext s0 sm ((sm.pc - initEntryExt img ext).toNat) →
      sm.pc = callee →
      sm.readReg64 .lr = initPcExt img ext k_out →
      sm.trace = s.trace →
      Φ sm →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := fun R hm hL => by
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hlrm, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (initProgExt_traceFsSound img hOk) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    have hctrl' := inInitiate_at_any_pc hctrl hrunm hsp hfp hx19 hfs_eq
      (hctrl.inv.of_steps hsteps) hvregs
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm hctrl' hpcm hlrm htrm hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem s3_dealloc {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext)
    (ptr : BitVec 64) (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntryExt img ext +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    (hlr : s.readReg64 .lr = initPcExt img ext k_out)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = 1)
    (hlay : LayoutOk sz 1)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ A.live ptr sz 1 ∗ memRegion ptr sz ∗ F)
    (hnext : ∀ sm : State,
      InInitiateExt img ext s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
      (ptr, sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [rustDeallocExternSpecWithStack, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hctrl.inv
      (Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩ (Entails.of_eq (by ac_rfl)))
  refine s3_call hOk (dealloc_ok_at_init hOk) (ptr, sz, 1) F hctrl htr hpc hlr hpanic hpre'
    ?_ ?_ ?_ ?_
  · intro _ _ h; simp only [rustDeallocExternSpecWithStack, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ _ h; simp only [rustDeallocExternSpecWithStack, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ h; simp only [rustDeallocExternSpecWithStack, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro sm _ _ _ hcsm _ hof
    simp only [rustDeallocExternSpecWithStack, Spec.inImage, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun htrm =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm htrm)

theorem oom_1918_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {S : RunSem} {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = initPcExt img ext 0x1918) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hext := panic_raw_vec_at_init img ext
  refine sepWP_bind_oom (mid := initEntryExt img ext +
    bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::raw_vec::handle_error")) ?_
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1918 12
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
    BitVec.ofNat_eq_ofNat] at hpc hext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPost_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

theorem oom_1930_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {S : RunSem} {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = initPcExt img ext 0x1930) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hext := panic_alloc_error_at_init img ext
  refine sepWP_bind_oom (mid := initEntryExt img ext +
    bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::alloc::handle_alloc_error")) ?_
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1930 12
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
    BitVec.ofNat_eq_ofNat] at hpc hext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPost_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

theorem oom_193c_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {S : RunSem} {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = initPcExt img ext 0x193c) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hext := panic_alloc_error_at_init img ext
  refine sepWP_bind_oom (mid := initEntryExt img ext +
    bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::alloc::handle_alloc_error")) ?_
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x193c 12
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
    BitVec.ofNat_eq_ofNat] at hpc hext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPost_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
