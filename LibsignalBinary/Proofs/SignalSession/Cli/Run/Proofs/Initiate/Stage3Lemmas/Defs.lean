/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs

/-!
# Stage 3 Call Combinators, Relative Targets, and Stack Split Helpers

Provides `SepWPp` stepping and call combinators (`s3_step_to`, `s3_call`, `s3_call_alloc`,
`s3_panic_at`), relative symbol target equivalences on `initProg img W`, stack sub-budget split
lemmas, and `CliExternsOk` counterparts (`Stage3Lemmas.Ext.*`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
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

/-! ## Function offset and relative call/hook targets -/

theorem cliInitiate_fnOff :
    libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") :=
  ls_lemma% fnOff "libsignal_cli_handshake::initiate"

theorem fnAddr_init_eq (img : Obj.Image) (W : CliHooks) {name : String} {off : Nat}
    (hoff : libsignalSessionCode.fnOff name = off) :
    (initProg img W).fnAddr name = img.base + BitVec.ofNat 64 off := by
  simp only [initProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, hoff]

theorem initEntry_eq (img : Obj.Image) (W : CliHooks) :
    initEntry img W =
      img.base + BitVec.ofNat 64 (num% (ls_off% "libsignal_cli_handshake::initiate")) :=
  fnAddr_init_eq img W cliInitiate_fnOff

theorem initPc_eq (img : Obj.Image) (W : CliHooks) (k : Nat) :
    initPc img W k =
      img.base + BitVec.ofNat 64 (num% (ls_off% "libsignal_cli_handshake::initiate")) +
        BitVec.ofNat 64 k := by
  simp only [initPc, initEntry_eq]

theorem coinsFill_fnAddr_eq (img : Obj.Image) (W : CliHooks) :
    initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill") =
      (initProg img W).fnAddr cliCoinsFillName := by
  rw [initEntry_eq, fnAddr_init_eq img W cliCoinsFill_fnOff]
  bv_omega

theorem calculateAgreement_fnAddr_eq (img : Obj.Image) (W : CliHooks) :
    initEntry img W -
        bv% (ls_rel% "<libsignal_core::curve::PrivateKey>::calculate_agreement"
          "libsignal_cli_handshake::initiate") =
      (initProg img W).fnAddr cliCalculateAgreementName := by
  rw [initEntry_eq, fnAddr_init_eq img W cliCalculateAgreement_fnOff]
  bv_omega

theorem kemCtSerialize_fnAddr_eq (img : Obj.Image) (W : CliHooks) :
    initEntry img W -
        bv% (ls_rel% "<libsignal_protocol::kem::Ciphertext>::serialize"
          "libsignal_cli_handshake::initiate") =
      (initProg img W).fnAddr cliKemCtSerializeName := by
  rw [initEntry_eq, fnAddr_init_eq img W cliKemCtSerialize_fnOff]
  bv_omega

theorem handshakeDerive_fnAddr_eq (img : Obj.Image) (W : CliHooks) :
    initEntry img W -
        bv% (ls_rel% "<libsignal_protocol::pqxdh::HandshakeKeys>::derive"
          "libsignal_cli_handshake::initiate") =
      (initProg img W).fnAddr cliHandshakeDeriveName := by
  rw [initEntry_eq, fnAddr_init_eq img W cliHandshakeDerive_fnOff]
  bv_omega

theorem shim_ok_at_init {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hh.alloc (name := cliInitiateName)
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (by rw [cliInitiate_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])

theorem alloc_ok_at_init {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hh.alloc (name := cliInitiateName)
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    (by rw [cliInitiate_fnOff, (ls_stub% "__rustc::__rust_alloc")])

theorem dealloc_ok_at_init {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hh.alloc (name := cliInitiateName)
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    (by rw [cliInitiate_fnOff, (ls_stub% "__rustc::__rust_dealloc")])

theorem memcpy_ok_at_init {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hh.alloc (name := cliInitiateName)
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    (by rw [cliInitiate_fnOff, (ls_stub% "memcpy")])

theorem kyberEncaps_row (W : CliHooks) :
    (Pqxdh.Initiator.kyberEncapsStub, CryptoVerification.E2E.kemEncapsHook W.Q.encaps) ∈
      cliHookTable W :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? (i := 8) rfl))

theorem kyberEncaps_ok_at_init (img : Obj.Image) (W : CliHooks) (X : UnreachedPqxdhPrimitives) :
    subroutine_ok (initProg img W)
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
      (Pqxdh.Initiator.kyberEncapsStubSpec
        (Pqxdh.Initiator.initiatorModelPrims X ⟨W.C, W.Q⟩)) :=
  hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExterns W)
    (name := cliInitiateName) (hname := Pqxdh.Initiator.kyberEncapsStub)
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
      "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
    (stub := num% (ls_off% "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
    cliInitiate_fnOff
    rfl
    (by decide)
    (ls_hook% "libcrux_ml_kem::mlkem1024::kyber::encapsulate")
    (by simp [Rust.isPanicSymbol, Pqxdh.Initiator.kyberEncapsStub])
    ⟨CryptoVerification.E2E.kemEncapsHook W.Q.encaps,
      cliExterns_row W (kyberEncaps_row W),
      Pqxdh.Initiator.kemEncapsHook_ok_initiatorModelPrims X ⟨W.C, W.Q⟩⟩

theorem panic_raw_vec_at_init (img : Obj.Image) (W : CliHooks) :
    (initProg img W).externAt?
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::raw_vec::handle_error")) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (b := img.base) (ext := cliExterns W) (name := cliInitiateName)
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::raw_vec::handle_error"))
    (by rw [cliInitiate_fnOff, (ls_stub% "alloc::raw_vec::handle_error")])

theorem panic_alloc_error_at_init (img : Obj.Image) (W : CliHooks) :
    (initProg img W).externAt?
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "alloc::alloc::handle_alloc_error")) =
      some Rust.panicked :=
  panic_at_panicSymbol (P := libsignalSessionCode) (b := img.base) (hooks := cliExterns W)
    (name := cliInitiateName) (hname := "alloc::alloc::handle_alloc_error")
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
      "alloc::alloc::handle_alloc_error"))
    (stub := num% (ls_off% "alloc::alloc::handle_alloc_error"))
    cliInitiate_fnOff
    rfl
    (by decide)
    (ls_hook% "alloc::alloc::handle_alloc_error")
    (by simp [Rust.isPanicSymbol])

/-! ## Frame alignment and `SepWPp` call combinators -/

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiate.spAligned_cur
    {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) : s.spAligned = true := by
  have h0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using h.spAligned
  simp only [State.spAligned, h.sp, cliInitiateFrame_eq, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiate.of_call
    {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W))
    {s0 s sm : State} {k_in k_out : Nat}
    (h : InInitiate img W s0 s k_in)
    (hsteps : Steps (initProg img W) s sm)
    (hpcm : sm.pc = initPc img W k_out)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s.sp)
    (hcsm : CalleeSavedPreserved s sm)
    (htrm : sm.trace = s.trace) :
    InInitiate img W s0 sm k_out := by
  rcases hcsm with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  have hfs_eq : sm.fs.files = s.fs.files :=
    TraceFsSound.files_eq hh.fs hsteps (evs := []) (by simpa using htrm) NoFsEv.nil
  exact
    { pc := hpcm
      run := hrunm
      sp := hspm.trans h.sp
      fp := hfp.trans h.fp
      x19 := hx19.trans h.x19
      files0 := hfs_eq.trans h.files0
      inv := h.inv.of_steps hsteps
      vregs := hvregs.trans h.vregs
      spAligned := h.spAligned }

theorem sepWPp_conseq_oom {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (h : P ⊢ P') (hw : SepWPp prog ret s P' Q Qp Qoom) :
    SepWPp prog ret s P Q Qp Qoom := fun R hm hL =>
  hw R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem sepWPp_pure_elim_oom {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (hw : φ → SepWPp prog ret s P Q Qp Qoom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp Qoom := fun R hm hL => by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hw hm.1 R hm.2 hL

theorem sepWPp_exists_elim_oom {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (hw : ∀ a, SepWPp prog ret s (P a) Q Qp Qoom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp Qoom := fun R hm hL => by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hma⟩ := hm
  exact hw a R hma hL

/-- Steps a trace-preserving basic block `s → mid` while lifting `ImgCallInv` and `fs.files` via `TraceFsSound`. -/
theorem s3_step_to {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W))
    {mid ret : BitVec 64} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP (initProg img W) mid s P (fun sm Pm =>
      sm.trace = s.trace ∧
      (ImgCallInv img sm → sm.fs.files = s.fs.files →
        SepWPp (initProg img W) ret sm Pm Q Qp (initOom s0)))) :
    SepWPp (initProg img W) ret s P Q Qp (initOom s0) := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, htrm, hnext⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq hh.fs hsteps (evs := []) (by simpa using htrm) NoFsEv.nil
    obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hinv.of_steps hsteps) hfs_eq R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem initPanicPost_of_allocFailed {A : RustAlloc} {img : Obj.Image} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sf : State} (Pf : SepProp)
    (h : allocFailedIn s0 sf) :
    InitPanicPost A img S x stk s0 sf Pf := by
  simp only [InitPanicPost, initSlotSpec, Spec.inImage]
  exact Entails.pure_right (Or.inr h) (ProofLib.entails_anyHeap Pf)

/-- `subroutine_ok` call combinator inside `initiate` for trace-preserving returns and `allocFailedIn` panics. -/
theorem s3_call {α : Type} {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hh : RunHooks img A (cliExterns W))
    {callee : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (initProg img W) callee spec)
    (g : α) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee)
    (hlr : s.readReg64 .lr = initPc img W k_out)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ spec.pre g s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic g s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit g code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom g s sm ∗ R'))
    (hnext : ∀ sm : State,
      sm.pc = initPc img W k_out → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (sm.trace = s.trace → InInitiate img W s0 sm k_out) →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm (spec.post g s sm ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  refine ProofLib.SepWPp.call_wpp_frozen (subroutine_ok_withStepsPost hcall) (x := g) (F := F)
    hctrl.inv.1 hctrl.inv.2 hpc hctrl.run (InInitiate.spAligned_cur hctrl) hlr
    (fun R hm => by rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun sf code R' _ hex => hexit_imp code sf R' hex)
    (fun sf _ ⟨R', hpan⟩ => by
      have halloc0 : allocFailedIn s0 sf := by
        simpa only [allocFailedIn, htr] using hpan_imp sf R' hpan
      exact hpanic sf _ (initPanicPost_of_allocFailed _ halloc0))
    (fun sm hpcm hrunm hspm hcsm hfz hsym => by
      dsimp only [withStepsPost, ReachesOutcome.withStepsPost]
      rw [sepConj_assoc]
      exact sepWPp_pure_elim_oom fun hsteps =>
        hnext sm hpcm hrunm hspm hcsm ⟨hfz, hsym⟩
          (InInitiate.of_call hh hctrl hsteps hpcm hrunm hspm hcsm))
    (fun sf R' _ hoom => (hoom_imp sf (F ∗ R') hoom).elim)

/-- `__rustc::__rust_alloc` call combinator handling the `allocFailedEvent` trace extension on null return. -/
theorem s3_call_alloc {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    (hh : RunHooks img A (cliExterns W))
    (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s k_in)
    (hpc : s.pc = initEntry img W +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    (hlr : s.readReg64 .lr = initPc img W k_out)
    (hx0 : (s.readReg64 .x0).toNat = sz)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : LayoutOk sz 1)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ F)
    (hnext_null : ∀ sm : State,
      sm.pc = initPc img W k_out → sm.status = .Running →
      sm.readReg64 .x0 = 0#64 →
      sm.trace = s.trace ++ [allocFailedEvent] →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0))
    (hnext_ok : ∀ sm : State,
      InInitiate img W s0 sm k_out →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 ≠ 0#64 →
      sm.trace = s.trace →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗
          A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have halloc := subroutine_ok_withStepsPost (alloc_ok_at_init hh)
  have hpre' : P ⊢ ((rustAllocSpecWithStack A extHookStack).inImage img).pre (sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [rustAllocSpecWithStack, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hctrl.inv (Entails.pure_right ⟨hx0, hx1, hlay⟩ (Entails.of_eq (by ac_rfl)))
  refine ProofLib.SepWPp.call_wpp_frozen halloc (x := (sz, 1)) (F := F)
    hctrl.inv.1 hctrl.inv.2 hpc hctrl.run (InInitiate.spAligned_cur hctrl) hlr
    (fun R hm => by rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hpre') hm)
    (fun _ _ _ _ hex => by
      simp only [rustAllocSpecWithStack, Spec.inImage] at hex
      exact not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hpan⟩ => by
      simp only [rustAllocSpecWithStack, Spec.inImage] at hpan
      exact (not_satisfies_false_sepConj hpan).elim)
    (fun sm hpcm hrunm hspm hcsm _ _ => by
      dsimp only [withStepsPost, ReachesOutcome.withStepsPost, rustAllocSpecWithStack, Spec.inImage]
      rw [sepConj_assoc]
      refine sepWPp_pure_elim_oom fun hsteps => ?_
      by_cases hnull : sm.readReg64 .x0 = 0
      · simp only [hnull, ↓reduceIte]
        refine sepWPp_conseq_oom (P' := ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗
          (A.pool ∗ stackAt s.sp extHookStack ∗ F)) (Entails.of_eq (by ac_rfl)) ?_
        exact sepWPp_pure_elim_oom fun htrm => hnext_null sm hpcm hrunm hnull htrm
      · simp only [hnull, ↓reduceIte]
        refine sepWPp_conseq_oom
          (P' := ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            (A.pool ∗ stackAt s.sp extHookStack ∗
              A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F))
          (Entails.of_eq (by ac_rfl)) ?_
        exact sepWPp_pure_elim_oom fun ⟨_, htrm⟩ =>
          hnext_ok sm (InInitiate.of_call hh hctrl hsteps hpcm hrunm hspm hcsm htrm) hcsm hnull htrm)
    (fun _ _ _ hoom => by
      simp only [rustAllocSpecWithStack, Spec.inImage] at hoom
      exact (not_satisfies_false_sepConj hoom).elim)

/-- Discharges `Rust.panicked` once `allocFailedIn s0 s` holds. -/
theorem s3_panic_at {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hext : (initProg img W).externAt? s.pc = some Rust.panicked)
    (hrun : s.status = .Running)
    (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) :=
  SepWPp.panic (P := P) (hrun := hrun) (hext := hext)
    (hqp := hpanic (Rust.panicked s) P
      (initPanicPost_of_allocFailed P
        (by simpa only [allocFailedIn, Rust.panicked] using hfail)))

/-! ## Stack sub-budget splits below `fsp` -/

theorem stackAt_sub_split_init (fsp : BitVec 64) {k m : Nat}
    (hle : k ≤ m) (hm : m ≤ 2 ^ 64) :
    stackAt fsp m = memRegion (fsp - BitVec.ofNat 64 m) (m - k) ∗ stackAt fsp k := by
  have heq : m = k + (m - k) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom fsp k (m - k) (by omega), ← heq]

theorem stk_sub_le_2pow64 {stk : Nat} (hstk64 : stk ≤ 2 ^ 63) :
    stk - cliInitiateFrame ≤ 2 ^ 64 := by omega

theorem stk_sub_le_2pow63 {stk : Nat} (hstk64 : stk ≤ 2 ^ 63) :
    stk - cliInitiateFrame ≤ 2 ^ 63 := by omega
theorem lay32 : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
theorem lay192 : LayoutOk 192 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
theorem lay1568 : LayoutOk 1568 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩

theorem s3_shim {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} (hh : RunHooks img A (cliExterns W)) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntry img W + bv% (ls_rel%
      "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (hlr : s.readReg64 .lr = initPc img W k_out)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiate img W s0 sm k_out → CalleeSavedPreserved s sm →
      sm.trace = s.trace → SepWPp (initProg img W) (s0.readReg64 .lr) sm
        (stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ (session2ShimSpecX.inImage img).pre () s ∗ F := Entails.trans hpre (by
    simp only [session2ShimSpecX, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hctrl.inv (Entails.refl _))
  refine s3_call hh (shim_ok_at_init hh) () F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [session2ShimSpecX, Spec.inImage] at h
  · intro _ _ _ h; simp [session2ShimSpecX, Spec.inImage] at h
  · intro _ _ h; simp [session2ShimSpecX, Spec.inImage] at h
  · intro sm _ _ _ hcsm _ hof; simp only [session2ShimSpecX, Spec.inImage, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun htrm =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm htrm)

theorem s3_memcpy {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} (hh : RunHooks img A (cliExterns W))
    (dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    (hlr : s.readReg64 .lr = initPc img W k_out)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiate img W s0 sm k_out → CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = dst → sm.trace = s.trace →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ (session2MemcpySpecX.inImage img).pre (dst, src, bs) s ∗ F := Entails.trans hpre (by
    simp only [session2MemcpySpecX, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hctrl.inv (Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.of_eq (by ac_rfl))))
  refine s3_call hh (memcpy_ok_at_init hh) (dst, src, bs) F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [session2MemcpySpecX, Spec.inImage] at h
  · intro _ _ _ h; simp [session2MemcpySpecX, Spec.inImage] at h
  · intro _ _ h; simp [session2MemcpySpecX, Spec.inImage] at h
  · intro sm _ _ _ hcsm _ hof; simp only [session2MemcpySpecX, Spec.inImage, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun ⟨hx0m, htrm⟩ =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm hx0m htrm)

/-! ## Extern-parameterized combinators (`InInitiateExt` and `Ext.*`) -/

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiateExt.spAligned_cur
    {img : Obj.Image} {ext : String → Option (State → State)} {s0 s : State} {k : Nat}
    (h : InInitiateExt img ext s0 s k) : s.spAligned = true := by
  have h0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using h.spAligned
  simp only [State.spAligned, h.sp, cliInitiateFrame_eq, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiateExt.of_call
    {img : Obj.Image} {P0 : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P0 A ext)
    {s0 s sm : State} {k_in k_out : Nat}
    (h : InInitiateExt img ext s0 s k_in)
    (hsteps : Steps (initProgExt img ext) s sm)
    (hpcm : sm.pc = initPcExt img ext k_out)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s.sp)
    (hcsm : CalleeSavedPreserved s sm)
    (htrm : sm.trace = s.trace) :
    InInitiateExt img ext s0 sm k_out := by
  rcases hcsm with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  have hfs_eq : sm.fs.files = s.fs.files :=
    TraceFsSound.files_eq (initProgExt_traceFsSound img hOk) hsteps (evs := [])
      (by simpa using htrm) NoFsEv.nil
  exact
    { pc := hpcm
      run := hrunm
      sp := hspm.trans h.sp
      fp := hfp.trans h.fp
      x19 := hx19.trans h.x19
      files0 := hfs_eq.trans h.files0
      inv := h.inv.of_steps hsteps
      vregs := hvregs.trans h.vregs
      spAligned := h.spAligned }

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiateExt.to_ctrlTuple
    {img : Obj.Image} {ext : String → Option (State → State)} {s0 s : State} {k : Nat}
    (h : InInitiateExt img ext s0 s k) :
    s.pc = initPcExt img ext k ∧ s.status = .Running ∧
      s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame ∧
      s.readReg64 .fp = s0.sp - 0x60#64 ∧
      s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
      s.fs.files = s0.fs.files ∧
      ImgCallInv img s ∧
      calleeSavedVRegs s = calleeSavedVRegs s0 ∧
      s0.spAligned = true :=
  ⟨h.pc, h.run, h.sp, h.fp, h.x19, h.files0, h.inv, h.vregs, h.spAligned⟩

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiateExt.of_ctrlTuple
    {img : Obj.Image} {ext : String → Option (State → State)} {s0 s : State} {k : Nat}
    (h : s.pc = initPcExt img ext k ∧ s.status = .Running ∧
      s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame ∧
      s.readReg64 .fp = s0.sp - 0x60#64 ∧
      s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
      s.fs.files = s0.fs.files ∧
      ImgCallInv img s ∧
      calleeSavedVRegs s = calleeSavedVRegs s0 ∧
      s0.spAligned = true) :
    InInitiateExt img ext s0 s k := by
  rcases h with ⟨hpc, hrun, hsp, hfp, hx19, hfiles, hinv, hvregs, hspA⟩
  exact ⟨hpc, hrun, hsp, hfp, hx19, hfiles, hinv, hvregs, hspA⟩

private theorem subroutine_ok_inImage_local {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) :=
  subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => by
    simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

namespace Ext

theorem fnAddr_init_eq (img : Obj.Image) (ext : String → Option (State → State))
    {name : String} {off : Nat} (hoff : libsignalSessionCode.fnOff name = off) :
    (initProgExt img ext).fnAddr name = img.base + BitVec.ofNat 64 off := by
  simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, hoff]

theorem initEntry_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    initEntryExt img ext =
      img.base + BitVec.ofNat 64 (num% (ls_off% "libsignal_cli_handshake::initiate")) :=
  fnAddr_init_eq img ext cliInitiate_fnOff

theorem initPc_eq (img : Obj.Image) (ext : String → Option (State → State)) (k : Nat) :
    initPcExt img ext k =
      img.base + BitVec.ofNat 64 (num% (ls_off% "libsignal_cli_handshake::initiate")) +
        BitVec.ofNat 64 k := by
  simp only [initPcExt, initEntry_eq]

theorem coinsFill_fnAddr_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill") =
      (initProgExt img ext).fnAddr cliCoinsFillName := by
  rw [initEntry_eq, fnAddr_init_eq img ext cliCoinsFill_fnOff]
  bv_omega

theorem calculateAgreement_fnAddr_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    initEntryExt img ext -
        bv% (ls_rel% "<libsignal_core::curve::PrivateKey>::calculate_agreement"
          "libsignal_cli_handshake::initiate") =
      (initProgExt img ext).fnAddr cliCalculateAgreementName := by
  rw [initEntry_eq, fnAddr_init_eq img ext cliCalculateAgreement_fnOff]
  bv_omega

theorem kemCtSerialize_fnAddr_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    initEntryExt img ext -
        bv% (ls_rel% "<libsignal_protocol::kem::Ciphertext>::serialize"
          "libsignal_cli_handshake::initiate") =
      (initProgExt img ext).fnAddr cliKemCtSerializeName := by
  rw [initEntry_eq, fnAddr_init_eq img ext cliKemCtSerialize_fnOff]
  bv_omega

theorem handshakeDerive_fnAddr_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    initEntryExt img ext -
        bv% (ls_rel% "<libsignal_protocol::pqxdh::HandshakeKeys>::derive"
          "libsignal_cli_handshake::initiate") =
      (initProgExt img ext).fnAddr cliHandshakeDeriveName := by
  rw [initEntry_eq, fnAddr_init_eq img ext cliHandshakeDerive_fnOff]
  bv_omega

theorem shim_ok_at_init {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (initProgExt img ext)
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (session2ShimSpecX.inImage img) := by
  have hraw : subroutine_ok (initProgExt img ext)
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      CliExt.shimSpec :=
    hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
      (name := cliInitiateName) (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
      (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (stub := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      cliInitiate_fnOff rfl (by decide)
      (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (by simp [Rust.isPanicSymbol])
      (hookSat_cliExternsWith
        (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
        hOk.shim)
  refine subroutine_ok_inImage_local img
    (subroutine_ok.of_codeLoaded fun u R s0 hpc hrun hpre hsp _ => ?_)
  have hpre' : s0.mem ⊨ CliExt.shimSpec.pre u s0 ∗ (stackAt s0.sp extHookStack ∗ R) := by
    simpa only [CliExt.shimSpec, session2ShimSpecX, emp_sepConj] using hpre
  refine hraw.mono_outcome u (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hsp ?_
  intro sf hout
  rcases hout with ⟨hc, hs, hpost⟩ | ⟨hp, hpost⟩ | ⟨c, he, hpost⟩ | ⟨ho, hpost⟩
  · exact Or.inl ⟨hc, hs, by simpa only [CliExt.shimSpec, session2ShimSpecX, sepConj_assoc] using hpost⟩
  · exact Or.inr (Or.inl ⟨hp, by simp [CliExt.shimSpec] at hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, by simp [CliExt.shimSpec] at hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, by simp [CliExt.shimSpec] at hpost⟩))

theorem alloc_ok_at_init {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (initProgExt img ext)
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) := by
  obtain ⟨f, hf, hok⟩ := hOk.alloc.alloc
  exact subroutine_ok_inImage_local img <|
    hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
      (name := cliInitiateName) (hname := allocName)
      (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
      (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
      (stub := num% (ls_off% "__rustc::__rust_alloc"))
      cliInitiate_fnOff rfl (by decide)
      (ls_hook% "__rustc::__rust_alloc")
      (by simp [Rust.isPanicSymbol, allocName])
      ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext
            (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, allocName])).trans hf,
       hookOk_rustAllocWithStack hok (by decide) (by decide)⟩

theorem dealloc_ok_at_init {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (initProgExt img ext)
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) := by
  obtain ⟨f, hf, hok⟩ := hOk.alloc.dealloc
  exact subroutine_ok_inImage_local img <|
    hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
      (name := cliInitiateName) (hname := deallocName)
      (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
      (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      (stub := num% (ls_off% "__rustc::__rust_dealloc"))
      cliInitiate_fnOff rfl (by decide)
      (ls_hook% "__rustc::__rust_dealloc")
      (by simp [Rust.isPanicSymbol, deallocName])
      ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext
            (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, deallocName])).trans hf,
       hookOk_rustDeallocExternWithStack hok (by decide) (by decide)⟩

theorem memcpy_raw_ok_at_init {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (initProgExt img ext)
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      CliExt.memcpySpec :=
  hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := "memcpy")
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    (stub := num% (ls_off% "memcpy"))
    cliInitiate_fnOff rfl (by decide)
    (ls_hook% "memcpy")
    (by simp [Rust.isPanicSymbol])
    (hookSat_cliExternsWith
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
      hOk.memcpy)

theorem memcpy_ok_at_init {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (initProgExt img ext)
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      (session2MemcpySpecX.inImage img) := by
  have hraw := memcpy_raw_ok_at_init hOk (img := img)
  refine subroutine_ok_inImage_local img
    (subroutine_ok.of_codeLoaded fun (dst, src, bs) R s0 hpc hrun hpre hsp _ => ?_)
  have hsplit := stackAt_sub_split_init s0.sp
    (by decide : CliExt.memHookStack ≤ extHookStack) (by decide : extHookStack ≤ 2 ^ 64)
  let tail := memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - CliExt.memHookStack)
  have hpre' : s0.mem ⊨ CliExt.memcpySpec.pre (dst, src, bs) s0 ∗ (tail ∗ R) := by
    dsimp only [session2MemcpySpecX] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
    rw [hsplit] at hmem
    dsimp only [CliExt.memcpySpec, libcMemcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq ?_) hmem⟩
    dsimp only [tail]; sep_ac_rfl
  refine hraw.mono_outcome (dst, src, bs) (tail ∗ R) s0 hpc hrun hpre' hsp ?_
  intro sf hout
  rcases hout with ⟨hc, hs, hpost⟩ | ⟨hp, hpost⟩ | ⟨c, he, hpost⟩ | ⟨ho, hpost⟩
  · refine Or.inl ⟨hc, hs, ?_⟩
    dsimp only [session2MemcpySpecX]
    rw [hsplit]
    refine Satisfies.mono (Entails.of_eq ?_) hpost
    dsimp only [CliExt.memcpySpec, tail]
    sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hp, by simp [CliExt.memcpySpec] at hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, by simp [CliExt.memcpySpec] at hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, by simp [CliExt.memcpySpec] at hpost⟩))

theorem kemEncaps_raw_ok_at_init {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (initProgExt img ext)
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
      (CliExt.kemEncapsSpec P0.Q) :=
  hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := E2E.kemEncapsName)
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
      "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
    (stub := num% (ls_off% "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
    cliInitiate_fnOff rfl (by decide)
    (ls_hook% "libcrux_ml_kem::mlkem1024::kyber::encapsulate")
    (by simp [Rust.isPanicSymbol, E2E.kemEncapsName])
    (hookSat_cliExternsWith
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, E2E.kemEncapsName])
      hOk.kemEncaps)

theorem kemEncaps_ok_at_init {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (initProgExt img ext)
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "libcrux_ml_kem::mlkem1024::kyber::encapsulate"))
      ((CliExt.kemEncapsSpec P0.Q).inImage img) :=
  subroutine_ok_inImage_local img (kemEncaps_raw_ok_at_init hOk)

theorem panic_raw_vec_at_init (img : Obj.Image) (ext : String → Option (State → State)) :
    (initProgExt img ext).externAt?
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::raw_vec::handle_error")) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (b := img.base) (ext := cliExternsWith ext) (name := cliInitiateName)
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::raw_vec::handle_error"))
    (by rw [cliInitiate_fnOff, (ls_stub% "alloc::raw_vec::handle_error")])

theorem panic_alloc_error_at_init (img : Obj.Image) (ext : String → Option (State → State)) :
    (initProgExt img ext).externAt?
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "alloc::alloc::handle_alloc_error")) =
      some Rust.panicked :=
  panic_at_panicSymbol (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := "alloc::alloc::handle_alloc_error")
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
      "alloc::alloc::handle_alloc_error"))
    (stub := num% (ls_off% "alloc::alloc::handle_alloc_error"))
    cliInitiate_fnOff rfl (by decide)
    (ls_hook% "alloc::alloc::handle_alloc_error")
    (by simp [Rust.isPanicSymbol])

theorem s3_step_to {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P0 A ext)
    {mid ret : BitVec 64} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP (initProgExt img ext) mid s P (fun sm Pm =>
      sm.trace = s.trace ∧
      (ImgCallInv img sm → sm.fs.files = s.fs.files →
        SepWPp (initProgExt img ext) ret sm Pm Q Qp (initOom s0)))) :
    SepWPp (initProgExt img ext) ret s P Q Qp (initOom s0) := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, htrm, hnext⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (initProgExt_traceFsSound img hOk) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hinv.of_steps hsteps) hfs_eq R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem s3_call {α : Type} {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext)
    {callee : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (initProgExt img ext) callee spec)
    (g : α) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee)
    (hlr : s.readReg64 .lr = initPcExt img ext k_out)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ spec.pre g s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic g s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit g code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom g s sm ∗ R'))
    (hnext : ∀ sm : State,
      sm.pc = initPcExt img ext k_out → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (sm.trace = s.trace → InInitiateExt img ext s0 sm k_out) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm (spec.post g s sm ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  refine ProofLib.SepWPp.call_wpp_frozen (subroutine_ok_withStepsPost hcall) (x := g) (F := F)
    hctrl.inv.1 hctrl.inv.2 hpc hctrl.run (InInitiateExt.spAligned_cur hctrl) hlr
    (fun R hm => by rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun sf code R' _ hex => hexit_imp code sf R' hex)
    (fun sf _ ⟨R', hpan⟩ => by
      have halloc0 : allocFailedIn s0 sf := by
        simpa only [allocFailedIn, htr] using hpan_imp sf R' hpan
      exact hpanic sf _ (initPanicPost_of_allocFailed _ halloc0))
    (fun sm hpcm hrunm hspm hcsm hfz hsym => by
      dsimp only [withStepsPost, ReachesOutcome.withStepsPost]
      rw [sepConj_assoc]
      exact sepWPp_pure_elim_oom fun hsteps =>
        hnext sm hpcm hrunm hspm hcsm ⟨hfz, hsym⟩
          (InInitiateExt.of_call hOk hctrl hsteps hpcm hrunm hspm hcsm))
    (fun sf R' _ hoom => (hoom_imp sf (F ∗ R') hoom).elim)

theorem s3_call_alloc {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P0 A ext)
    (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in)
    (hpc : s.pc = initEntryExt img ext +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    (hlr : s.readReg64 .lr = initPcExt img ext k_out)
    (hx0 : (s.readReg64 .x0).toNat = sz)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : LayoutOk sz 1)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ F)
    (hnext_null : ∀ sm : State,
      sm.pc = initPcExt img ext k_out → sm.status = .Running →
      sm.readReg64 .x0 = 0#64 →
      sm.trace = s.trace ++ [allocFailedEvent] →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0))
    (hnext_ok : ∀ sm : State,
      InInitiateExt img ext s0 sm k_out →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 ≠ 0#64 →
      sm.trace = s.trace →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗
          A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have halloc := subroutine_ok_withStepsPost (alloc_ok_at_init hOk (img := img))
  have hpre' : P ⊢ ((rustAllocSpecWithStack A extHookStack).inImage img).pre (sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [rustAllocSpecWithStack, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hctrl.inv (Entails.pure_right ⟨hx0, hx1, hlay⟩ (Entails.of_eq (by ac_rfl)))
  refine ProofLib.SepWPp.call_wpp_frozen halloc (x := (sz, 1)) (F := F)
    hctrl.inv.1 hctrl.inv.2 hpc hctrl.run (InInitiateExt.spAligned_cur hctrl) hlr
    (fun R hm => by rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hpre') hm)
    (fun _ _ _ _ hex => by
      simp only [rustAllocSpecWithStack, Spec.inImage] at hex
      exact not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hpan⟩ => by
      simp only [rustAllocSpecWithStack, Spec.inImage] at hpan
      exact (not_satisfies_false_sepConj hpan).elim)
    (fun sm hpcm hrunm hspm hcsm _ _ => by
      dsimp only [withStepsPost, ReachesOutcome.withStepsPost, rustAllocSpecWithStack, Spec.inImage]
      rw [sepConj_assoc]
      refine sepWPp_pure_elim_oom fun hsteps => ?_
      by_cases hnull : sm.readReg64 .x0 = 0
      · simp only [hnull, ↓reduceIte]
        refine sepWPp_conseq_oom (P' := ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗
          (A.pool ∗ stackAt s.sp extHookStack ∗ F)) (Entails.of_eq (by ac_rfl)) ?_
        exact sepWPp_pure_elim_oom fun htrm => hnext_null sm hpcm hrunm hnull htrm
      · simp only [hnull, ↓reduceIte]
        refine sepWPp_conseq_oom
          (P' := ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            (A.pool ∗ stackAt s.sp extHookStack ∗
              A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F))
          (Entails.of_eq (by ac_rfl)) ?_
        exact sepWPp_pure_elim_oom fun ⟨_, htrm⟩ =>
          hnext_ok sm (InInitiateExt.of_call hOk hctrl hsteps hpcm hrunm hspm hcsm htrm) hcsm hnull htrm)
    (fun _ _ _ hoom => by
      simp only [rustAllocSpecWithStack, Spec.inImage] at hoom
      exact (not_satisfies_false_sepConj hoom).elim)

theorem s3_panic_at {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {S : RunSem} {x : InitGhost} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hext : (initProgExt img ext).externAt? s.pc = some Rust.panicked)
    (hrun : s.status = .Running)
    (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) :=
  SepWPp.panic (P := P) (hrun := hrun) (hext := hext)
    (hqp := hpanic (Rust.panicked s) P
      (initPanicPost_of_allocFailed P
        (by simpa only [allocFailedIn, Rust.panicked] using hfail)))

theorem s3_shim {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat} (hOk : CliExternsOk P0 A ext) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntryExt img ext + bv% (ls_rel%
      "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (hlr : s.readReg64 .lr = initPcExt img ext k_out)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiateExt img ext s0 sm k_out → CalleeSavedPreserved s sm →
      sm.trace = s.trace → SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
        (stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ (session2ShimSpecX.inImage img).pre () s ∗ F := Entails.trans hpre (by
    simp only [session2ShimSpecX, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hctrl.inv (Entails.refl _))
  refine s3_call hOk (shim_ok_at_init hOk) () F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [session2ShimSpecX, Spec.inImage] at h
  · intro _ _ _ h; simp [session2ShimSpecX, Spec.inImage] at h
  · intro _ _ h; simp [session2ShimSpecX, Spec.inImage] at h
  · intro sm _ _ _ hcsm _ hof; simp only [session2ShimSpecX, Spec.inImage, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun htrm =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm htrm)

theorem s3_memcpy {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat} (hOk : CliExternsOk P0 A ext)
    (dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    (hlr : s.readReg64 .lr = initPcExt img ext k_out)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiateExt img ext s0 sm k_out → CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = dst → sm.trace = s.trace →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ (session2MemcpySpecX.inImage img).pre (dst, src, bs) s ∗ F := Entails.trans hpre (by
    simp only [session2MemcpySpecX, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hctrl.inv (Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.of_eq (by ac_rfl))))
  refine s3_call hOk (memcpy_ok_at_init hOk) (dst, src, bs) F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [session2MemcpySpecX, Spec.inImage] at h
  · intro _ _ _ h; simp [session2MemcpySpecX, Spec.inImage] at h
  · intro _ _ h; simp [session2MemcpySpecX, Spec.inImage] at h
  · intro sm _ _ _ hcsm _ hof; simp only [session2MemcpySpecX, Spec.inImage, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun ⟨hx0m, htrm⟩ =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm hx0m htrm)

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
