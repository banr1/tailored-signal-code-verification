/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Hops
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout

/-!
# Shared Call, Stack-Frame, and Semantic Helpers for Arm `R1b`

Symbol offsets, stack-budget bounds, generic `SepWPp` call/deallocation/`SignalProtocolError`-drop
combinators, `runLocals` (`0x29f0` B) focusing helpers, and bundle-path reject lemmas for Arm `R1b`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-! ## Symbol Offsets, Vtable Equations, and Callee Lemmas -/

theorem r1b_run_fnOff :
    libsignalSessionCode.fnOff runName = num% (ls_off% "libsignal_cli::run") :=
  MainHops.run_fnOff

theorem r1b_run_fnAddr_rel {img : Obj.Image} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff runName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (mProg img ext).fnAddr runName + off = (mProg img ext).fnAddr target := by
  simp only [mProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

private theorem r1b_shim_fnOff :
    libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" =
      num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") :=
  ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2"

theorem r1b_shimFs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_cli::run"))
      ((withStack sessionShimSpec extHookStack).keepsFs.inImage img) :=
  hh.allocFs.shim_ok_at runName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "libsignal_cli::run"))
    (hk := by rw [r1b_run_fnOff, r1b_shim_fnOff])

theorem r1b_allocFs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli::run"))
      ((rustAllocSpecWithStack A extHookStack).keepsFs.inImage img) :=
  hh.allocFs.alloc_ok_at runName
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli::run"))
    (by rw [r1b_run_fnOff, MainHops.rustAlloc_fnOff])

theorem r1b_deallocFs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run"))
      ((rustDeallocExternSpecWithStack A extHookStack).keepsFs.inImage img) :=
  hh.allocFs.dealloc_ok_at runName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run"))
    (by rw [r1b_run_fnOff, MainHops.rustDealloc_fnOff])

theorem r1b_memcpyFs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% (ls_off% "memcpy" - ls_off% "libsignal_cli::run"))
      ((sessionMemcpySpec extHookStack).keepsFs.inImage img) :=
  hh.allocFs.session_memcpy_ok_at runName
    (num% (ls_off% "memcpy" - ls_off% "libsignal_cli::run"))
    (hk := by rw [r1b_run_fnOff, MainHops.memcpyCallee_fnOff])

theorem r1b_panic_handle_error (img : Obj.Image) (ext : String → Option (State → State)) :
    (mProg img ext).externAt?
      ((mProg img ext).fnAddr runName +
        bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::run")) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (b := img.base) (ext := ext) (name := runName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::run"))
    (by rw [r1b_run_fnOff, MainHops.handleError_fnOff])

private theorem r1b_pkDeserialize_fnOff :
    libsignalSessionCode.fnOff "<libsignal_core::curve::PublicKey>::deserialize" =
      num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize") :=
  ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize"

private theorem r1b_kemDeserialize_fnOff :
    libsignalSessionCode.fnOff RunSkeleton.kemDeserializeName =
      num% (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize")

theorem r1b_path_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) {stk : Nat} (hstk : pathNeed ≤ stk) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 + ls_off% "libsignal_cli::stores::path" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      (pathSpec A img stk) := by
  rw [r1b_run_fnAddr_rel (target := pathName) (by rw [r1b_run_fnOff, path_fnOff]; decide)]
  exact Path.path_ok_of_deps_roX hh.alloc
    (SpqrV1.Alloc.memcpyROOkExtX_of_hookSat_withStack (Nat.le_refl _) hh.memcpyRO_X)
    (reserve_ok_ext hh (Nat.le_refl _)) hstk (base_aligned himg)

theorem r1b_readFile_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {σ : RunSlots}
    (hc : RunCallees img A ext B σ) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 + ls_off% "libsignal_cli_io::read_file" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      (readFileSpec cliIo.rd cliWrOk A img B.readFile) := by
  rw [r1b_run_fnAddr_rel (target := readFileName) (by rw [r1b_run_fnOff, readFile_fnOff]; decide)]
  exact hc.readFile

theorem r1b_bundleRead_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {σ : RunSlots}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B σ)
    {stk : Nat} (hstk : B.bundleReadNeed ≤ stk) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 + ls_off% "libsignal_cli::public::read_bundle::{closure#0}" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      (bundleReadSpec cliIo.rd cliWrOk A img stk) := by
  rw [r1b_run_fnAddr_rel (target := bundleReadName)
    (by rw [r1b_run_fnOff, bundleRead_fnOff]; decide)]
  exact RunSkeleton.bundleRead_ok_of_path_ext himg hh
    (Path.path_ok_of_deps_roX hh.alloc
      (SpqrV1.Alloc.memcpyROOkExtX_of_hookSat_withStack (Nat.le_refl _) hh.memcpyRO_X)
      (reserve_ok_ext hh (Nat.le_refl _)) (Nat.le_refl _) (base_aligned himg))
    hc hstk

theorem r1b_splitSigned_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    {stk : Nat} (hstk : splitSignedNeed ≤ stk) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 + ls_off% "libsignal_cli::public::split_signed" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      (splitSignedSpec A img stk) := by
  rw [r1b_run_fnAddr_rel (target := splitSignedName)
    (by rw [r1b_run_fnOff, splitSigned_fnOff]; decide)]
  exact RunSkeleton.splitSigned_ok_ext himg hh hstk

theorem r1b_splitId_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    {stk : Nat} (hstk : splitIdNeed ≤ stk) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 + ls_off% "libsignal_cli::public::split_id" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      (splitIdSpec A img stk) := by
  rw [r1b_run_fnAddr_rel (target := splitIdName)
    (by rw [r1b_run_fnOff, splitId_fnOff]; decide)]
  exact RunSkeleton.splitId_ok_ext himg hh hstk

theorem r1b_pkDeserializeFull_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::deserialize" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      ((CryptoVerification.LibsignalTripleRatchet.Wire.deserializeFullSpec img.base).inImage
        img) := by
  rw [r1b_run_fnAddr_rel (target := "<libsignal_core::curve::PublicKey>::deserialize")
    (by rw [r1b_run_fnOff, r1b_pkDeserialize_fnOff]; decide)]
  exact RunSkeleton.pkDeserializeFull_ok img ext

theorem r1b_kemDeserialize_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    {stk : Nat} (hstk : 48 + extHookStack ≤ stk) (hstk63 : stk ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 +
          ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      ((RunProofs.cliKemDeserializeSpec A stk).inImage img) := by
  rw [r1b_run_fnAddr_rel (target := RunSkeleton.kemDeserializeName)
    (by rw [r1b_run_fnOff, r1b_kemDeserialize_fnOff]; decide)]
  exact hc.kemDeserialize stk hstk hstk63

theorem r1b_tryAllocateIn3_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hh : RunHooksExt img A ext)
    {stk : Nat} (hstk : finishGrowStackX ≤ stk) (hstk63 : stk ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      ((tryAllocateInSpecOf stk A).keepsFs.inImage img) := by
  rw [r1b_run_fnAddr_rel (target := tryAllocateIn3Name)
    (by rw [r1b_run_fnOff, MainHops.tryAllocateIn3_fnOff]; decide)]
  exact RunSkeleton.runTryAllocateIn3_ok_ext hh stk hstk hstk63

theorem r1b_dropSpeOwned_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    {stk : Nat} (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% ((2 ^ 64 +
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" -
          ls_off% "libsignal_cli::run") % 2 ^ 64))
      ((RunDrop.dropSpeOwnedSpec A stk).inImage img) := by
  rw [r1b_run_fnAddr_rel (target := cliDropSpeName)
    (by rw [r1b_run_fnOff, cliDropSpe_fnOff]; decide)]
  exact hdrop stk hstk hstk64

/-! ## Stack-Budget Bounds -/

structure r1b_StackBounds (B : RunBudgets) (resStack : Nat) : Prop where
  frame : runFrame ≤ resStack
  sub63 : resStack - runFrame ≤ 2 ^ 63
  sub64 : resStack - runFrame ≤ 2 ^ 64
  tryAlloc : finishGrowStackX ≤ resStack - runFrame
  readFile : B.readFile ≤ resStack - runFrame
  path : pathNeed ≤ resStack - runFrame
  bundleRead : B.bundleReadNeed ≤ resStack - runFrame
  splitId : splitIdNeed ≤ resStack - runFrame
  splitSigned : splitSignedNeed ≤ resStack - runFrame
  dropSpe : 32 + extHookStack ≤ resStack - runFrame
  hook : extHookStack ≤ resStack - runFrame
  kem : 48 + extHookStack ≤ resStack - runFrame

theorem r1b_stackBounds_of {A : RustAlloc} {img : Obj.Image} {B : RunBudgets} {S : RunSem}
    {needs : RunNeeds} {resStack : Nat}
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack) (hres63 : resStack ≤ 2 ^ 63) :
    r1b_StackBounds B resStack := by
  have hb := runNeed_bounds hres hres63
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## Generic `SepWPp` Call, Deallocation, and Panic Helpers -/

theorem r1b_files_eq_of_trace_eq {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hh : RunHooksExt img A ext)
    {s sf : State} (hsteps : Steps (mProg img ext) s sf)
    (htr : sf.trace = s.trace) :
    sf.fs.files = s.fs.files :=
  hh.fs.files_eq hsteps (by simp [htr] : sf.trace = s.trace ++ []) NoFsEv.nil

theorem r1b_stdout_eq_of_trace_eq {s sf : State}
    (htr : sf.trace = s.trace)
    (hout : Arm64.Process.ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    Arm64.Process.ProcessOutcome.traceStreamBytes .stdout sf.trace = [] := by
  rwa [htr]

/-- Invokes a `subroutine_ok` callee incorporating `ImgCallInv`, forwarding `Steps`, `ImgCallInv`, `sp`, and `CalleeSavedPreserved` while routing allocation panics to `Qp`/`runOom`. -/
theorem r1b_call {α : Type} {img : Obj.Image} {ext : String → Option (State → State)}
    {callee ret_pc ret : BitVec 64} {spec : Spec α} {g : RunCall} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok (mProg img ext) callee spec)
    (hinv : ImgCallInv img s)
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
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      Steps (mProg img ext) s sf →
      ImgCallInv img sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp (mProg img ext) ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp (mProg img ext) ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    have h1 := Satisfies.mono (sepConj_mono_left hP) hm
    simpa only [sepConj_emp, sepConj_assoc] using h1
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm_pre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_steps hsteps) hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanicK sm _ (hpanic sm (F ∗ R) hpan hpost)⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

theorem r1b_spAligned_of_fsp {s0 s : State}
    (hsp : s.sp = runFsp s0)
    (hsp0 : s0.spAligned = true) :
    s.spAligned = true := by
  have hs0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using hsp0
  have hfsp : (s0.sp - 0x2a50#64) &&& 15#64 = 0#64 := by
    bv_bits
  simp only [State.spAligned, hsp, runFsp, hfsp, beq_self_eq_true]

/-- Discharges a `bl alloc::raw_vec::handle_error` panic site given `allocFailedIn s0 s`. -/
theorem r1b_handle_error_panic {img : Obj.Image} {ext : String → Option (State → State)}
    {ret : BitVec 64} {g : RunCall} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (mProg img ext).fnAddr runName +
      bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli::run"))
    (hrun : s.status = .Running)
    (hpanicK : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (mProg img ext) ret s P Q Qp (runOom s0) := by
  intro R hm _
  let s1 := Rust.panicked s
  have hstep : Step (mProg img ext) s s1 :=
    Step.extern hrun (hpc ▸ r1b_panic_handle_error img ext) (Memory.KeepsFrozen.refl s.mem) rfl
  exact ⟨s1, Steps.step hstep (Steps.refl s1), Or.inr (Or.inl ⟨rfl, P, hm,
    hpanicK s1 P (Or.inr hfail)⟩)⟩

/-- Invokes `__rust_dealloc(ptr, cap.toNat, 1)` on `ownedBytes` when `cap ≠ 0`, preserving `InRun`, `CalleeSavedPreserved`, `fs`, and `trace`. -/
theorem r1b_call_dealloc_ownedBytes {img : Obj.Image} {ext : String → Option (State → State)}
    {A : RustAlloc} {B : RunBudgets} {g : RunCall} {s0 st_bl : State}
    {resStack retOff : Nat}
    {cap ptr len : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run"))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : st_bl.readReg64 .x1 = cap)
    (hx2 : st_bl.readReg64 .x2 = 1#64)
    (hcap : cap ≠ 0#64)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (ownedBytes A cap ptr len bs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  rw [M3Helpers.ownedBytes_pure A cap ptr len bs, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, _, hlt_cap, _⟩ => ?_
  set fsp := runFsp s0
  refine r1b_call (ptr, cap.toNat, 1) (r1b_deallocFs_ok hh) hinv hpc hrun hal_bl hlr hpanicK
    (F := memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
      (resStack - runFrame - extHookStack) ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.inImage, Spec.keepsFs, rustDeallocExternSpecWithStack]
    have hpure : st_bl.readReg64 .x0 = ptr ∧ (st_bl.readReg64 .x1).toNat = cap.toNat ∧
        (st_bl.readReg64 .x2).toNat = 1 ∧ LayoutOk cap.toNat 1 := by
      refine ⟨hx0, by rw [hx1], by rw [hx2]; decide,
        ⟨Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq (by simpa using h0)),
          ⟨0, rfl⟩, by omega⟩⟩
    rw [hsp]
    change ownedBytes A cap ptr len bs ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ F ⊢ _
    rw [BundleRead.Helpers.stackAt_split_sub fsp (resStack - runFrame) extHookStack
      hbnd.hook hbnd.sub64]
    refine Entails.trans (sepConj_mono_left (M3Helpers.ownedBytes_to_dealloc A hcap)) ?_
    conv => rhs; rw [sepConj_assoc, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hinv
    apply Entails.pure_right hpure
    exact Entails.of_eq (by ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    refine MainHops.sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfs_f htr_f)
    rw [hsp, BundleRead.Helpers.stackAt_split_sub fsp (resStack - runFrame) extHookStack
      hbnd.hook hbnd.sub64]
    exact Entails.of_eq (by ac_rfl)

/-- Invokes `drop_glue::<SignalProtocolError>` on `speOwnedAt`, returning `memRegion a 48` and preserving `InRun`, `CalleeSavedPreserved`, `fs.files`, and `trace`. -/
theorem r1b_call_dropSpeOwned {img : Obj.Image} {ext : String → Option (State → State)}
    {A : RustAlloc} {B : RunBudgets} {g : RunCall} {s0 st_bl : State}
    {resStack retOff : Nat}
    {a : BitVec 64} {k : RunDrop.SpeOwned} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 +
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = a)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (memRegion a 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (RunDrop.speOwnedAt A a k ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call ⟨a, k⟩ (r1b_dropSpeOwned_ok hdrop hbnd.dropSpe hbnd.sub64)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [Spec.inImage, RunDrop.dropSpeOwnedSpec]
    rw [hsp]
    conv => rhs; rw [sepConj_assoc, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hinv
    apply Entails.pure_right hx0
    exact Entails.of_eq (by ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, RunDrop.dropSpeOwnedSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq hh hsteps htr_f
    refine MainHops.sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfiles_f htr_f)
    rw [hsp]
    exact Entails.of_eq (by ac_rfl)

/-! ## `runLocals` (`0x29f0` B) Focusing and Update Helpers -/

def r1b_localsBound : List (Nat × Nat × SepProp) → Nat
  | [] => runLocalBytes
  | (o, _, _) :: _ => o

def r1b_localsEnd (off : Nat) : List (Nat × Nat × SepProp) → Nat
  | [] => off
  | (o, n, _) :: cs => r1b_localsEnd (o + n) cs

def r1b_localsCtx (fsp : BitVec 64) :
    Nat → List (Nat × Nat × SepProp) → Nat → Nat → List (Nat × Nat × SepProp) → SepProp
  | off, [], o, n, cs₂ =>
    memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ runLocalsFrom fsp (o + n) cs₂
  | off, (o₁, n₁, P₁) :: cs₁, o, n, cs₂ =>
    memRegion (fsp + BitVec.ofNat 64 off) (o₁ - off) ∗ P₁ ∗
      r1b_localsCtx fsp (o₁ + n₁) cs₁ o n cs₂

theorem r1b_localsFrom_focus (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp)
    (cs₂ : List (Nat × Nat × SepProp)) :
    runLocalsFrom fsp off (cs₁ ++ (o, n, P) :: cs₂) =
      P ∗ r1b_localsCtx fsp off cs₁ o n cs₂ := by
  induction cs₁ generalizing off with
  | nil =>
    simp only [List.nil_append, runLocalsFrom, r1b_localsCtx]
    ac_rfl
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, runLocalsFrom, r1b_localsCtx, ih (o₁ + n₁)]
    ac_rfl

theorem r1b_locals_focus (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp)
    (cs₂ : List (Nat × Nat × SepProp)) :
    runLocals fsp (cs₁ ++ (o, n, P) :: cs₂) =
      P ∗ r1b_localsCtx fsp 0 cs₁ o n cs₂ :=
  r1b_localsFrom_focus fsp 0 cs₁ o n P cs₂

theorem r1b_locals_mono_piece (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) {P Q : SepProp}
    (cs₂ : List (Nat × Nat × SepProp)) (hPQ : P ⊢ Q) :
    runLocals fsp (cs₁ ++ (o, n, P) :: cs₂) ⊢
      runLocals fsp (cs₁ ++ (o, n, Q) :: cs₂) := by
  rw [r1b_locals_focus fsp cs₁ o n P cs₂, r1b_locals_focus fsp cs₁ o n Q cs₂]
  exact sepConj_mono_left hPQ

theorem r1b_localsFrom_carve_region (fsp : BitVec 64) (off o n : Nat)
    (cs : List (Nat × Nat × SepProp))
    (hlo : off ≤ o)
    (hhi : o + n ≤ r1b_localsBound cs)
    (hbnd : r1b_localsBound cs ≤ runLocalBytes) :
    runLocalsFrom fsp off cs =
      runLocalsFrom fsp off ((o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs) := by
  have hrlb : runLocalBytes = 0x29f0 := rfl
  have hsplit1 :
      memRegion (fsp + BitVec.ofNat 64 off) (r1b_localsBound cs - off) =
        memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗
          memRegion (fsp + BitVec.ofNat 64 o) (r1b_localsBound cs - o) := by
    refine ProofLib.memRegion_split' (n := o - off) (k := r1b_localsBound cs - o)
      (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hsplit2 :
      memRegion (fsp + BitVec.ofNat 64 o) (r1b_localsBound cs - o) =
        memRegion (fsp + BitVec.ofNat 64 o) n ∗
          memRegion (fsp + BitVec.ofNat 64 (o + n)) (r1b_localsBound cs - (o + n)) := by
    refine ProofLib.memRegion_split' (n := n) (k := r1b_localsBound cs - (o + n))
      (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  cases cs with
  | nil =>
    simp only [r1b_localsBound] at hhi hbnd hsplit1 hsplit2
    simp only [runLocalsFrom, hsplit1, hsplit2]
  | cons c cs' =>
    rcases c with ⟨o', n', P'⟩
    simp only [r1b_localsBound] at hhi hbnd hsplit1 hsplit2
    simp only [runLocalsFrom, hsplit1, hsplit2]
    ac_rfl

private theorem r1b_localsFrom_carve_after (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1b_localsEnd off cs₁ ≤ o)
    (hhi : o + n ≤ r1b_localsBound cs₂)
    (hbnd : r1b_localsBound cs₂ ≤ runLocalBytes) :
    runLocalsFrom fsp off (cs₁ ++ cs₂) =
      runLocalsFrom fsp off (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) := by
  induction cs₁ generalizing off with
  | nil =>
    exact r1b_localsFrom_carve_region fsp off o n cs₂ hlo hhi hbnd
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, runLocalsFrom]
    rw [ih (o₁ + n₁) hlo]

theorem r1b_locals_carve_region (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1b_localsEnd 0 cs₁ ≤ o := by simp [r1b_localsEnd, MainHops.cell])
    (hhi : o + n ≤ r1b_localsBound cs₂ := by simp [r1b_localsBound, MainHops.cell, runLocalBytes])
    (hbnd : r1b_localsBound cs₂ ≤ runLocalBytes := by
      simp [r1b_localsBound, MainHops.cell, runLocalBytes]) :
    runLocals fsp (cs₁ ++ cs₂) =
      runLocals fsp (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) :=
  r1b_localsFrom_carve_after fsp 0 cs₁ o n cs₂ hlo hhi hbnd

theorem r1b_locals_carve_cell (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1b_localsEnd 0 cs₁ ≤ o := by simp [r1b_localsEnd, MainHops.cell])
    (hhi : o + 8 ≤ r1b_localsBound cs₂ := by simp [r1b_localsBound, MainHops.cell, runLocalBytes])
    (hbnd : r1b_localsBound cs₂ ≤ runLocalBytes := by
      simp [r1b_localsBound, MainHops.cell, runLocalBytes]) :
    runLocals fsp (cs₁ ++ cs₂) =
      ∃∗ v : BitVec 64, runLocals fsp (cs₁ ++ MainHops.cell fsp o v :: cs₂) := by
  rw [r1b_locals_carve_region fsp cs₁ o 8 cs₂ hlo hhi hbnd,
    r1b_locals_focus fsp cs₁ o 8 _ cs₂, ProofLib.memRegion_eight, sepExists_sepConj_left]
  congr 1; funext v
  exact (r1b_locals_focus fsp cs₁ o 8 _ cs₂).symm

theorem r1b_locals_forget_cell (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o : Nat) (v : BitVec 64)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1b_localsEnd 0 cs₁ ≤ o := by simp [r1b_localsEnd, MainHops.cell])
    (hhi : o + 8 ≤ r1b_localsBound cs₂ := by simp [r1b_localsBound, MainHops.cell, runLocalBytes])
    (hbnd : r1b_localsBound cs₂ ≤ runLocalBytes := by
      simp [r1b_localsBound, MainHops.cell, runLocalBytes]) :
    runLocals fsp (cs₁ ++ MainHops.cell fsp o v :: cs₂) ⊢ runLocals fsp (cs₁ ++ cs₂) := by
  rw [r1b_locals_carve_cell fsp cs₁ o cs₂ hlo hhi hbnd]
  exact Entails.sepExists_right v (Entails.refl _)

/-! ## Bundle-Path Bounds and `AtInit1` Reject Semantics -/

theorem r1b_bundlePath_eq (dir : Bytes) (name : String) :
    bundlePath dir name = dir ++ [0x2f#8] ++ utf8 name := rfl

theorem r1b_init_path_facts {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {peerV : AddrV} {dir : Bytes}
    {s0 : State}
    (he : AtRunEntry S img ext g s0) (hc : g.c = .init peerV dir) :
    dir.length < 2 ^ 32 ∧
      (∀ name ∈ bundleNames,
        cliWrOk (dir ++ [0x2f#8] ++ utf8 name) ∧
          (dir ++ [0x2f#8] ++ utf8 name).length < 2 ^ 32) := by
  have hall := he.init_bundlePaths_ok hc
  have hreg := hall "registration-id" (by simp [bundleNames])
  have hreg_len : (dir ++ [0x2f#8] ++ utf8 "registration-id").length < 2 ^ 32 := hreg.2
  simp only [List.length_append] at hreg_len
  refine ⟨by omega, fun name hmem => ?_⟩
  have hn := hall name hmem
  exact ⟨hn, hn.2⟩

theorem r1b_reject_of_readBundle_none {S : RunSem} {img : Obj.Image}
    {ext : String → Option (State → State)} {g : RunCall} {d1 : Init1Data}
    {s0 s1 : State}
    (he : AtRunEntry S img ext g s0)
    (hi1 : AtInit1 img ext g d1 s0 s1)
    (hnone : readBundleV (runFiles g.i) d1.dir d1.peerV.device = none) :
    g.a = some none := by
  rcases hi1.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map Process.bytesOfString) =
      some (.init d1.peerV d1.dir) :=
    hi1.callEq ▸ he.parse
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  rw [hparse]
  simp [hget, hme, hnone]

theorem r1b_vecU8_14_intro (A : RustAlloc) (a buf : BitVec 64) (hbuf : buf ≠ 0#64) :
    ((a ↦₆₄ 14#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗ ((a + 16#64) ↦₆₄ 14#64) ∗
      A.live buf 14 1 ∗ memRegion buf 14) ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  rw [memRegion_eq_exists_bytes buf 14 (by decide)]
  rw [sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs
  have hcomm :
      ((a ↦₆₄ 14#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗ ((a + 16#64) ↦₆₄ 14#64) ∗
        A.live buf 14 1 ∗ (⌜bs.length = 14⌝ ∗ (buf ↦ₛ bs))) =
      (⌜bs.length = 14⌝ ∗ ((a ↦₆₄ 14#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗
        ((a + 16#64) ↦₆₄ 14#64) ∗ A.live buf 14 1 ∗ (buf ↦ₛ bs))) := by
    ac_rfl
  rw [hcomm]
  apply Entails.pure_left
  intro hlen
  refine Entails.sepExists_right bs ?_
  dsimp only [vecU8, vecU8At, vecHeader]
  refine Entails.sepExists_right 14#64 ?_
  refine Entails.sepExists_right buf ?_
  have h14 : BitVec.ofNat 64 bs.length = 14#64 := by rw [hlen]
  have h14nat : (14#64 : BitVec 64).toNat = 14 := rfl
  have hne14 : (14#64 : BitVec 64) ≠ 0 := by decide
  have hsub : 14 - bs.length = 0 := by omega
  simp only [h14, hne14, ↓reduceIte, h14nat, hsub, memRegion_zero, sepConj_emp]
  have hpure : bs.length ≤ 14 ∧ 14 < 2 ^ 63 ∧ buf ≠ 0 :=
    ⟨by omega, by decide, hbuf⟩
  conv => rhs; rw [sepConj_comm (a ↦₆₄ 14#64 ∗ (a + 8#64) ↦₆₄ buf ∗ (a + 16#64) ↦₆₄ 14#64),
    sepConj_assoc]
  exact Entails.pure_right hpure (Entails.of_eq (by ac_rfl))

end CryptoVerification.SignalSession.Cli.RunCompose
