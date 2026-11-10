/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Non-I/O `bl` Call-Site Distance Facts and Call Combinators for `main`

Symbolic `fnOff`/`fnAddr` equations, `MainCallees` instantiation corollaries, `SepWPp` in-image call
combinators (`oom := mainOom s0`), and per-site branch-target distance lemmas for all 71 non-I/O
`bl` sites of `main`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## `fnOff` Equations for Non-I/O Callees -/

theorem reserve11_fnOff :
    libsignalSessionCode.fnOff reserve11Name =
      num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")

theorem tryAllocateIn3_fnOff :
    libsignalSessionCode.fnOff tryAllocateIn3Name =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")

theorem address_fnOff :
    libsignalSessionCode.fnOff addressName =
      num% (ls_off% "libsignal_cli::address") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::address")

theorem run_fnOff :
    libsignalSessionCode.fnOff runName =
      num% (ls_off% "libsignal_cli::run") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::run")

theorem handleError_fnOff :
    libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" =
      num% (ls_off% "alloc::raw_vec::handle_error") :=
  ls_stub% "alloc::raw_vec::handle_error"

private theorem shim_fnOff :
    libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" =
      num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") :=
  ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2"

theorem rustAlloc_fnOff :
    libsignalSessionCode.fnOff "__rustc::__rust_alloc" =
      num% (ls_off% "__rustc::__rust_alloc") :=
  ls_stub% "__rustc::__rust_alloc"

theorem rustDealloc_fnOff :
    libsignalSessionCode.fnOff "__rustc::__rust_dealloc" =
      num% (ls_off% "__rustc::__rust_dealloc") :=
  ls_stub% "__rustc::__rust_dealloc"

theorem memcpyCallee_fnOff :
    libsignalSessionCode.fnOff "memcpy" =
      num% (ls_off% "memcpy") :=
  ls_stub% "memcpy"

theorem strlen_fnOff :
    libsignalSessionCode.fnOff "strlen" =
      num% (ls_off% "strlen") :=
  ls_stub% "strlen"

theorem fromUtf8_fnOff :
    libsignalSessionCode.fnOff "core::str::converts::from_utf8" =
      num% (ls_off% "core::str::converts::from_utf8") :=
  ls_stub% "core::str::converts::from_utf8"

/-! ## `main`-Relative `fnAddr` Equations and `MainCallees` Corollaries -/

theorem main_fnAddr_rel {img : Obj.Image} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff mainName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (mProg img ext).fnAddr mainName + off = (mProg img ext).fnAddr target := by
  simp only [mProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem main_fnAddr_sub {img : Obj.Image} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff mainName) - off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (mProg img ext).fnAddr mainName - off = (mProg img ext).fnAddr target := by
  have hadd : BitVec.ofNat 64 (libsignalSessionCode.fnOff mainName) + (0#64 - off) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target) := by
    rw [← h]; bv_omega
  have hrel := main_fnAddr_rel (img := img) (ext := ext) hadd
  calc
    (mProg img ext).fnAddr mainName - off
      = (mProg img ext).fnAddr mainName + (0#64 - off) := by bv_omega
    _ = (mProg img ext).fnAddr target := hrel

theorem main_bl_fwd {img : Obj.Image} {ext : String → Option (State → State)}
    {target : String} {site d : Nat}
    (h : libsignalSessionCode.fnOff mainName + (site + d) =
      libsignalSessionCode.fnOff target) :
    mPc img ext site + BitVec.ofNat 64 d = (mProg img ext).fnAddr target := by
  unfold mPc
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact main_fnAddr_rel (by rw [← BitVec.ofNat_add, h])

theorem main_bl_bwd {img : Obj.Image} {ext : String → Option (State → State)}
    {target : String} {site : Nat} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff mainName + site) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    mPc img ext site + off = (mProg img ext).fnAddr target := by
  unfold mPc
  rw [BitVec.add_assoc]
  exact main_fnAddr_rel (by rw [← BitVec.add_assoc, ← BitVec.ofNat_add, h])

theorem main_panic_handle_error (img : Obj.Image) (ext : String → Option (State → State)) :
    (mProg img ext).externAt?
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "main")) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (b := img.base) (ext := ext) (name := mainName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "main"))
    (by rw [main_fnOff, handleError_fnOff])

theorem main_shim_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "main"))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hC (name := mainName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "main"))
    (by rw [main_fnOff, shim_fnOff])

theorem main_alloc_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "main"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hC (name := mainName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "main"))
    (by rw [main_fnOff, rustAlloc_fnOff])

theorem main_dealloc_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "main"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hC (name := mainName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "main"))
    (by rw [main_fnOff, rustDealloc_fnOff])

theorem main_memcpy_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "memcpy" - ls_off% "main"))
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hC (name := mainName)
    (k := num% (ls_off% "memcpy" - ls_off% "main"))
    (by rw [main_fnOff, memcpyCallee_fnOff])

theorem main_shim_fs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsFs img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "main"))
      (session2ShimSpecX.keepsFs.inImage img) := by
  rw [main_fnAddr_rel (target := shimName) (by rw [main_fnOff, shim_fnOff]; decide)]
  exact subroutine_ok_mono_entails
    (hC.shim extHookStack (Nat.le_refl _) (by decide))
    (fun _ _ => Entails.of_eq (by
      simp [Spec.inImage, Spec.keepsFs, withStack, sessionShimSpec, session2ShimSpecX]))
    (fun _ _ _ => Entails.of_eq (by
      simp [Spec.inImage, Spec.keepsFs, withStack, sessionShimSpec, session2ShimSpecX]))

theorem main_alloc_fs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsFs img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "main"))
      ((rustAllocSpecWithStack A extHookStack).keepsFs.inImage img) := by
  rw [main_fnAddr_rel (target := allocName) (by rw [main_fnOff, rustAlloc_fnOff]; decide)]
  exact hC.alloc

theorem main_dealloc_fs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsFs img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "main"))
      ((rustDeallocExternSpecWithStack A extHookStack).keepsFs.inImage img) := by
  rw [main_fnAddr_rel (target := deallocName) (by rw [main_fnOff, rustDealloc_fnOff]; decide)]
  exact hC.dealloc

theorem main_memcpy_fs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsFs img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "memcpy" - ls_off% "main"))
      ((CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec extHookStack).keepsFs.inImage
        img) := by
  rw [main_fnAddr_rel (target := memcpyName) (by rw [main_fnOff, memcpyCallee_fnOff]; decide)]
  exact hC.session_memcpy extHookStack (Nat.le_refl _) (by decide)

theorem main_libc_memcpy_fs_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsFs img A ext) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "memcpy" - ls_off% "main"))
      ((libcMemcpySpec extHookStack).keepsFs.inImage img) := by
  rw [main_fnAddr_rel (target := memcpyName) (by rw [main_fnOff, memcpyCallee_fnOff]; decide)]
  exact hC.memcpy extHookStack (Nat.le_refl _) (by decide)

theorem main_strlen_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName + bv% (ls_off% "strlen" - ls_off% "main"))
      ((strlenSpec hookStack).inImage img) := by
  rw [main_fnAddr_rel (target := "strlen") (by rw [main_fnOff, strlen_fnOff]; decide)]
  exact hc.strlen

theorem main_fromUtf8_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% (ls_off% "core::str::converts::from_utf8" - ls_off% "main"))
      ((fromUtf8AsciiSpec hookStack).inImage img) := by
  rw [main_fnAddr_rel (target := "core::str::converts::from_utf8")
    (by rw [main_fnOff, fromUtf8_fnOff]; decide)]
  exact hc.fromUtf8

theorem main_address_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% ((2 ^ 64 + ls_off% "libsignal_cli::address" - ls_off% "main") % 2 ^ 64))
      ((addressSpec A uuidParse resStack).inImage img) := by
  rw [main_fnAddr_rel (target := addressName) (by rw [main_fnOff, address_fnOff]; decide)]
  exact hc.address

theorem main_address_sub_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName - bv% (ls_off% "main" - ls_off% "libsignal_cli::address"))
      ((addressSpec A uuidParse resStack).inImage img) := by
  rw [main_fnAddr_sub (target := addressName) (by rw [main_fnOff, address_fnOff]; decide)]
  exact hc.address

theorem main_reserve16_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% ((2 ^ 64 +
          ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]" -
          ls_off% "main") % 2 ^ 64))
      ((reserve16Spec A resStack).inImage img) := by
  rw [main_fnAddr_rel (target := reserve11Name) (by rw [main_fnOff, reserve11_fnOff]; decide)]
  exact hc.reserve16

theorem main_reserve16_sub_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName -
        bv% (ls_off% "main" -
          ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"))
      ((reserve16Spec A resStack).inImage img) := by
  rw [main_fnAddr_sub (target := reserve11Name) (by rw [main_fnOff, reserve11_fnOff]; decide)]
  exact hc.reserve16

theorem main_reserve1_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% ((2 ^ 64 +
          ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]" -
          ls_off% "main") % 2 ^ 64))
      ((CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs.inImage img) := by
  rw [main_fnAddr_rel (target := reserve11Name) (by rw [main_fnOff, reserve11_fnOff]; decide)]
  exact hc.reserve1

theorem main_reserve1_sub_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName -
        bv% (ls_off% "main" -
          ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"))
      ((CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs.inImage img) := by
  rw [main_fnAddr_sub (target := reserve11Name) (by rw [main_fnOff, reserve11_fnOff]; decide)]
  exact hc.reserve1

theorem main_tryAllocateIn3_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName +
        bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" -
          ls_off% "main") % 2 ^ 64))
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img) := by
  rw [main_fnAddr_rel (target := tryAllocateIn3Name)
    (by rw [main_fnOff, tryAllocateIn3_fnOff]; decide)]
  exact hc.tryAllocateIn3

theorem main_tryAllocateIn3_sub_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCallees img A ext uuidParse hookStack resStack) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr mainName -
        bv% (ls_off% "main" - ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]"))
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img) := by
  rw [main_fnAddr_sub (target := tryAllocateIn3Name)
    (by rw [main_fnOff, tryAllocateIn3_fnOff]; decide)]
  exact hc.tryAllocateIn3

theorem main_run_fnAddr_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    (mProg img ext).fnAddr mainName +
      bv% ((2 ^ 64 + ls_off% "libsignal_cli::run" - ls_off% "main") % 2 ^ 64) =
      (mProg img ext).fnAddr runName :=
  main_fnAddr_rel (by rw [main_fnOff, run_fnOff]; decide)

theorem main_run_fnAddr_sub_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    (mProg img ext).fnAddr mainName -
      bv% (ls_off% "main" - ls_off% "libsignal_cli::run") =
      (mProg img ext).fnAddr runName :=
  main_fnAddr_sub (by rw [main_fnOff, run_fnOff]; decide)

/-! ## `SepWPp` In-Image Cut and Call Combinators -/

theorem sepWPp_seq_inImage {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hcont (hinv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

set_option linter.unusedVariables false in
theorem main_call_inImage_steps {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      Steps prog s sf →
      ImgCallInv img sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (s0 : State := by exact s) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (spec.inImage img).pre x s ∗ (F ∗ R) := by
    dsimp only [Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, by simpa only [sepConj_assoc] using hm_pre⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [Spec.inImage] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_steps hsteps) hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [Spec.inImage] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [Spec.inImage] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

set_option linter.unusedVariables false in
theorem main_call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      ImgCallInv img sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (s0 : State := by exact s) :
    SepWPp prog ret s P Q Qp oom :=
  main_call_inImage_steps x hcall hinv hpc hrun hsp hlr hP hpanic hexit hoom
    (fun sf _ => hnext sf) s0

/-! ## Per-Site Distance Facts for Non-I/O `bl` Sites -/

-- M1 sites (4 non-IO `bl`s: `0x058`, `0x068`, `0x078`, `0x0ac`)
theorem blOff_0x058 : libsignalSessionCode.fnOff mainName + (0x058 + num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0x058))) = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by rw [main_fnOff, handleError_fnOff]
theorem bl_0x058 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x058 + bv% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0x058)) = (mProg img ext).fnAddr "alloc::raw_vec::handle_error" := main_bl_fwd blOff_0x058

theorem blOff_0x068 : libsignalSessionCode.fnOff mainName + (0x068 + num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "main" + 0x068))) = libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by rw [main_fnOff, shim_fnOff]
theorem bl_0x068 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x068 + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "main" + 0x068)) = (mProg img ext).fnAddr "__rustc::__rust_no_alloc_shim_is_unstable_v2" := main_bl_fwd blOff_0x068

theorem blOff_0x078 : libsignalSessionCode.fnOff mainName + (0x078 + num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "main" + 0x078))) = libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by rw [main_fnOff, rustAlloc_fnOff]
theorem bl_0x078 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x078 + bv% (ls_off% "__rustc::__rust_alloc" - (ls_off% "main" + 0x078)) = (mProg img ext).fnAddr "__rustc::__rust_alloc" := main_bl_fwd blOff_0x078

theorem blOff_0x0ac : libsignalSessionCode.fnOff mainName + (0x0ac + num% (ls_off% "strlen" - (ls_off% "main" + 0x0ac))) = libsignalSessionCode.fnOff "strlen" := by rw [main_fnOff, strlen_fnOff]
theorem bl_0x0ac (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x0ac + bv% (ls_off% "strlen" - (ls_off% "main" + 0x0ac)) = (mProg img ext).fnAddr "strlen" := main_bl_fwd blOff_0x0ac

-- M2 collect & dispatch sites (`0x0c8` .. `0x55c`: 12 non-IO `bl`s)
theorem blOff_0x0c8 : libsignalSessionCode.fnOff mainName + (0x0c8 + num% (ls_off% "core::str::converts::from_utf8" - (ls_off% "main" + 0x0c8))) = libsignalSessionCode.fnOff "core::str::converts::from_utf8" := by rw [main_fnOff, fromUtf8_fnOff]
theorem bl_0x0c8 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x0c8 + bv% (ls_off% "core::str::converts::from_utf8" - (ls_off% "main" + 0x0c8)) = (mProg img ext).fnAddr "core::str::converts::from_utf8" := main_bl_fwd blOff_0x0c8

theorem blOff_0x0dc : libsignalSessionCode.fnOff mainName + (0x0dc + num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "main" + 0x0dc))) = libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by rw [main_fnOff, shim_fnOff]
theorem bl_0x0dc (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x0dc + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "main" + 0x0dc)) = (mProg img ext).fnAddr "__rustc::__rust_no_alloc_shim_is_unstable_v2" := main_bl_fwd blOff_0x0dc

theorem blOff_0x0e8 : libsignalSessionCode.fnOff mainName + (0x0e8 + num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "main" + 0x0e8))) = libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by rw [main_fnOff, rustAlloc_fnOff]
theorem bl_0x0e8 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x0e8 + bv% (ls_off% "__rustc::__rust_alloc" - (ls_off% "main" + 0x0e8)) = (mProg img ext).fnAddr "__rustc::__rust_alloc" := main_bl_fwd blOff_0x0e8

theorem blOff_0x12c : libsignalSessionCode.fnOff mainName + (0x12c + num% (ls_off% "core::str::converts::from_utf8" - (ls_off% "main" + 0x12c))) = libsignalSessionCode.fnOff "core::str::converts::from_utf8" := by rw [main_fnOff, fromUtf8_fnOff]
theorem bl_0x12c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x12c + bv% (ls_off% "core::str::converts::from_utf8" - (ls_off% "main" + 0x12c)) = (mProg img ext).fnAddr "core::str::converts::from_utf8" := main_bl_fwd blOff_0x12c

theorem blOff_0x180 : libsignalSessionCode.fnOff reserve11Name + num% ((ls_off% "main" + 0x180) - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") = libsignalSessionCode.fnOff mainName + 0x180 := by rw [main_fnOff, reserve11_fnOff]
theorem bl_0x180 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x180 + bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]" - (ls_off% "main" + 0x180)) % 2 ^ 64) = (mProg img ext).fnAddr reserve11Name := main_bl_bwd (by rw [main_fnOff, reserve11_fnOff]; decide)

theorem blOff_0x1fc : libsignalSessionCode.fnOff addressName + num% ((ls_off% "main" + 0x1fc) - ls_off% "libsignal_cli::address") = libsignalSessionCode.fnOff mainName + 0x1fc := by rw [main_fnOff, address_fnOff]
theorem bl_0x1fc (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x1fc + bv% ((2 ^ 64 + ls_off% "libsignal_cli::address" - (ls_off% "main" + 0x1fc)) % 2 ^ 64) = (mProg img ext).fnAddr addressName := main_bl_bwd (by rw [main_fnOff, address_fnOff]; decide)

theorem blOff_0x264 : libsignalSessionCode.fnOff addressName + num% ((ls_off% "main" + 0x264) - ls_off% "libsignal_cli::address") = libsignalSessionCode.fnOff mainName + 0x264 := by rw [main_fnOff, address_fnOff]
theorem bl_0x264 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x264 + bv% ((2 ^ 64 + ls_off% "libsignal_cli::address" - (ls_off% "main" + 0x264)) % 2 ^ 64) = (mProg img ext).fnAddr addressName := main_bl_bwd (by rw [main_fnOff, address_fnOff]; decide)

theorem blOff_0x28c : libsignalSessionCode.fnOff tryAllocateIn3Name + num% ((ls_off% "main" + 0x28c) - ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]") = libsignalSessionCode.fnOff mainName + 0x28c := by rw [main_fnOff, tryAllocateIn3_fnOff]
theorem bl_0x28c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x28c + bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" - (ls_off% "main" + 0x28c)) % 2 ^ 64) = (mProg img ext).fnAddr tryAllocateIn3Name := main_bl_bwd (by rw [main_fnOff, tryAllocateIn3_fnOff]; decide)

theorem blOff_0x2b8 : libsignalSessionCode.fnOff mainName + (0x2b8 + num% (ls_off% "memcpy" - (ls_off% "main" + 0x2b8))) = libsignalSessionCode.fnOff "memcpy" := by rw [main_fnOff, memcpyCallee_fnOff]
theorem bl_0x2b8 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x2b8 + bv% (ls_off% "memcpy" - (ls_off% "main" + 0x2b8)) = (mProg img ext).fnAddr "memcpy" := main_bl_fwd blOff_0x2b8

theorem blOff_0x334 : libsignalSessionCode.fnOff addressName + num% ((ls_off% "main" + 0x334) - ls_off% "libsignal_cli::address") = libsignalSessionCode.fnOff mainName + 0x334 := by rw [main_fnOff, address_fnOff]
theorem bl_0x334 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x334 + bv% ((2 ^ 64 + ls_off% "libsignal_cli::address" - (ls_off% "main" + 0x334)) % 2 ^ 64) = (mProg img ext).fnAddr addressName := main_bl_bwd (by rw [main_fnOff, address_fnOff]; decide)

theorem blOff_0x364 : libsignalSessionCode.fnOff addressName + num% ((ls_off% "main" + 0x364) - ls_off% "libsignal_cli::address") = libsignalSessionCode.fnOff mainName + 0x364 := by rw [main_fnOff, address_fnOff]
theorem bl_0x364 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x364 + bv% ((2 ^ 64 + ls_off% "libsignal_cli::address" - (ls_off% "main" + 0x364)) % 2 ^ 64) = (mProg img ext).fnAddr addressName := main_bl_bwd (by rw [main_fnOff, address_fnOff]; decide)

theorem blOff_0x55c : libsignalSessionCode.fnOff mainName + (0x55c + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0x55c))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0x55c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x55c + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0x55c)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0x55c

-- M4 `run` site (`0x710`)
theorem blOff_0x710 : libsignalSessionCode.fnOff runName + num% ((ls_off% "main" + 0x710) - ls_off% "libsignal_cli::run") = libsignalSessionCode.fnOff mainName + 0x710 := by rw [main_fnOff, run_fnOff]
theorem bl_0x710 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x710 + bv% ((2 ^ 64 + ls_off% "libsignal_cli::run" - (ls_off% "main" + 0x710)) % 2 ^ 64) = (mProg img ext).fnAddr runName := main_bl_bwd (by rw [main_fnOff, run_fnOff]; decide)

-- M5 payload-move & commit-loop sites (`0x73c` .. `0xa3c`: 16 non-IO `bl`s)
theorem blOff_0x73c : libsignalSessionCode.fnOff mainName + (0x73c + num% (ls_off% "memcpy" - (ls_off% "main" + 0x73c))) = libsignalSessionCode.fnOff "memcpy" := by rw [main_fnOff, memcpyCallee_fnOff]
theorem bl_0x73c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x73c + bv% (ls_off% "memcpy" - (ls_off% "main" + 0x73c)) = (mProg img ext).fnAddr "memcpy" := main_bl_fwd blOff_0x73c

theorem blOff_0x814 : libsignalSessionCode.fnOff mainName + (0x814 + num% (ls_off% "memcpy" - (ls_off% "main" + 0x814))) = libsignalSessionCode.fnOff "memcpy" := by rw [main_fnOff, memcpyCallee_fnOff]
theorem bl_0x814 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x814 + bv% (ls_off% "memcpy" - (ls_off% "main" + 0x814)) = (mProg img ext).fnAddr "memcpy" := main_bl_fwd blOff_0x814

theorem blOff_0x874 : libsignalSessionCode.fnOff mainName + (0x874 + num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "main" + 0x874))) = libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by rw [main_fnOff, shim_fnOff]
theorem bl_0x874 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x874 + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "main" + 0x874)) = (mProg img ext).fnAddr "__rustc::__rust_no_alloc_shim_is_unstable_v2" := main_bl_fwd blOff_0x874

theorem blOff_0x880 : libsignalSessionCode.fnOff mainName + (0x880 + num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "main" + 0x880))) = libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by rw [main_fnOff, rustAlloc_fnOff]
theorem bl_0x880 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x880 + bv% (ls_off% "__rustc::__rust_alloc" - (ls_off% "main" + 0x880)) = (mProg img ext).fnAddr "__rustc::__rust_alloc" := main_bl_fwd blOff_0x880

theorem blOff_0x894 : libsignalSessionCode.fnOff mainName + (0x894 + num% (ls_off% "memcpy" - (ls_off% "main" + 0x894))) = libsignalSessionCode.fnOff "memcpy" := by rw [main_fnOff, memcpyCallee_fnOff]
theorem bl_0x894 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x894 + bv% (ls_off% "memcpy" - (ls_off% "main" + 0x894)) = (mProg img ext).fnAddr "memcpy" := main_bl_fwd blOff_0x894

theorem blOff_0x8b4 : libsignalSessionCode.fnOff reserve11Name + num% ((ls_off% "main" + 0x8b4) - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") = libsignalSessionCode.fnOff mainName + 0x8b4 := by rw [main_fnOff, reserve11_fnOff]
theorem bl_0x8b4 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x8b4 + bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]" - (ls_off% "main" + 0x8b4)) % 2 ^ 64) = (mProg img ext).fnAddr reserve11Name := main_bl_bwd (by rw [main_fnOff, reserve11_fnOff]; decide)

theorem blOff_0x8ec : libsignalSessionCode.fnOff mainName + (0x8ec + num% (ls_off% "memcpy" - (ls_off% "main" + 0x8ec))) = libsignalSessionCode.fnOff "memcpy" := by rw [main_fnOff, memcpyCallee_fnOff]
theorem bl_0x8ec (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x8ec + bv% (ls_off% "memcpy" - (ls_off% "main" + 0x8ec)) = (mProg img ext).fnAddr "memcpy" := main_bl_fwd blOff_0x8ec

theorem blOff_0x914 : libsignalSessionCode.fnOff mainName + (0x914 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0x914))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0x914 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x914 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0x914)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0x914

theorem blOff_0x940 : libsignalSessionCode.fnOff reserve11Name + num% ((ls_off% "main" + 0x940) - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") = libsignalSessionCode.fnOff mainName + 0x940 := by rw [main_fnOff, reserve11_fnOff]
theorem bl_0x940 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x940 + bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]" - (ls_off% "main" + 0x940)) % 2 ^ 64) = (mProg img ext).fnAddr reserve11Name := main_bl_bwd (by rw [main_fnOff, reserve11_fnOff]; decide)

theorem blOff_0x96c : libsignalSessionCode.fnOff mainName + (0x96c + num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "main" + 0x96c))) = libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by rw [main_fnOff, shim_fnOff]
theorem bl_0x96c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x96c + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "main" + 0x96c)) = (mProg img ext).fnAddr "__rustc::__rust_no_alloc_shim_is_unstable_v2" := main_bl_fwd blOff_0x96c

theorem blOff_0x978 : libsignalSessionCode.fnOff mainName + (0x978 + num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "main" + 0x978))) = libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by rw [main_fnOff, rustAlloc_fnOff]
theorem bl_0x978 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x978 + bv% (ls_off% "__rustc::__rust_alloc" - (ls_off% "main" + 0x978)) = (mProg img ext).fnAddr "__rustc::__rust_alloc" := main_bl_fwd blOff_0x978

theorem blOff_0x98c : libsignalSessionCode.fnOff mainName + (0x98c + num% (ls_off% "memcpy" - (ls_off% "main" + 0x98c))) = libsignalSessionCode.fnOff "memcpy" := by rw [main_fnOff, memcpyCallee_fnOff]
theorem bl_0x98c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x98c + bv% (ls_off% "memcpy" - (ls_off% "main" + 0x98c)) = (mProg img ext).fnAddr "memcpy" := main_bl_fwd blOff_0x98c

theorem blOff_0x9b0 : libsignalSessionCode.fnOff mainName + (0x9b0 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0x9b0))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0x9b0 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0x9b0 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0x9b0)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0x9b0

theorem blOff_0xa0c : libsignalSessionCode.fnOff mainName + (0xa0c + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xa0c))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xa0c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xa0c + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xa0c)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xa0c

theorem blOff_0xa20 : libsignalSessionCode.fnOff mainName + (0xa20 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xa20))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xa20 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xa20 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xa20)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xa20

theorem blOff_0xa3c : libsignalSessionCode.fnOff mainName + (0xa3c + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xa3c))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xa3c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xa3c + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xa3c)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xa3c

-- M3/M4/M2-error/free_args/M5-drop/M6/cold tail sites (`0xa60` .. `0xfc4`: 38 non-IO `bl`s)
theorem blOff_0xa60 : libsignalSessionCode.fnOff mainName + (0xa60 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xa60))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xa60 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xa60 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xa60)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xa60

theorem blOff_0xaa4 : libsignalSessionCode.fnOff mainName + (0xaa4 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xaa4))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xaa4 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xaa4 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xaa4)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xaa4

theorem blOff_0xacc : libsignalSessionCode.fnOff mainName + (0xacc + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xacc))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xacc (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xacc + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xacc)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xacc

theorem blOff_0xae4 : libsignalSessionCode.fnOff mainName + (0xae4 + num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0xae4))) = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by rw [main_fnOff, handleError_fnOff]
theorem bl_0xae4 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xae4 + bv% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0xae4)) = (mProg img ext).fnAddr "alloc::raw_vec::handle_error" := main_bl_fwd blOff_0xae4

theorem blOff_0xaf4 : libsignalSessionCode.fnOff mainName + (0xaf4 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xaf4))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xaf4 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xaf4 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xaf4)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xaf4

theorem blOff_0xb08 : libsignalSessionCode.fnOff mainName + (0xb08 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xb08))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xb08 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xb08 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xb08)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xb08

theorem blOff_0xb20 : libsignalSessionCode.fnOff mainName + (0xb20 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xb20))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xb20 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xb20 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xb20)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xb20

theorem blOff_0xb58 : libsignalSessionCode.fnOff mainName + (0xb58 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xb58))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xb58 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xb58 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xb58)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xb58

theorem blOff_0xb80 : libsignalSessionCode.fnOff mainName + (0xb80 + num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0xb80))) = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by rw [main_fnOff, handleError_fnOff]
theorem bl_0xb80 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xb80 + bv% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0xb80)) = (mProg img ext).fnAddr "alloc::raw_vec::handle_error" := main_bl_fwd blOff_0xb80

theorem blOff_0xbb4 : libsignalSessionCode.fnOff mainName + (0xbb4 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xbb4))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xbb4 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xbb4 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xbb4)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xbb4

theorem blOff_0xbe8 : libsignalSessionCode.fnOff mainName + (0xbe8 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xbe8))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xbe8 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xbe8 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xbe8)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xbe8

theorem blOff_0xbfc : libsignalSessionCode.fnOff mainName + (0xbfc + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xbfc))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xbfc (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xbfc + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xbfc)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xbfc

theorem blOff_0xc18 : libsignalSessionCode.fnOff mainName + (0xc18 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xc18))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xc18 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xc18 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xc18)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xc18

theorem blOff_0xc60 : libsignalSessionCode.fnOff mainName + (0xc60 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xc60))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xc60 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xc60 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xc60)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xc60

theorem blOff_0xc74 : libsignalSessionCode.fnOff mainName + (0xc74 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xc74))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xc74 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xc74 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xc74)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xc74

theorem blOff_0xc94 : libsignalSessionCode.fnOff mainName + (0xc94 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xc94))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xc94 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xc94 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xc94)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xc94

theorem blOff_0xccc : libsignalSessionCode.fnOff mainName + (0xccc + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xccc))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xccc (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xccc + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xccc)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xccc

theorem blOff_0xce0 : libsignalSessionCode.fnOff mainName + (0xce0 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xce0))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xce0 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xce0 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xce0)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xce0

theorem blOff_0xd00 : libsignalSessionCode.fnOff mainName + (0xd00 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xd00))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xd00 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xd00 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xd00)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xd00

theorem blOff_0xd38 : libsignalSessionCode.fnOff mainName + (0xd38 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xd38))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xd38 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xd38 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xd38)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xd38

theorem blOff_0xd4c : libsignalSessionCode.fnOff mainName + (0xd4c + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xd4c))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xd4c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xd4c + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xd4c)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xd4c

theorem blOff_0xd6c : libsignalSessionCode.fnOff mainName + (0xd6c + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xd6c))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xd6c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xd6c + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xd6c)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xd6c

theorem blOff_0xda4 : libsignalSessionCode.fnOff mainName + (0xda4 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xda4))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xda4 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xda4 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xda4)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xda4

theorem blOff_0xdb8 : libsignalSessionCode.fnOff mainName + (0xdb8 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xdb8))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xdb8 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xdb8 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xdb8)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xdb8

theorem blOff_0xdd8 : libsignalSessionCode.fnOff mainName + (0xdd8 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xdd8))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xdd8 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xdd8 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xdd8)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xdd8

theorem blOff_0xe10 : libsignalSessionCode.fnOff mainName + (0xe10 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe10))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xe10 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xe10 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe10)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xe10

theorem blOff_0xe24 : libsignalSessionCode.fnOff mainName + (0xe24 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe24))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xe24 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xe24 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe24)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xe24

theorem blOff_0xe44 : libsignalSessionCode.fnOff mainName + (0xe44 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe44))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xe44 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xe44 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe44)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xe44

theorem blOff_0xe7c : libsignalSessionCode.fnOff mainName + (0xe7c + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe7c))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xe7c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xe7c + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe7c)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xe7c

theorem blOff_0xe90 : libsignalSessionCode.fnOff mainName + (0xe90 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe90))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xe90 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xe90 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xe90)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xe90

theorem blOff_0xeb0 : libsignalSessionCode.fnOff mainName + (0xeb0 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xeb0))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xeb0 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xeb0 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xeb0)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xeb0

theorem blOff_0xee8 : libsignalSessionCode.fnOff mainName + (0xee8 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xee8))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xee8 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xee8 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xee8)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xee8

theorem blOff_0xefc : libsignalSessionCode.fnOff mainName + (0xefc + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xefc))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xefc (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xefc + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xefc)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xefc

theorem blOff_0xf30 : libsignalSessionCode.fnOff mainName + (0xf30 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xf30))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xf30 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xf30 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xf30)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xf30

theorem blOff_0xf64 : libsignalSessionCode.fnOff mainName + (0xf64 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xf64))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xf64 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xf64 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xf64)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xf64

theorem blOff_0xf78 : libsignalSessionCode.fnOff mainName + (0xf78 + num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xf78))) = libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by rw [main_fnOff, rustDealloc_fnOff]
theorem bl_0xf78 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xf78 + bv% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "main" + 0xf78)) = (mProg img ext).fnAddr "__rustc::__rust_dealloc" := main_bl_fwd blOff_0xf78

theorem blOff_0xf8c : libsignalSessionCode.fnOff mainName + (0xf8c + num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0xf8c))) = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by rw [main_fnOff, handleError_fnOff]
theorem bl_0xf8c (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xf8c + bv% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0xf8c)) = (mProg img ext).fnAddr "alloc::raw_vec::handle_error" := main_bl_fwd blOff_0xf8c

theorem blOff_0xfc4 : libsignalSessionCode.fnOff mainName + (0xfc4 + num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0xfc4))) = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by rw [main_fnOff, handleError_fnOff]
theorem bl_0xfc4 (img : Obj.Image) (ext : String → Option (State → State)) : mPc img ext 0xfc4 + bv% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "main" + 0xfc4)) = (mProg img ext).fnAddr "alloc::raw_vec::handle_error" := main_bl_fwd blOff_0xfc4

end CryptoVerification.SignalSession.Cli.MainHops
