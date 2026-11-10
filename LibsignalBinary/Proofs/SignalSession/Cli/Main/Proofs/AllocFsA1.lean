/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# `AllocContractsFs` and `AllocContractsX` from `cliExterns` and `CliExternsOk`

Discharges `AllocContractsX`, `AllocContractsFs`, and read-only-source `memcpy`
(`session_memcpy_region_ro`) on `mProg img (cliExterns W)` (via `CliAllocHooks A`, unconditional at
`A₀`) and parametrically on `mProg img (cliExternsWith ext)` from `CliExternsOk P A ext`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## File-System Preservation for Allocator and Memory Hooks -/

/-- `bumpThen` preserves `fs` whenever both continuations do. -/
theorem bumpThen_fs {size align : Nat} {ok : State → BitVec 64 → State} {fail : State → State}
    (hok : ∀ s p, (ok s p).fs = s.fs) (hfail : ∀ s, (fail s).fs = s.fs) :
    ∀ s, (E2E.bumpThen size align ok fail s).fs = s.fs := by
  intro s
  unfold E2E.bumpThen
  split
  · rw [hok, State.fs_setMem]
  · exact hfail s

theorem allocFail_fs : ∀ s, (E2E.allocFail s).fs = s.fs := by
  intro s
  simp [E2E.allocFail, retHook]

theorem hookNoop_fs : ∀ s, (hookNoop s).fs = s.fs := by
  intro s
  simp [hookNoop, retHook]

theorem allocHook0_fs : ∀ s, (E2E.allocHook0 s).fs = s.fs := by
  intro s
  unfold E2E.allocHook0
  exact bumpThen_fs (fun _ _ => by simp [retHook]) allocFail_fs s

theorem deallocHook_fs : ∀ s, (E2E.deallocHook s).fs = s.fs := hookNoop_fs

theorem reallocHook0_fs : ∀ s, (E2E.reallocHook0 s).fs = s.fs := by
  intro s
  unfold E2E.reallocHook0
  exact bumpThen_fs (fun _ _ => by simp [retHook]) allocFail_fs s

theorem hookMemset_fs : ∀ s, (hookMemset s).fs = s.fs := by
  intro s
  simp [hookMemset, retHook]

theorem hookMemcpy_fs : ∀ s, (hookMemcpy s).fs = s.fs := by
  intro s
  simp [hookMemcpy, retHook]

theorem hookMemmove_fs : ∀ s, (hookMemmove s).fs = s.fs := hookMemcpy_fs

/-! ## Stub Plumbing on `mProg img (cliExterns W)` -/

/-- Lifts a `cliHookTable` row satisfying `HookOk h spec` to `subroutine_ok` at its stub entry. -/
theorem cli_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {name : String}
    {h : State → State} {spec : Spec α} {stub : Nat}
    (hfn : libsignalSessionCode.fnOff name = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? stub = H name)
    (hnp : Rust.isPanicSymbol name = false)
    (hrow : (name, h) ∈ cliHookTable W) (hh : HookOk h spec) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr name) spec := by
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExterns W)
    (hname := name) (k := 0) hfn (Nat.add_zero _) hs hstub hnp ⟨_, cliExterns_row W hrow, hh⟩
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

theorem shim_fnOff :
    libsignalSessionCode.fnOff shimName =
      num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")

theorem alloc_fnOff :
    libsignalSessionCode.fnOff allocName = num% (ls_off% "__rustc::__rust_alloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_alloc")

theorem dealloc_fnOff :
    libsignalSessionCode.fnOff deallocName = num% (ls_off% "__rustc::__rust_dealloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_dealloc")

theorem realloc_fnOff :
    libsignalSessionCode.fnOff reallocName = num% (ls_off% "__rustc::__rust_realloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_realloc")

theorem memset_fnOff : libsignalSessionCode.fnOff memsetName = num% (ls_off% "memset") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "memset")

theorem memmove_fnOff : libsignalSessionCode.fnOff memmoveName = num% (ls_off% "memmove") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "memmove")

theorem memcpy_fnOff : libsignalSessionCode.fnOff memcpyName = num% (ls_off% "memcpy") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "memcpy")

theorem shim_row (W : CliHooks) : (shimName, hookNoop) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 0) rfl)

theorem alloc_row (W : CliHooks) : (allocName, E2E.allocHook0) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 1) rfl)

theorem dealloc_row (W : CliHooks) : (deallocName, E2E.deallocHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 2) rfl)

theorem realloc_row (W : CliHooks) : (reallocName, E2E.reallocHook0) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 3) rfl)

theorem memset_row (W : CliHooks) : (memsetName, hookMemset) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 5) rfl)

theorem memmove_row (W : CliHooks) : (memmoveName, hookMemmove) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 6) rfl)

theorem memcpy_row (W : CliHooks) : (memcpyName, hookMemcpy) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 7) rfl)

theorem shim_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk hookNoop spec) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr shimName) spec :=
  cli_stub_ok W img shim_fnOff (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by simp [Rust.isPanicSymbol, shimName]) (shim_row W) hh

theorem alloc_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk E2E.allocHook0 spec) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr allocName) spec :=
  cli_stub_ok W img alloc_fnOff (by decide) (ls_hook% "__rustc::__rust_alloc")
    (by simp [Rust.isPanicSymbol, allocName]) (alloc_row W) hh

theorem dealloc_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk E2E.deallocHook spec) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr deallocName)
      spec :=
  cli_stub_ok W img dealloc_fnOff (by decide) (ls_hook% "__rustc::__rust_dealloc")
    (by simp [Rust.isPanicSymbol, deallocName]) (dealloc_row W) hh

theorem realloc_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk E2E.reallocHook0 spec) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr reallocName)
      spec :=
  cli_stub_ok W img realloc_fnOff (by decide) (ls_hook% "__rustc::__rust_realloc")
    (by simp [Rust.isPanicSymbol, reallocName]) (realloc_row W) hh

theorem memset_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk hookMemset spec) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr memsetName) spec :=
  cli_stub_ok W img memset_fnOff (by decide) (ls_hook% "memset")
    (by simp [Rust.isPanicSymbol, memsetName]) (memset_row W) hh

theorem memmove_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk hookMemmove spec) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr memmoveName)
      spec :=
  cli_stub_ok W img memmove_fnOff (by decide) (ls_hook% "memmove")
    (by simp [Rust.isPanicSymbol, memmoveName]) (memmove_row W) hh

theorem memcpy_stub_ok {α : Type} (W : CliHooks) (img : Obj.Image) {spec : Spec α}
    (hh : HookOk hookMemcpy spec) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr memcpyName) spec :=
  cli_stub_ok W img memcpy_fnOff (by decide) (ls_hook% "memcpy")
    (by simp [Rust.isPanicSymbol, memcpyName]) (memcpy_row W) hh

/-! ## `AllocContractsFs` and `AllocContractsX` Constructors -/

/-- Bundle of `HookOk` witnesses for `allocHook0`, `deallocHook`, and `reallocHook0` at `A`. -/
structure CliAllocHooks (A : RustAlloc) : Prop where
  alloc : HookOk E2E.allocHook0 (rustAllocSpec A)
  dealloc : HookOk E2E.deallocHook (rustDeallocSpec A)
  realloc : HookOk E2E.reallocHook0 (rustReallocSpec A)

theorem cliAllocHooks_A0 : CliAllocHooks E2E.HooksE.A0 where
  alloc := E2E.HooksE.allocHook0_ok
  dealloc := E2E.HooksE.deallocHook_ok
  realloc := E2E.HooksE.reallocHook0_ok

theorem allocHookStack_le_extHookStack : allocHookStack ≤ extHookStack := by decide

theorem extHookStack_le : extHookStack ≤ 2 ^ 64 := by decide

theorem pos_of_extHookStack_le {stk : Nat} (h : extHookStack ≤ stk) : 0 < stk :=
  Nat.lt_of_lt_of_le (by decide) h

/-- Constructs `AllocContractsFs` on `cliExterns W` from `CliAllocHooks A`. -/
theorem AllocContractsFs.of_hooks (W : CliHooks) (img : Obj.Image) {A : RustAlloc}
    (hA : CliAllocHooks A) : AllocContractsFs img A (cliExterns W) where
  alloc := subroutine_ok_inImage_of_subroutine_ok img <| alloc_stub_ok W img <|
    (hookOk_rustAllocWithStack (stk := extHookStack) hA.alloc allocHookStack_le_extHookStack
      extHookStack_le).keepsFs allocHook0_fs
  dealloc := subroutine_ok_inImage_of_subroutine_ok img <| dealloc_stub_ok W img <|
    (hookOk_rustDeallocExternWithStack (stk := extHookStack) hA.dealloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs deallocHook_fs
  realloc := subroutine_ok_inImage_of_subroutine_ok img <| realloc_stub_ok W img <|
    (hookOk_rustReallocExternWithStack (stk := extHookStack) hA.realloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs reallocHook0_fs
  shim stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| shim_stub_ok W img <|
    (hookOk_withStack sessionShim_hookOk stk).keepsFs hookNoop_fs
  memcpy stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_stub_ok W img <|
    (hookMemcpy_ok stk).keepsFs hookMemcpy_fs
  session_memcpy stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_stub_ok W img <|
    (hookMemcpy_trace_ok stk).keepsFs hookMemcpy_fs
  memcpy_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_stub_ok W img <|
    (hookOk_withStack hookMemcpy_region_ok stk).keepsFs hookMemcpy_fs
  session_memcpy_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memcpy_stub_ok W img <| (hookOk_withStack hookMemcpy_region_trace_ok stk).keepsFs hookMemcpy_fs
  memmove stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memmove_stub_ok W img <|
    (hookMemmove_ok stk).keepsFs hookMemmove_fs
  session_memmove stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memmove_stub_ok W img <|
    (hookMemmove_trace_ok stk).keepsFs hookMemmove_fs
  memset stk hle _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_stub_ok W img <|
    (hookMemset_ok stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs
  session_memset stk hle _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_stub_ok W img <|
    (hookMemset_trace_ok stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs
  memset_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_stub_ok W img <|
    (hookOk_withStack hookMemset_region_ok stk).keepsFs hookMemset_fs
  session_memset_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memset_stub_ok W img <| (hookOk_withStack hookMemset_region_trace_ok stk).keepsFs hookMemset_fs
  session_memcpy_region_ro stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memcpy_stub_ok W img <|
      (hookOk_withStack CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok stk).keepsFs
        hookMemcpy_fs

/-- Constructs `AllocContractsX` on `cliExterns W` from `CliAllocHooks A`. -/
theorem AllocContractsX.of_hooks (W : CliHooks) (img : Obj.Image) {A : RustAlloc}
    (hA : CliAllocHooks A) : AllocContractsX img A (cliExterns W) where
  alloc := subroutine_ok_inImage_of_subroutine_ok img <| alloc_stub_ok W img <|
    hookOk_rustAllocWithStack (stk := extHookStack) hA.alloc allocHookStack_le_extHookStack
      extHookStack_le
  dealloc := subroutine_ok_inImage_of_subroutine_ok img <| dealloc_stub_ok W img <|
    hookOk_rustDeallocExternWithStack (stk := extHookStack) hA.dealloc
      allocHookStack_le_extHookStack extHookStack_le
  realloc := subroutine_ok_inImage_of_subroutine_ok img <| realloc_stub_ok W img <|
    hookOk_rustReallocExternWithStack (stk := extHookStack) hA.realloc
      allocHookStack_le_extHookStack extHookStack_le
  shim stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| shim_stub_ok W img <|
    hookOk_withStack sessionShim_hookOk stk
  memcpy stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_stub_ok W img <|
    hookMemcpy_ok stk
  session_memcpy stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_stub_ok W img <|
    hookMemcpy_trace_ok stk
  memcpy_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memcpy_stub_ok W img <|
    hookOk_withStack hookMemcpy_region_ok stk
  session_memcpy_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memcpy_stub_ok W img <| hookOk_withStack hookMemcpy_region_trace_ok stk
  memmove stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memmove_stub_ok W img <|
    hookMemmove_ok stk
  session_memmove stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memmove_stub_ok W img <|
    hookMemmove_trace_ok stk
  memset stk hle _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_stub_ok W img <|
    hookMemset_ok stk (pos_of_extHookStack_le hle)
  session_memset stk hle _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_stub_ok W img <|
    hookMemset_trace_ok stk (pos_of_extHookStack_le hle)
  memset_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <| memset_stub_ok W img <|
    hookOk_withStack hookMemset_region_ok stk
  session_memset_region stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    memset_stub_ok W img <| hookOk_withStack hookMemset_region_trace_ok stk

theorem allocContractsFs_cli (W : CliHooks) (img : Obj.Image) :
    AllocContractsFs img E2E.HooksE.A0 (cliExterns W) :=
  AllocContractsFs.of_hooks W img cliAllocHooks_A0

theorem allocContractsX_cli (W : CliHooks) (img : Obj.Image) :
    AllocContractsX img E2E.HooksE.A0 (cliExterns W) :=
  AllocContractsX.of_hooks W img cliAllocHooks_A0

/-! ## Read-Only-Source `memcpy` -/

theorem cli_hookSat_memcpy_region_ro (W : CliHooks) :
    HookSat (cliExterns W) memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
  ⟨hookMemcpy, cliExterns_row W (memcpy_row W),
    CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok⟩

/-- Read-only-source `memcpy` (`sessionMemcpyRegionROSpec`) at `cliExterns W` with `.keepsFs` and
stack frame `extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem cli_session_memcpy_region_ro (W : CliHooks) (img : Obj.Image) :
    ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr memcpyName)
        ((withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).keepsFs.inImage
          img) :=
  fun stk _ _ => subroutine_ok_inImage_of_subroutine_ok img <| memcpy_stub_ok W img <|
    (hookOk_withStack CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok stk).keepsFs
      hookMemcpy_fs

theorem cli_session_memcpy_region_ro_x (W : CliHooks) (img : Obj.Image) :
    ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr memcpyName)
        ((withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).inImage img) :=
  fun stk _ _ => subroutine_ok_inImage_of_subroutine_ok img <| memcpy_stub_ok W img <|
    hookOk_withStack CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok stk

/-! ## Parametric Constructors from `CliExternsOk` -/

private theorem hookSat_cliExternsWith_map {α β : Type}
    {ext : String → Option (State → State)} {name : String}
    {s₁ : Spec α} {s₂ : Spec β}
    (hnp : E2E.isImagePanicSymbol name = false)
    (hsat : HookSat ext name s₁)
    (hmap : ∀ f, ext name = some f → HookOk f s₁ → HookOk f s₂) :
    HookSat (cliExternsWith ext) name s₂ := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnp).trans hf, hmap f hf hok⟩

private theorem ext_stub_ok {α : Type} (img : Obj.Image)
    (ext : String → Option (State → State)) {name : String}
    {spec : Spec α} {stub : Nat}
    (hfn : libsignalSessionCode.fnOff name = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? stub = H name)
    (hnp : Rust.isPanicSymbol name = false)
    (hsat : HookSat (cliExternsWith ext) name spec) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr name) spec := by
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base)
    (hooks := cliExternsWith ext) (hname := name) (k := 0) hfn (Nat.add_zero _) hs hstub hnp hsat
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

private theorem hookOk_conseq {α β : Type} {f : State → State} {spec₁ : Spec α} {spec₂ : Spec β}
    (hh : HookOk f spec₁)
    (hstep : ∀ (x : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec₂.pre x s0 ∗ R) →
      ∃ (y : α) (F : SepProp),
        (s0.mem ⊨ spec₁.pre y s0 ∗ (F ∗ R)) ∧
        ∀ sf, (sf.mem ⊨ spec₁.post y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec₂.post x s0 sf ∗ R))
    (hpan₁ : ∀ y s0 sf, spec₁.onPanic y s0 sf = ⌜False⌝ := by intros; rfl)
    (hex₁ : ∀ y code s0 sf, spec₁.onExit y code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom₁ : ∀ y s0 sf, spec₁.onOom y s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f spec₂ := by
  intro x R s0 hrun hpre hsp
  obtain ⟨y, F, hpre₁, hpost₁⟩ := hstep x R s0 hpre
  obtain ⟨hkf, hsym, hout⟩ := hh y (F ∗ R) s0 hrun hpre₁ hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost₁ (f s0) hpost⟩
  · rw [hpan₁ y s0 (f s0), satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · rw [hex₁ y code s0 (f s0), satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · rw [hoom₁ y s0 (f s0), satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem stackAt_split_ge {sp : BitVec 64} {inner stk : Nat}
    (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - inner) ∗ stackAt sp inner := by
  have h1 := stackAt_split_bottom sp inner (stk - inner) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

private theorem memHookStack_le_of_ext {stk : Nat} (hle : extHookStack ≤ stk) :
    CliExt.memHookStack ≤ stk :=
  Nat.le_trans (by decide : CliExt.memHookStack ≤ extHookStack) hle

private theorem hookOk_shim_of_cliExt {f : State → State} (hh : HookOk f CliExt.shimSpec) :
    HookOk f sessionShimSpec :=
  hookOk_conseq hh fun u R s0 hpre => ⟨u, emp,
    by simpa [CliExt.shimSpec, sessionShimSpec, emp_sepConj] using hpre,
    fun sf hpost => by simpa [CliExt.shimSpec, sessionShimSpec, emp_sepConj] using hpost⟩

private theorem hookOk_sessionMemcpy_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpySpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpySpec stk) := by
  refine hookOk_conseq hh fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(dst, src, bs), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack), ?_, ?_⟩
  · dsimp only [sessionMemcpySpec, CliExt.memcpySpec, libcMemcpySpec] at hpre ⊢
    rw [hsp] at hpre; ac_nf at hpre ⊢
  · intro sf hpost
    dsimp only [sessionMemcpySpec, CliExt.memcpySpec] at hpost ⊢
    rw [hsp]; ac_nf at hpost ⊢

private theorem hookOk_libcMemcpy_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpySpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemcpySpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemcpy_of_cliExt hh stk hle hmax)
    fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), emp,
      by simpa [sessionMemcpySpec, libcMemcpySpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

private theorem hookOk_sessionMemcpyRegion_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpySpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack sessionMemcpyRegionSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemcpy_of_cliExt hh stk hle hmax)
    fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), emp, ?_, ?_⟩
  · dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sessionMemcpySpec,
      libcMemcpySpec] at hpre ⊢
    simp only [emp_sepConj]; ac_nf at hpre ⊢
  · intro sf hpost
    dsimp only [withStack, sessionMemcpyRegionSpec, sessionMemcpySpec] at hpost ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩; have h2 := hpost.2; ac_nf at h2 ⊢

private theorem hookOk_memcpyRegion_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpySpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack memcpyRegionSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemcpyRegion_of_cliExt hh stk hle hmax)
    fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), emp,
      by simpa [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

private theorem hookOk_sessionMemcpyRegionRO_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpyROSpec) (stk : Nat)
    (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk) := by
  refine hookOk_conseq hh fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) hle hmax
  refine ⟨(dst, src, bs), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack), ?_, ?_⟩
  · dsimp only [withStack, CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec,
      CliExt.memcpyROSpec, CliExt.withStack] at hpre ⊢
    rw [hsp] at hpre; ac_nf at hpre ⊢
  · intro sf hpost
    dsimp only [withStack, CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec,
      CliExt.memcpyROSpec, CliExt.withStack] at hpost ⊢
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩; have h2 := hpost.2; ac_nf at h2 ⊢

private theorem hookOk_sessionMemmove_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memmoveSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemmoveSpec stk) := by
  refine hookOk_conseq hh fun ⟨base, buf, dst, src, len⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(base, buf, dst, src, len),
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack), ?_, ?_⟩
  · dsimp only [sessionMemmoveSpec, CliExt.memmoveSpec, libcMemmoveSpec] at hpre ⊢
    rw [hsp] at hpre; ac_nf at hpre ⊢
  · intro sf hpost
    dsimp only [sessionMemmoveSpec, CliExt.memmoveSpec] at hpost ⊢
    rw [hsp]; ac_nf at hpost ⊢

private theorem hookOk_libcMemmove_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memmoveSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemmoveSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemmove_of_cliExt hh stk hle hmax)
    fun x R s0 hpre => ⟨x, emp,
      by simpa [sessionMemmoveSpec, libcMemmoveSpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [sessionMemmoveSpec, libcMemmoveSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

private theorem hookOk_sessionMemset_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memsetSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemsetSpec stk) := by
  refine hookOk_conseq hh fun ⟨ptr, c, len⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(ptr, c, len), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack), ?_, ?_⟩
  · dsimp only [sessionMemsetSpec, CliExt.memsetSpec, libcMemsetSpec] at hpre ⊢
    rw [hsp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2⟩, ?_⟩
    have h2 := hpre.2; ac_nf at h2 ⊢
  · intro sf hpost
    dsimp only [sessionMemsetSpec, CliExt.memsetSpec] at hpost ⊢
    rw [hsp]; ac_nf at hpost ⊢

private theorem hookOk_libcMemset_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memsetSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemsetSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemset_of_cliExt hh stk hle hmax)
    fun x R s0 hpre => ⟨x, emp,
      by simpa [sessionMemsetSpec, libcMemsetSpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [sessionMemsetSpec, libcMemsetSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

private theorem hookOk_sessionMemsetRegion_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memsetSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack sessionMemsetRegionSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemset_of_cliExt hh stk hle hmax)
    fun ⟨ptr, c, len⟩ R s0 hpre => ⟨(ptr, c, len), emp, ?_, ?_⟩
  · dsimp only [withStack, sessionMemsetRegionSpec, memsetRegionSpec, sessionMemsetSpec,
      libcMemsetSpec] at hpre ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, ?_⟩
    have h2 := hpre.2; ac_nf at h2 ⊢
  · intro sf hpost
    dsimp only [withStack, sessionMemsetRegionSpec, sessionMemsetSpec] at hpost ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩; have h2 := hpost.2; ac_nf at h2 ⊢

private theorem hookOk_memsetRegion_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memsetSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack memsetRegionSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemsetRegion_of_cliExt hh stk hle hmax)
    fun x R s0 hpre => ⟨x, emp,
      by simpa [withStack, sessionMemsetRegionSpec, memsetRegionSpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [withStack, sessionMemsetRegionSpec, memsetRegionSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

private theorem alloc_nonPanicE : E2E.isImagePanicSymbol allocName = false := by
  simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, allocName]
private theorem dealloc_nonPanicE : E2E.isImagePanicSymbol deallocName = false := by
  simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, deallocName]
private theorem realloc_nonPanicE : E2E.isImagePanicSymbol reallocName = false := by
  simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, reallocName]
private theorem shim_nonPanicE : E2E.isImagePanicSymbol shimName = false := by
  simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, shimName]
private theorem memcpy_nonPanicE : E2E.isImagePanicSymbol memcpyName = false := by
  simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, memcpyName]
private theorem memmove_nonPanicE : E2E.isImagePanicSymbol memmoveName = false := by
  simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, memmoveName]
private theorem memset_nonPanicE : E2E.isImagePanicSymbol memsetName = false := by
  simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, memsetName]

private theorem alloc_notIo : allocName ∉ CliExt.ioNames := by
  simp [CliExt.ioNames, allocName, SignalSession.readFileName, writeFileName, readStdinName, writeStdoutName]
private theorem dealloc_notIo : deallocName ∉ CliExt.ioNames := by
  simp [CliExt.ioNames, deallocName, SignalSession.readFileName, writeFileName, readStdinName, writeStdoutName]
private theorem realloc_notIo : reallocName ∉ CliExt.ioNames := by
  simp [CliExt.ioNames, reallocName, SignalSession.readFileName, writeFileName, readStdinName, writeStdoutName]
private theorem shim_notIo : shimName ∉ CliExt.ioNames := by
  simp [CliExt.ioNames, shimName, SignalSession.readFileName, writeFileName, readStdinName, writeStdoutName]
private theorem memcpy_notIo : memcpyName ∉ CliExt.ioNames := by
  simp [CliExt.ioNames, memcpyName, SignalSession.readFileName, writeFileName, readStdinName, writeStdoutName]
private theorem memmove_notIo : memmoveName ∉ CliExt.ioNames := by
  simp [CliExt.ioNames, memmoveName, SignalSession.readFileName, writeFileName, readStdinName, writeStdoutName]
private theorem memset_notIo : memsetName ∉ CliExt.ioNames := by
  simp [CliExt.ioNames, memsetName, SignalSession.readFileName, writeFileName, readStdinName, writeStdoutName]

/-- Constructs `AllocContractsX` on `mProg img (cliExternsWith ext)` from `CliExternsOk P A ext`. -/
theorem allocContractsX_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : CliExternsOk P A ext) :
    AllocContractsX img A (cliExternsWith ext) where
  alloc := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext alloc_fnOff (by decide) (ls_hook% "__rustc::__rust_alloc")
      (by simp [Rust.isPanicSymbol, allocName]) <|
      hookSat_cliExternsWith_map alloc_nonPanicE hOk.alloc.alloc fun _ _ h =>
        hookOk_rustAllocWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
          extHookStack_le
  dealloc := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext dealloc_fnOff (by decide) (ls_hook% "__rustc::__rust_dealloc")
      (by simp [Rust.isPanicSymbol, deallocName]) <|
      hookSat_cliExternsWith_map dealloc_nonPanicE hOk.alloc.dealloc fun _ _ h =>
        hookOk_rustDeallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
          extHookStack_le
  realloc := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext realloc_fnOff (by decide) (ls_hook% "__rustc::__rust_realloc")
      (by simp [Rust.isPanicSymbol, reallocName]) <|
      hookSat_cliExternsWith_map realloc_nonPanicE hOk.alloc.realloc fun _ _ h =>
        hookOk_rustReallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
          extHookStack_le
  shim stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext shim_fnOff (by decide)
      (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (by simp [Rust.isPanicSymbol, shimName]) <|
      hookSat_cliExternsWith_map shim_nonPanicE hOk.shim fun _ _ h =>
        hookOk_withStack (hookOk_shim_of_cliExt h) stk
  memcpy stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun _ _ h =>
        hookOk_libcMemcpy_of_cliExt h stk hle hmax
  session_memcpy stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun _ _ h =>
        hookOk_sessionMemcpy_of_cliExt h stk hle hmax
  memcpy_region stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun _ _ h =>
        hookOk_memcpyRegion_of_cliExt h stk hle hmax
  session_memcpy_region stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun _ _ h =>
        hookOk_sessionMemcpyRegion_of_cliExt h stk hle hmax
  memmove stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memmove_fnOff (by decide) (ls_hook% "memmove")
      (by simp [Rust.isPanicSymbol, memmoveName]) <|
      hookSat_cliExternsWith_map memmove_nonPanicE hOk.memmove fun _ _ h =>
        hookOk_libcMemmove_of_cliExt h stk hle hmax
  session_memmove stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memmove_fnOff (by decide) (ls_hook% "memmove")
      (by simp [Rust.isPanicSymbol, memmoveName]) <|
      hookSat_cliExternsWith_map memmove_nonPanicE hOk.memmove fun _ _ h =>
        hookOk_sessionMemmove_of_cliExt h stk hle hmax
  memset stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memset_fnOff (by decide) (ls_hook% "memset")
      (by simp [Rust.isPanicSymbol, memsetName]) <|
      hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun _ _ h =>
        hookOk_libcMemset_of_cliExt h stk hle hmax
  session_memset stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memset_fnOff (by decide) (ls_hook% "memset")
      (by simp [Rust.isPanicSymbol, memsetName]) <|
      hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun _ _ h =>
        hookOk_sessionMemset_of_cliExt h stk hle hmax
  memset_region stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memset_fnOff (by decide) (ls_hook% "memset")
      (by simp [Rust.isPanicSymbol, memsetName]) <|
      hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun _ _ h =>
        hookOk_memsetRegion_of_cliExt h stk hle hmax
  session_memset_region stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memset_fnOff (by decide) (ls_hook% "memset")
      (by simp [Rust.isPanicSymbol, memsetName]) <|
      hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun _ _ h =>
        hookOk_sessionMemsetRegion_of_cliExt h stk hle hmax

/-- Constructs `AllocContractsFs` on `mProg img (cliExternsWith ext)` from `CliExternsOk P A ext`. -/
theorem allocContractsFs_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : CliExternsOk P A ext) :
    AllocContractsFs img A (cliExternsWith ext) where
  alloc := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext alloc_fnOff (by decide) (ls_hook% "__rustc::__rust_alloc")
      (by simp [Rust.isPanicSymbol, allocName]) <|
      hookSat_cliExternsWith_map alloc_nonPanicE hOk.alloc.alloc fun f hf h =>
        (hookOk_rustAllocWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
          extHookStack_le).keepsFs (hOk.fsKept _ f hf alloc_notIo)
  dealloc := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext dealloc_fnOff (by decide) (ls_hook% "__rustc::__rust_dealloc")
      (by simp [Rust.isPanicSymbol, deallocName]) <|
      hookSat_cliExternsWith_map dealloc_nonPanicE hOk.alloc.dealloc fun f hf h =>
        (hookOk_rustDeallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
          extHookStack_le).keepsFs (hOk.fsKept _ f hf dealloc_notIo)
  realloc := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext realloc_fnOff (by decide) (ls_hook% "__rustc::__rust_realloc")
      (by simp [Rust.isPanicSymbol, reallocName]) <|
      hookSat_cliExternsWith_map realloc_nonPanicE hOk.alloc.realloc fun f hf h =>
        (hookOk_rustReallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
          extHookStack_le).keepsFs (hOk.fsKept _ f hf realloc_notIo)
  shim stk _ _ := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext shim_fnOff (by decide)
      (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (by simp [Rust.isPanicSymbol, shimName]) <|
      hookSat_cliExternsWith_map shim_nonPanicE hOk.shim fun f hf h =>
        (hookOk_withStack (hookOk_shim_of_cliExt h) stk).keepsFs (hOk.fsKept _ f hf shim_notIo)
  memcpy stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
        (hookOk_libcMemcpy_of_cliExt h stk hle hmax).keepsFs (hOk.fsKept _ f hf memcpy_notIo)
  session_memcpy stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
        (hookOk_sessionMemcpy_of_cliExt h stk hle hmax).keepsFs (hOk.fsKept _ f hf memcpy_notIo)
  memcpy_region stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
        (hookOk_memcpyRegion_of_cliExt h stk hle hmax).keepsFs (hOk.fsKept _ f hf memcpy_notIo)
  session_memcpy_region stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
        (hookOk_sessionMemcpyRegion_of_cliExt h stk hle hmax).keepsFs
          (hOk.fsKept _ f hf memcpy_notIo)
  memmove stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memmove_fnOff (by decide) (ls_hook% "memmove")
      (by simp [Rust.isPanicSymbol, memmoveName]) <|
      hookSat_cliExternsWith_map memmove_nonPanicE hOk.memmove fun f hf h =>
        (hookOk_libcMemmove_of_cliExt h stk hle hmax).keepsFs (hOk.fsKept _ f hf memmove_notIo)
  session_memmove stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memmove_fnOff (by decide) (ls_hook% "memmove")
      (by simp [Rust.isPanicSymbol, memmoveName]) <|
      hookSat_cliExternsWith_map memmove_nonPanicE hOk.memmove fun f hf h =>
        (hookOk_sessionMemmove_of_cliExt h stk hle hmax).keepsFs (hOk.fsKept _ f hf memmove_notIo)
  memset stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memset_fnOff (by decide) (ls_hook% "memset")
      (by simp [Rust.isPanicSymbol, memsetName]) <|
      hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
        (hookOk_libcMemset_of_cliExt h stk hle hmax).keepsFs (hOk.fsKept _ f hf memset_notIo)
  session_memset stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memset_fnOff (by decide) (ls_hook% "memset")
      (by simp [Rust.isPanicSymbol, memsetName]) <|
      hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
        (hookOk_sessionMemset_of_cliExt h stk hle hmax).keepsFs (hOk.fsKept _ f hf memset_notIo)
  memset_region stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memset_fnOff (by decide) (ls_hook% "memset")
      (by simp [Rust.isPanicSymbol, memsetName]) <|
      hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
        (hookOk_memsetRegion_of_cliExt h stk hle hmax).keepsFs (hOk.fsKept _ f hf memset_notIo)
  session_memset_region stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memset_fnOff (by decide) (ls_hook% "memset")
      (by simp [Rust.isPanicSymbol, memsetName]) <|
      hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
        (hookOk_sessionMemsetRegion_of_cliExt h stk hle hmax).keepsFs
          (hOk.fsKept _ f hf memset_notIo)
  session_memcpy_region_ro stk hle hmax := subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpyRO fun f hf h =>
        (hookOk_sessionMemcpyRegionRO_of_cliExt h stk (memHookStack_le_of_ext hle) hmax).keepsFs
          (hOk.fsKept _ f hf memcpy_notIo)

theorem AllocContractsX.of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    AllocContractsX img A (cliExternsWith ext) :=
  allocContractsX_of_externsOk img hOk

theorem AllocContractsFs.of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    AllocContractsFs img A (cliExternsWith ext) :=
  allocContractsFs_of_externsOk img hOk

/-- `HookSat` for `sessionMemcpyRegionROSpecWithStack stk` on `cliExternsWith ext` (`memHookStack ≤ stk ≤ 2 ^ 64`). -/
theorem memcpyRegionRO_withStack_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    (stk : Nat) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack stk) :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpyRO fun _ _ hh =>
    hookOk_conseq (hookOk_sessionMemcpyRegionRO_of_cliExt hh stk hle hmax)
      fun ⟨dst, src, bs⟩ R s0 hpre =>
        ⟨(dst, src, bs), emp,
          by
            dsimp only [withStack,
              CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack,
              CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec] at hpre ⊢
            simp only [emp_sepConj]; ac_nf at hpre ⊢,
          fun sf hpost => by
            dsimp only [withStack,
              CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack,
              CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec] at hpost ⊢
            simp only [emp_sepConj] at hpost; ac_nf at hpost ⊢⟩

theorem memcpyRegionRO_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack CliExt.memHookStack) :=
  memcpyRegionRO_withStack_of_externsOk hOk CliExt.memHookStack (Nat.le_refl _) (by decide)

theorem memcpyRegionRO_X_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) memcpyName
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecX := by
  have h := memcpyRegionRO_withStack_of_externsOk hOk extHookStack (by decide) extHookStack_le
  exact h

/-- Read-only-source `memcpy` with `.keepsFs` on `mProg img (cliExternsWith ext)` from `CliExternsOk`. -/
theorem ext_session_memcpy_region_ro {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      subroutine_ok (mProg img (cliExternsWith ext))
        ((mProg img (cliExternsWith ext)).fnAddr memcpyName)
        ((withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).keepsFs.inImage
          img) :=
  (allocContractsFs_of_externsOk img hOk).session_memcpy_region_ro

theorem ext_session_memcpy_region_ro_x {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
      subroutine_ok (mProg img (cliExternsWith ext))
        ((mProg img (cliExternsWith ext)).fnAddr memcpyName)
        ((withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).inImage img) :=
  fun stk hle hmax => subroutine_ok_inImage_of_subroutine_ok img <|
    ext_stub_ok img ext memcpy_fnOff (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) <|
      hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpyRO fun _ _ h =>
        hookOk_sessionMemcpyRegionRO_of_cliExt h stk (memHookStack_le_of_ext hle) hmax

end CryptoVerification.SignalSession.Cli.MainHops
