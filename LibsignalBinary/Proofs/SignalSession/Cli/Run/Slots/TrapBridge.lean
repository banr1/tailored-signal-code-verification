/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import ProofLib.SepLogic.WP.StateNorm

/-!
# Trap-at-RNG and Unlisted-Stub Program Bridges (`trTrapProgAt` and `trapUnlisted`)

Bridges subroutine proofs from `trTrapProgAt b W.C (cliExterns W)` (where `libsignal_session_rng_fill`
traps via `rngTrap`) to the CLI program `tripleRatchetProgAtExt b (cliExterns W)` via `TrapsOnly`
(`trapsOnly_trTrap_cli`, `subroutine_ok_cli_of_trTrap`). Neither `TrapsOnly kit cli` nor
`TrapsOnly cli kit` holds directly because the kit installs a returning `rngFillHook` at
`rngFillName` (`0x97388`) whereas `cliHookTable` leaves `rngFillName` unhooked.

Also defines `trapUnlisted ext`, replacing every non-panic symbol outside `cliHookNames` with
`rngTrap` while preserving `CliExternsOk P A`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib ProofLib.Variant CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet

/-- Away from `rngFillName`, `Rust.withPanics (tripleRatchetExterns W.C ctl (cliExterns W))` agrees
pointwise with `Rust.withPanics (cliExterns W)`. -/
theorem cliExterns_agree (W : CliHooks) (ctl : BitVec 64) {n : String} (hn : n ≠ rngFillName) :
    Rust.withPanics (tripleRatchetExterns W.C ctl (cliExterns W)) n =
      Rust.withPanics (cliExterns W) n := by
  rw [withPanics_cliExterns]
  by_cases hp : Rust.isPanicSymbol n = true
  · have hpC : isCliPanicSymbol n = true := isCliPanicSymbol_of_isPanicSymbol hp
    unfold cliExterns withCliPanics
    simp [Rust.withPanics, hp, hpC]
  · simp only [Rust.withPanics, hp, Bool.false_eq_true, ↓reduceIte]
    by_cases hk : n ∈ kitOwnNames
    · simp only [kitOwnNames, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      simp [tripleRatchetExterns, CryptoVerification.LibsignalSession.sessionExterns,
        dhName, pubFromSecretName, staticDropName, sharedDropName, rngFillName, noHookNames] <;>
      first
        | (unfold cliExterns withCliPanics
           simp [isCliPanicSymbol, E2E.isImagePanicSymbol, E2E.extraImagePanicNames,
             deadCliHashbrownPanicNames]; done)
        | (refine (cliExterns_row W ?_).symm
           simp [cliHookTable])
        | (refine (cliExterns_none_of_not_imagePanic W ?_ ?_).symm
           · decide +kernel
           · simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames])
    · exact tripleRatchetExterns_of_not_mem W.C ctl (cliExterns W) hk hn

/-- `TrapsOnly` from `trTrapProgAt b W.C (cliExterns W)` to `tripleRatchetProgAtExt b (cliExterns W)`. -/
theorem trapsOnly_trTrap_cli (b : BitVec 64) (W : CliHooks) :
    TrapsOnly (trTrapProgAt b W.C (cliExterns W)) (tripleRatchetProgAtExt b (cliExterns W)) := by
  refine TrapsOnly.rebase libsignalSessionCode b ?_
  intro n
  by_cases hr : n = rngFillName
  · subst hr
    by_cases hp : Rust.isPanicSymbol rngFillName = true
    · left; simp [Rust.withPanics, hp]
    · right
      refine ⟨rngTrap, ?_, rngTrap_isTrap⟩
      simp [Rust.withPanics, trTrapExterns, ProofLib.Variant.trapAt, hp]
  · left
    rw [withPanics_trTrap_ne W.C (cliExterns W) hr]
    exact cliExterns_agree W 0#64 hr

/-- Transfers `subroutine_ok` from `trTrapProgAt b W.C (cliExterns W)` to `tripleRatchetProgAtExt b (cliExterns W)`. -/
theorem subroutine_ok_cli_of_trTrap {α : Type} {b : BitVec 64} {W : CliHooks} {name : String}
    {spec : Spec α}
    (h : subroutine_ok (trTrapProgAt b W.C (cliExterns W))
      ((trTrapProgAt b W.C (cliExterns W)).fnAddr name) spec) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExterns W))
      ((tripleRatchetProgAtExt b (cliExterns W)).fnAddr name) spec := by
  rw [← (trapsOnly_trTrap_cli b W).fnAddr name]
  exact subroutine_ok.of_trapsOnly (trapsOnly_trTrap_cli b W) h

/-! ## Unlisted-stub trap bridge (`trapUnlisted`) for `CliExternsOk` -/

set_option autoImplicit false

local macro "in_cli_hooks" : tactic => `(tactic|
  simp [cliHookNames, E2E.compress512Name, E2E.toEdwardsName, E2E.compressName, E2E.edNegName,
    E2E.torsionFreeName, E2E.dsmbName, E2E.scalarModName, E2E.scalarWideName,
    E2E.kemEncapsName, E2E.kemDecapsName,
    LibsignalSpqrV1.mlkemFromSeedName, LibsignalSpqrV1.mlkemPk1Name,
    LibsignalSpqrV1.mlkemPk2Name, LibsignalSpqrV1.mlkemEncaps1Name,
    LibsignalSpqrV1.mlkemEncaps2Name, LibsignalSpqrV1.mlkemDecapsName,
    LibsignalSpqrV1.mlkemValidatePkName, LibsignalSpqrV1.libcruxHmacName,
    SignalSession.readFileName, SignalSession.writeFileName,
    SignalSession.readStdinName, SignalSession.writeStdoutName,
    allocZeroedName, aesEncName, aesDecName, formatInnerName, fmtWriteName,
    LibsignalPublicApi.durationSinceHookName,
    LibsignalPublicApi.timeAddHookName, pubFromSecretName, dhName, staticDropName, sharedDropName,
    allocName, deallocName, reallocName])

theorem cliHookNames_notPanic_std3 :
    cliHookNames.all (fun n => !E2E.isImagePanicSymbol n) = true := by
  rw [List.all_eq_true]
  intro n hn
  simp only [cliHookNames, E2E.compress512Name, E2E.toEdwardsName, E2E.compressName, E2E.edNegName,
    E2E.torsionFreeName, E2E.dsmbName, E2E.scalarModName, E2E.scalarWideName,
    E2E.kemEncapsName, E2E.kemDecapsName,
    LibsignalSpqrV1.mlkemFromSeedName, LibsignalSpqrV1.mlkemPk1Name,
    LibsignalSpqrV1.mlkemPk2Name, LibsignalSpqrV1.mlkemEncaps1Name,
    LibsignalSpqrV1.mlkemEncaps2Name, LibsignalSpqrV1.mlkemDecapsName,
    LibsignalSpqrV1.mlkemValidatePkName, LibsignalSpqrV1.libcruxHmacName,
    SignalSession.readFileName, SignalSession.writeFileName,
    SignalSession.readStdinName, SignalSession.writeStdoutName,
    List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames]

theorem isPanicSymbolE_false_of_mem_cliHookNames {n : String} (hn : n ∈ cliHookNames) :
    E2E.isImagePanicSymbol n = false := by
  have h := List.all_eq_true.mp cliHookNames_notPanic_std3 n hn
  simpa using h

theorem isCliPanicSymbol_false_of_mem_cliHookNames {n : String} (hn : n ∈ cliHookNames) :
    isCliPanicSymbol n = false :=
  isCliPanicSymbol_eq_false_of_isImagePanicSymbol_false (isPanicSymbolE_false_of_mem_cliHookNames hn)

theorem cliExternsWith_of_not_panic (ext : String → Option (State → State)) {n : String}
    (h : E2E.isImagePanicSymbol n = false) :
    cliExternsWith ext n = ext n := by
  simp [cliExternsWith, h]

theorem cliExternsWith_of_not_cliPanic (ext : String → Option (State → State)) {n : String}
    (h : isCliPanicSymbol n = false) :
    cliExternsWith ext n = ext n := by
  simp [cliExternsWith, h]

theorem cliExternsWith_eq_of_mem {ext : String → Option (State → State)} {n : String}
    (hn : n ∈ cliHookNames) :
    cliExternsWith ext n = ext n :=
  cliExternsWith_of_not_panic ext (isPanicSymbolE_false_of_mem_cliHookNames hn)

theorem withPanics_cliExternsWith (ext : String → Option (State → State)) :
    Rust.withPanics (cliExternsWith ext) = cliExternsWith ext :=
  withPanics_withCliPanics ext

theorem cliExternsWith_allocErr (ext : String → Option (State → State)) :
    cliExternsWith ext "alloc::alloc::handle_alloc_error" = some Rust.panicked :=
  withCliPanics_of_isPanicSymbol_true ext (by simp [Rust.isPanicSymbol])

theorem hookSat_cliExternsWith {α : Type} {ext : String → Option (State → State)} {n : String}
    {spec : Spec α} (h : E2E.isImagePanicSymbol n = false) (hs : HookSat ext n spec) :
    HookSat (cliExternsWith ext) n spec := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, (cliExternsWith_of_not_panic ext h).trans hf, hok⟩

theorem hookSat_cliExternsWith_of_mem {α : Type} {ext : String → Option (State → State)} {n : String}
    {spec : Spec α} (hn : n ∈ cliHookNames) (hs : HookSat ext n spec) :
    HookSat (cliExternsWith ext) n spec :=
  hookSat_cliExternsWith (isPanicSymbolE_false_of_mem_cliHookNames hn) hs

/-- Wraps `cliExternsWith ext` so every non-panic symbol outside `cliHookNames` traps via `rngTrap`,
enabling `TrapsOnly` transfer to `cliExternsWith ext` without contracts on unlisted stubs. -/
noncomputable def trapUnlisted (ext : String → Option (State → State)) :
    String → Option (State → State) :=
  ProofLib.Variant.trapAt
    (fun n => !decide (n ∈ cliHookNames) && !isCliPanicSymbol n)
    rngTrap
    (cliExternsWith ext)

theorem trapUnlisted_eq_of_mem {ext : String → Option (State → State)} {n : String}
    (hn : n ∈ cliHookNames) :
    trapUnlisted ext n = ext n := by
  simp [trapUnlisted, ProofLib.Variant.trapAt, hn, cliExternsWith_eq_of_mem hn]

theorem trapUnlisted_of_not_panic_not_mem {ext : String → Option (State → State)} {n : String}
    (hmem : n ∉ cliHookNames) (hp : isCliPanicSymbol n = false) :
    trapUnlisted ext n = some rngTrap := by
  simp [trapUnlisted, ProofLib.Variant.trapAt, hmem, hp]

theorem cliExternsWith_trapUnlisted (ext : String → Option (State → State)) :
    cliExternsWith (trapUnlisted ext) = trapUnlisted ext := by
  funext n
  by_cases hp : isCliPanicSymbol n = true
  · simp [cliExternsWith, trapUnlisted, ProofLib.Variant.trapAt, withCliPanics, hp]
  · simp [cliExternsWith, withCliPanics, hp]

theorem withPanics_trapUnlisted (ext : String → Option (State → State)) :
    Rust.withPanics (trapUnlisted ext) = trapUnlisted ext := by
  rw [← cliExternsWith_trapUnlisted ext, withPanics_cliExternsWith]

theorem hookSat_trapUnlisted {α : Type} {ext : String → Option (State → State)} {n : String}
    {spec : Spec α} (hn : n ∈ cliHookNames) (h : HookSat ext n spec) :
    HookSat (trapUnlisted ext) n spec := by
  obtain ⟨f, hf, hok⟩ := h
  exact ⟨f, (trapUnlisted_eq_of_mem hn).trans hf, hok⟩

theorem hooksTrapOnly_trapUnlisted (ext : String → Option (State → State)) :
    HooksTrapOnly (Rust.withPanics (trapUnlisted ext)) (Rust.withPanics (cliExternsWith ext)) := by
  intro n
  by_cases hp : Rust.isPanicSymbol n = true
  · left
    simp [Rust.withPanics, hp]
  · simp only [Rust.withPanics, hp, Bool.false_eq_true, ↓reduceIte]
    exact HooksTrapOnly.trapAt rngTrap_isTrap (cliExternsWith ext) n

theorem trapsOnly_trapUnlisted (b : BitVec 64) (ext : String → Option (State → State)) :
    TrapsOnly (tripleRatchetProgAtExt b (trapUnlisted ext))
      (tripleRatchetProgAtExt b (cliExternsWith ext)) :=
  TrapsOnly.rebase libsignalSessionCode b (hooksTrapOnly_trapUnlisted ext)

theorem subroutine_ok_of_trapUnlisted {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt b (trapUnlisted ext)) entry spec) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext)) entry spec :=
  subroutine_ok.of_trapsOnly (trapsOnly_trapUnlisted b ext) h

theorem subroutine_ok_cliExternsWith_of_trapUnlisted {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt b (trapUnlisted ext))
      ((tripleRatchetProgAtExt b (trapUnlisted ext)).fnAddr name) spec) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr name) spec := by
  rw [← (trapsOnly_trapUnlisted b ext).fnAddr name]
  exact subroutine_ok.of_trapsOnly (trapsOnly_trapUnlisted b ext) h

theorem cliExternsWith_stub_ok {α : Type} (img : Obj.Image)
    {ext : String → Option (State → State)} {name : String} {spec : Spec α} {stub : Nat}
    (hfn : libsignalSessionCode.fnOff name = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? stub = H name)
    (hmem : name ∈ cliHookNames) (hnp : Rust.isPanicSymbol name = false)
    (hsat : HookSat ext name spec) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr name) spec := by
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base)
    (hooks := cliExternsWith ext) (hname := name) (k := 0) hfn (Nat.add_zero _) hs hstub hnp
    (hookSat_cliExternsWith_of_mem hmem hsat)
  simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

theorem trapUnlisted_stub_ok {α : Type} (img : Obj.Image)
    {ext : String → Option (State → State)} {name : String} {spec : Spec α} {stub : Nat}
    (hfn : libsignalSessionCode.fnOff name = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? stub = H name)
    (hmem : name ∈ cliHookNames) (hnp : Rust.isPanicSymbol name = false)
    (hsat : HookSat ext name spec) :
    subroutine_ok (tripleRatchetProgAtExt img.base (trapUnlisted ext))
      ((tripleRatchetProgAtExt img.base (trapUnlisted ext)).fnAddr name) spec := by
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base)
    (hooks := trapUnlisted ext) (hname := name) (k := 0) hfn (Nat.add_zero _) hs hstub hnp
    (hookSat_trapUnlisted hmem hsat)
  simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

theorem cliExternsOk_cliExternsWith {P : E2E.PEParams} {A : CryptoVerification.RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    CliExternsOk P A (cliExternsWith ext) where
  tpidr n f hf s := by
    unfold cliExternsWith withCliPanics at hf
    split at hf
    · cases hf; rfl
    · exact hOk.tpidr n f hf s
  noExec n f hf s a := by
    unfold cliExternsWith withCliPanics at hf
    split at hf
    · cases hf; exact id
    · exact hOk.noExec n f hf s a
  fsTraced n f hf := by
    unfold cliExternsWith withCliPanics at hf
    split at hf
    · cases hf; exact fun _ => FsTraced.of_eq rfl rfl
    · exact hOk.fsTraced n f hf
  fsKept n f hf hio s := by
    unfold cliExternsWith withCliPanics at hf
    split at hf
    · cases hf; rfl
    · exact hOk.fsKept n f hf hio s
  poolEmp := hOk.poolEmp
  shim := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.shim
  alloc := ⟨hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.alloc.alloc,
            hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.alloc.dealloc,
            hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.alloc.realloc⟩
  allocZeroed := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.allocZeroed
  memset := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.memset
  memmove := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.memmove
  memcpy := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.memcpy
  memcpyRO := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.memcpyRO
  bcmp := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.bcmp
  strlen := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.strlen
  readFile img := hookSat_cliExternsWith_of_mem (by in_cli_hooks) (hOk.readFile img)
  writeFile img := hookSat_cliExternsWith_of_mem (by in_cli_hooks) (hOk.writeFile img)
  readStdin img := hookSat_cliExternsWith_of_mem (by in_cli_hooks) (hOk.readStdin img)
  writeStdout img := hookSat_cliExternsWith_of_mem (by in_cli_hooks) (hOk.writeStdout img)
  memrchr := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.memrchr
  fromUtf8 := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.fromUtf8
  fmtWrite := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.fmtWrite
  formatInner := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.formatInner
  durationSince := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.durationSince
  timeAdd := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.timeAdd
  blackBox := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.blackBox
  compress256 := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.compress256
  aesEnc := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.aesEnc
  aesDec := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.aesDec
  pubFromSecret := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.pubFromSecret
  dh := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.dh
  staticDrop := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.staticDrop
  sharedDrop := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.sharedDrop
  compress512 := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.compress512
  toEdwards := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.toEdwards
  compress := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.compress
  edNeg := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.edNeg
  torsionFree := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.torsionFree
  dsmb := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.dsmb
  scalarMod := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.scalarMod
  scalarWide := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.scalarWide
  kemEncaps := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.kemEncaps
  kemDecaps := hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.kemDecaps
  spqr := ⟨hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.spqr.fromSeed,
           hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.spqr.pk1,
           hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.spqr.pk2,
           hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.spqr.encaps1,
           hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.spqr.encaps2,
           hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.spqr.decaps,
           hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.spqr.validatePk,
           hookSat_cliExternsWith_of_mem (by in_cli_hooks) hOk.spqr.hmac⟩

/-- `trapUnlisted ext` preserves `CliExternsOk P A`. -/
theorem cliExternsOk_trapUnlisted {P : E2E.PEParams} {A : CryptoVerification.RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    CliExternsOk P A (trapUnlisted ext) where
  tpidr n f hf s := by
    unfold trapUnlisted ProofLib.Variant.trapAt at hf
    split at hf
    · cases hf; rfl
    · exact (cliExternsOk_cliExternsWith hOk).tpidr n f hf s
  noExec n f hf s a := by
    unfold trapUnlisted ProofLib.Variant.trapAt at hf
    split at hf
    · cases hf; exact id
    · exact (cliExternsOk_cliExternsWith hOk).noExec n f hf s a
  fsTraced n f hf := by
    unfold trapUnlisted ProofLib.Variant.trapAt at hf
    split at hf
    · cases hf; exact fun _ => FsTraced.of_eq rfl rfl
    · exact (cliExternsOk_cliExternsWith hOk).fsTraced n f hf
  fsKept n f hf hio s := by
    unfold trapUnlisted ProofLib.Variant.trapAt at hf
    split at hf
    · cases hf; rfl
    · exact (cliExternsOk_cliExternsWith hOk).fsKept n f hf hio s
  poolEmp := hOk.poolEmp
  shim := hookSat_trapUnlisted (by in_cli_hooks) hOk.shim
  alloc := ⟨hookSat_trapUnlisted (by in_cli_hooks) hOk.alloc.alloc,
            hookSat_trapUnlisted (by in_cli_hooks) hOk.alloc.dealloc,
            hookSat_trapUnlisted (by in_cli_hooks) hOk.alloc.realloc⟩
  allocZeroed := hookSat_trapUnlisted (by in_cli_hooks) hOk.allocZeroed
  memset := hookSat_trapUnlisted (by in_cli_hooks) hOk.memset
  memmove := hookSat_trapUnlisted (by in_cli_hooks) hOk.memmove
  memcpy := hookSat_trapUnlisted (by in_cli_hooks) hOk.memcpy
  memcpyRO := hookSat_trapUnlisted (by in_cli_hooks) hOk.memcpyRO
  bcmp := hookSat_trapUnlisted (by in_cli_hooks) hOk.bcmp
  strlen := hookSat_trapUnlisted (by in_cli_hooks) hOk.strlen
  readFile img := hookSat_trapUnlisted (by in_cli_hooks) (hOk.readFile img)
  writeFile img := hookSat_trapUnlisted (by in_cli_hooks) (hOk.writeFile img)
  readStdin img := hookSat_trapUnlisted (by in_cli_hooks) (hOk.readStdin img)
  writeStdout img := hookSat_trapUnlisted (by in_cli_hooks) (hOk.writeStdout img)
  memrchr := hookSat_trapUnlisted (by in_cli_hooks) hOk.memrchr
  fromUtf8 := hookSat_trapUnlisted (by in_cli_hooks) hOk.fromUtf8
  fmtWrite := hookSat_trapUnlisted (by in_cli_hooks) hOk.fmtWrite
  formatInner := hookSat_trapUnlisted (by in_cli_hooks) hOk.formatInner
  durationSince := hookSat_trapUnlisted (by in_cli_hooks) hOk.durationSince
  timeAdd := hookSat_trapUnlisted (by in_cli_hooks) hOk.timeAdd
  blackBox := hookSat_trapUnlisted (by in_cli_hooks) hOk.blackBox
  compress256 := hookSat_trapUnlisted (by in_cli_hooks) hOk.compress256
  aesEnc := hookSat_trapUnlisted (by in_cli_hooks) hOk.aesEnc
  aesDec := hookSat_trapUnlisted (by in_cli_hooks) hOk.aesDec
  pubFromSecret := hookSat_trapUnlisted (by in_cli_hooks) hOk.pubFromSecret
  dh := hookSat_trapUnlisted (by in_cli_hooks) hOk.dh
  staticDrop := hookSat_trapUnlisted (by in_cli_hooks) hOk.staticDrop
  sharedDrop := hookSat_trapUnlisted (by in_cli_hooks) hOk.sharedDrop
  compress512 := hookSat_trapUnlisted (by in_cli_hooks) hOk.compress512
  toEdwards := hookSat_trapUnlisted (by in_cli_hooks) hOk.toEdwards
  compress := hookSat_trapUnlisted (by in_cli_hooks) hOk.compress
  edNeg := hookSat_trapUnlisted (by in_cli_hooks) hOk.edNeg
  torsionFree := hookSat_trapUnlisted (by in_cli_hooks) hOk.torsionFree
  dsmb := hookSat_trapUnlisted (by in_cli_hooks) hOk.dsmb
  scalarMod := hookSat_trapUnlisted (by in_cli_hooks) hOk.scalarMod
  scalarWide := hookSat_trapUnlisted (by in_cli_hooks) hOk.scalarWide
  kemEncaps := hookSat_trapUnlisted (by in_cli_hooks) hOk.kemEncaps
  kemDecaps := hookSat_trapUnlisted (by in_cli_hooks) hOk.kemDecaps
  spqr := ⟨hookSat_trapUnlisted (by in_cli_hooks) hOk.spqr.fromSeed,
           hookSat_trapUnlisted (by in_cli_hooks) hOk.spqr.pk1,
           hookSat_trapUnlisted (by in_cli_hooks) hOk.spqr.pk2,
           hookSat_trapUnlisted (by in_cli_hooks) hOk.spqr.encaps1,
           hookSat_trapUnlisted (by in_cli_hooks) hOk.spqr.encaps2,
           hookSat_trapUnlisted (by in_cli_hooks) hOk.spqr.decaps,
           hookSat_trapUnlisted (by in_cli_hooks) hOk.spqr.validatePk,
           hookSat_trapUnlisted (by in_cli_hooks) hOk.spqr.hmac⟩

end CryptoVerification.SignalSession.Cli.Slots
