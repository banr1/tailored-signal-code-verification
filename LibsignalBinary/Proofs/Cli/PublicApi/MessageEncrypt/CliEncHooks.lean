/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# CLI `MessageEncrypt` Hook Bundles

Defines `CliEncHooks` (using `durationSinceBoundedSpec` on `cliExterns W` / `trTrapExterns`) and
`CliEncHooksExt` (contract-backed hooks on `tripleRatchetProgAtExt`), together with call-distance
stepping lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Hook contract bundle for CLI `MessageEncrypt` on `trTrapProgAt` / `cliExterns`:
identical to `PublicApiHooksNoStores` except `durationSince` uses `durationSinceBoundedSpec`. -/
structure CliEncHooks (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S abs where
  timeAdd : HookSat abs timeAddHookName timeAddSpec
  durationSince : HookSat abs durationSinceHookName durationSinceBoundedSpec

theorem hookSat_trTrap_iff (C : Crypto) (abs : String → Option (State → State))
    {α : Type} {n : String} {spec : Spec α}
    (hk : n ∉ kitOwnNames) (hr : n ≠ rngFillName) :
    HookSat (trTrapExterns C abs) n spec ↔ HookSat abs n spec := by
  simp only [HookSat, trTrapExterns_of_not_mem C abs hk hr]

theorem allocHooks_trTrap_iff (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) :
    AllocHooks A (trTrapExterns C abs) ↔ AllocHooks A abs := by
  constructor
  · intro h
    exact ⟨(hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.alloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.dealloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.realloc⟩
  · intro h
    exact ⟨(hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.alloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.dealloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.realloc⟩

theorem tripleRatchetHooks_trTrap_iff (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) :
    TripleRatchetHooks C A S (trTrapExterns C abs) ↔ TripleRatchetHooks C A S abs := by
  constructor
  · intro h
    exact ⟨(allocHooks_trTrap_iff C A abs).mp h.alloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.allocZeroed,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.aesEnc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.aesDec,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.formatInner,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.fmtWrite⟩
  · intro h
    exact ⟨(allocHooks_trTrap_iff C A abs).mpr h.alloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.allocZeroed,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.aesEnc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.aesDec,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.formatInner,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.fmtWrite⟩

theorem cliEncHooks_trTrap_iff (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) :
    CliEncHooks C A S (trTrapExterns C abs) ↔ CliEncHooks C A S abs := by
  constructor
  · intro h
    exact ⟨(tripleRatchetHooks_trTrap_iff C A S abs).mp h.toTripleRatchetHooks,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.timeAdd,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.durationSince⟩
  · intro h
    exact ⟨(tripleRatchetHooks_trTrap_iff C A S abs).mpr h.toTripleRatchetHooks,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.timeAdd,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.durationSince⟩

/-- `CliEncHooks` holds directly on `cliExterns W` at `A := E2E.HooksE.A0`. -/
theorem cliEncHooks_cliExterns (W : CliHooks) (S : SpqrModel) :
    CliEncHooks W.C E2E.HooksE.A0 S (cliExterns W) where
  toTripleRatchetHooks := cliExterns_tripleRatchetHooks W S
  timeAdd := cliExterns_timeAdd W
  durationSince := cliExterns_durationSinceBounded W

/-- Instantiation of `CliEncHooks` at `A := E2E.HooksE.A0` and `abs := trTrapExterns W.C (cliExterns W)`. -/
theorem cliEncHooks_of_runHooks (W : CliHooks) (S : SpqrModel) :
    CliEncHooks W.C E2E.HooksE.A0 S (trTrapExterns W.C (cliExterns W)) :=
  (cliEncHooks_trTrap_iff W.C E2E.HooksE.A0 S (cliExterns W)).mpr (cliEncHooks_cliExterns W S)

/-- `__rustc::__rust_no_alloc_shim_is_unstable_v2` at call distance `k` from `name` on `trTrapProgAt`. -/
theorem cliNoAllocShim_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      sessionShimSpec :=
  shim_ok_at_trap b C abs name k hk

/-- `memcpy` (`framelessMemcpySpec`) at call distance `k` from `name` on `trTrapProgAt`. -/
theorem cliFramelessMemcpy_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) framelessMemcpySpec :=
  session_memcpy_region_ok_at_trap b C abs name k hk

/-- `__rust_alloc` at call distance `k` from `name` on `trTrapProgAt`, taking `AllocHooks A abs`. -/
theorem cliAlloc_ok_at_norm_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  alloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA) hk

/-- `__rust_dealloc` at call distance `k` from `name` on `trTrapProgAt`, taking `AllocHooks A abs`. -/
theorem cliDealloc_ok_at_norm_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA) hk

/-- Extract `AllocHooks A abs` from `CliEncHooks C A S (trTrapExterns C abs)`. -/
theorem CliEncHooks.alloc_abs {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : CliEncHooks C A S (trTrapExterns C abs)) : AllocHooks A abs :=
  (allocHooks_trTrap_iff C A abs).mp h.alloc

/-- `entryOf img name` equals `(trTrapProgAt img.base C abs).fnAddr name`. -/
theorem entryOf_eq_trTrapProgAt {img : Obj.Image} (C : Crypto)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (name : String) :
    entryOf img name = (trTrapProgAt img.base C abs).fnAddr name :=
  entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) himg name

/-! ## Contract-backed `Ext` hook bundle (`CliEncHooksExt`) and call-site helpers -/

/-- Contract-backed hook bundle for CLI `MessageEncrypt` on `tripleRatchetProgAtExt img.base ext`:
carries `TripleRatchetHooks`, `shim`, stacked `mem*` (`memHookStack = allocHookStack = 4096`),
`timeAdd`, and `CliExt.durationSinceEpochSpec` (`UNIX_EPOCH`). -/
structure CliEncHooksExt (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S ext where
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" CliExt.shimSpec
  memcpy : HookSat ext "memcpy" CliExt.memcpySpec
  memcpyRO : HookSat ext "memcpy" CliExt.memcpyROSpec
  memmove : HookSat ext "memmove" CliExt.memmoveSpec
  memset : HookSat ext "memset" CliExt.memsetSpec
  timeAdd : HookSat ext timeAddHookName timeAddSpec
  durationSinceEpoch : HookSat ext durationSinceHookName CliExt.durationSinceEpochSpec

theorem cliEncHooksExt_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (S : SpqrModel)
    (hOk : CliExternsOk P A ext) : CliEncHooksExt P.C A S ext where
  toTripleRatchetHooks := ⟨hOk.alloc, hOk.allocZeroed, hOk.aesEnc, hOk.aesDec,
    hOk.formatInner, hOk.fmtWrite⟩
  shim := hOk.shim
  memcpy := hOk.memcpy
  memcpyRO := hOk.memcpyRO
  memmove := hOk.memmove
  memset := hOk.memset
  timeAdd := hOk.timeAdd
  durationSinceEpoch := hOk.durationSince

theorem cliEncHooksExt_cliExternsWith {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (S : SpqrModel)
    (hOk : CliExternsOk P A ext) : CliEncHooksExt P.C A S (cliExternsWith ext) :=
  cliEncHooksExt_of_externsOk S (cliExternsOk_cliExternsWith hOk)

theorem cliEncHooksExt_trapUnlisted {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (S : SpqrModel)
    (hOk : CliExternsOk P A ext) : CliEncHooksExt P.C A S (trapUnlisted ext) :=
  cliEncHooksExt_of_externsOk S (cliExternsOk_trapUnlisted hOk)

/-- `__rustc::__rust_no_alloc_shim_is_unstable_v2` at call distance `k` from `name` on `tripleRatchetProgAtExt`. -/
theorem cliNoAllocShim_ok_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hshim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" CliExt.shimSpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      sessionShimSpec :=
  hook_ok_at (hname := shimName)
    rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, shimName]) hshim

/-- `memcpy` (`CliExt.memcpySpec`, 4096 B stack) at call distance `k` from `name` on `tripleRatchetProgAtExt`. -/
theorem cliMemcpy_ok_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : HookSat ext "memcpy" CliExt.memcpySpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      CliExt.memcpySpec :=
  hook_ok_at (hname := memcpyName)
    rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, memcpyName]) hmemcpy

/-- `memcpy` (`withStack framelessMemcpySpec allocHookStack`, 4096 B stack, deriving `bs.length ≤ 2^64`
automatically from `(s0.readReg64 .x2).toNat = bs.length`) at call distance `k` from `name`. -/
theorem cliStackedMemcpy_ok_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : HookSat ext "memcpy" CliExt.memcpySpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack framelessMemcpySpec allocHookStack) := by
  have h := cliMemcpy_ok_at_ext (b := b) hmemcpy (name := name) (k := k) hk
  refine subroutine_ok_outcome_intro fun (dst, src, bs) R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ CliExt.memcpySpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [withStack, framelessMemcpySpec] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    dsimp only [CliExt.memcpySpec, libcMemcpySpec, CliExt.memHookStack, allocHookStack] at hm ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  refine h.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CliExt.memcpySpec, CliExt.memHookStack, withStack, framelessMemcpySpec,
      allocHookStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- `memcpy` from `.rodata` (`CliExt.memcpyROSpec`, 4096 B stack) at call distance `k` from `name`. -/
theorem cliMemcpyRO_ok_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpyRO : HookSat ext "memcpy" CliExt.memcpyROSpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      CliExt.memcpyROSpec :=
  hook_ok_at (hname := memcpyName)
    rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, memcpyName]) hmemcpyRO

/-- `__rust_alloc` at call distance `k` from `name` on `tripleRatchetProgAtExt`, taking `AllocHooks A ext`. -/
theorem cliAlloc_ok_at_norm_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  alloc_ok_at_ext b A ext hA name k hk

/-- `__rust_dealloc` at call distance `k` from `name` on `tripleRatchetProgAtExt`, taking `AllocHooks A ext`. -/
theorem cliDealloc_ok_at_norm_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  dealloc_ok_at_ext b A ext hA name k hk

/-- `__rust_realloc` at call distance `k` from `name` on `tripleRatchetProgAtExt`, taking `AllocHooks A ext`. -/
theorem cliRealloc_ok_at_norm_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  realloc_ok_at_ext b A ext hA name k hk

private theorem entryOf_eq_trExtProgAt {img : Obj.Image} (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (name : String) :
    entryOf img name = (tripleRatchetProgAtExt img.base ext).fnAddr name :=
  entryOf_eq_tripleRatchetProgAtExt (ext := ext) himg name

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
