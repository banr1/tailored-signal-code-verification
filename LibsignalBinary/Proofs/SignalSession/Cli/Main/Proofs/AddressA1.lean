/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address

/-!
# `memrchr` Hook Discharge for `signal_session::address`

Discharges the `memrchr` extern hypothesis of `address_ok` against `CliRun.memrchrHook`
(`address_ok_a1`) and parametric `CliExternsOk P A ext` (`address_ok_ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open Address.Helpers

/-- `CliRun.memrchrHook` satisfies `memrchrSpec stk` for any stack budget `stk`. -/
theorem memrchrHook_ok (stk : Nat) : HookOk memrchrHook (memrchrSpec stk) := by
  intro x R s0 hrun hpre _hsp
  simp only [memrchrSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
  have hlen : (s0.readReg64 .x2).toNat = x.bs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  obtain ⟨hlen_le, hrd⟩ := (IsBlock.pointsToBytes x.p x.bs).read hmem
  have hcan := (IsBlock.pointsToBytes x.p x.bs).canRead hlen_le hmem
  have hmemrchr :
      memrchrHook s0 =
        match memrchrIdx x.c x.bs with
        | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s0
        | none => retHook (fun s => s.writeReg64 .x0 0#64) s0 := by
    unfold memrchrHook memrchrIdx
    simp only [hx0, hx1, hlen, hcan, hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hmemrchr]
  cases hidx : memrchrIdx x.c x.bs with
  | some i =>
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [memrchrSpec]
    simp only [hidx, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm],
      ⟨by simp only [retHook, arm64_norm], by simp only [retHook, arm64_norm]⟩⟩, hmem⟩
  | none =>
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [memrchrSpec]
    simp only [hidx, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm]⟩, hmem⟩

/-- Discharges `address_ok`'s `memrchr` hypothesis when `ext` maps `memrchr` to `memrchrHook`. -/
theorem address_ok_a1 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hext : ext "core::slice::memchr::memrchr" = some memrchrHook)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr addressName)
      ((addressSpec A uuidTryParse resStack).inImage img) := by
  refine address_ok hCF ?_ hres hres64
  have hhook := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
    (hname := "core::slice::memchr::memrchr") (k := 0)
    (ls_stub% "core::slice::memchr::memrchr")
    (Nat.add_zero _)
    (by decide)
    (ls_hook% "core::slice::memchr::memrchr")
    (by simp [Rust.isPanicSymbol])
    ⟨memrchrHook, hext, memrchrHook_ok extHookStack⟩
  rw [BitVec.add_zero] at hhook
  exact subroutine_ok_inImage_of_subroutine_ok img hhook

/-! ## Parametric `CliExternsOk` Specializations -/

private theorem stackAt_split_ext_addr (sp : BitVec 64) {stk : Nat}
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk = memRegion (sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
      stackAt sp extHookStack := by
  have h1 := stackAt_split_bottom sp extHookStack (stk - extHookStack) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

/-- Frames `HookSat ext "core::slice::memchr::memrchr" CliExt.memrchrSpec` to `extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem memrchr_ok_of_hookSat {img : Obj.Image} {ext : String → Option (State → State)}
    {stk : Nat} (hsat : HookSat ext "core::slice::memchr::memrchr" CliExt.memrchrSpec)
    (hle : extHookStack ≤ stk := by decide)
    (hmax : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::slice::memchr::memrchr")
      ((memrchrSpec stk).inImage img) := by
  rcases hsat with ⟨f, hf, hh⟩
  have hh' : HookOk f (memrchrSpec stk) := by
    intro x R s0 hrun hpre hsp
    have hsplit := stackAt_split_ext_addr s0.sp hle hmax
    let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
    have hpre' : s0.mem ⊨ CliExt.memrchrSpec.pre ⟨x.c, x.p, x.bs⟩ s0 ∗ R' := by
      dsimp only [memrchrSpec, CliExt.memrchrSpec, R'] at hpre ⊢
      rw [hsplit] at hpre
      ac_nf at hpre ⊢
    obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.c, x.p, x.bs⟩ R' s0 hrun hpre' hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [memrchrSpec, CliExt.memrchrSpec, R'] at hpost ⊢
      rw [hsplit]
      ac_nf at hpost ⊢
    · dsimp only [CliExt.memrchrSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.memrchrSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.memrchrSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  have hhook := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
    (hname := "core::slice::memchr::memrchr") (k := 0)
    (ls_stub% "core::slice::memchr::memrchr") (Nat.add_zero _) (by decide)
    (ls_hook% "core::slice::memchr::memrchr") (by simp [Rust.isPanicSymbol])
    ⟨f, hf, hh'⟩
  rw [BitVec.add_zero] at hhook
  exact subroutine_ok_inImage_of_subroutine_ok img hhook

theorem memrchr_ok_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (stk : Nat := extHookStack)
    (hle : extHookStack ≤ stk := by decide)
    (hmax : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr "core::slice::memchr::memrchr")
      ((memrchrSpec stk).inImage img) := by
  rcases hOk.memrchr with ⟨f, hf, hh⟩
  have hnpe : E2E.isImagePanicSymbol "core::slice::memchr::memrchr" = false := by
    simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol]
  have hsat : HookSat (cliExternsWith ext) "core::slice::memchr::memrchr" CliExt.memrchrSpec :=
    ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnpe).trans hf, hh⟩
  exact memrchr_ok_of_hookSat hsat hle hmax

theorem address_ok_of_hookSat {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hmemrchr : HookSat ext "core::slice::memchr::memrchr" CliExt.memrchrSpec)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr addressName)
      ((addressSpec A uuidTryParse resStack).inImage img) :=
  address_ok hCF (memrchr_ok_of_hookSat hmemrchr) hres hres64

/-- Specialization of `address_ok` to `mProg img (cliExternsWith ext)` under `CliExternsOk P A ext`. -/
theorem address_a1_ok_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} {resStack : Nat}
    (hCF : AllocContractsFs img A (cliExternsWith ext))
    (hOk : CliExternsOk P A ext)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr addressName)
      ((addressSpec A uuidTryParse resStack).inImage img) :=
  address_ok hCF (memrchr_ok_ext hOk img) hres hres64

theorem address_ok_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} {resStack : Nat}
    (hCF : AllocContractsFs img A (cliExternsWith ext))
    (hOk : CliExternsOk P A ext)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr addressName)
      ((addressSpec A uuidTryParse resStack).inImage img) :=
  address_a1_ok_ext hCF hOk hres hres64

end CryptoVerification.SignalSession.Cli.MainHops

