/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.Update
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed Proofs for `<spqr::authenticator::Authenticator>::update`

Lifts `<spqr::authenticator::Authenticator>::update` from `Auth.Update` onto `AllocContracts4K`
and `CliExternsOk` (both `cliExternsWith ext` and hook-agreeing external environments).
-/

set_option maxRecDepth 200000

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 (spqrHkdfWith)
open CryptoVerification.SpqrV1.Alloc (session2MemcpySpecWithStack
  sessionMemcpyRegionROSpecWithStack slice_concat_2_ok_x_of_hooks)
open CryptoVerification.SpqrV1.ChainProofs (SliceConcat2OkX)
open CryptoVerification.SpqrV1.Kdf (HkdfToSliceSpqrOkExt SpqrKdfHooksExt)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof (hkdf_to_slice_spqr_ok_of_hooks_ext)
open CryptoVerification.Cli.LibsignalSpqrV1.M4 (AllocContracts4K)
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli.Slots (AgreeOnCliHooks
  allocContractsX_of_externsOk_on)

set_option maxHeartbeats 400000

private theorem hookOk_map_local {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (g : β → α) (I : State → State → Prop) (hI : ∀ s, I s (f s))
    (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0 sf, I s0 sf → s0.mem ⊨ s₂.pre y s0 ∗ R →
      sf.mem ⊨ s₁.post (g y) s0 sf ∗ R → sf.mem ⊨ s₂.post y s0 sf ∗ R)
    (hpanic : ∀ y R s0 sf, sf.mem ⊨ s₁.onPanic (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onPanic y s0 sf ∗ R)
    (hexit : ∀ y c R s0 sf,
      sf.mem ⊨ s₁.onExit (g y) c s0 sf ∗ R → sf.mem ⊨ s₂.onExit y c s0 sf ∗ R)
    (hoom : ∀ y R s0 sf, sf.mem ⊨ s₁.onOom (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onOom y s0 sf ∗ R) :
    HookOk f s₂ := by
  intro y R s0 hrun hpreY hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hpreY) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · exact Or.inl ⟨hret, hcc, hpost y R s0 (f s0) (hI s0) hpreY hq⟩
  · exact Or.inr (Or.inl ⟨hp1, hpanic y R s0 (f s0) hp2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, hexit y c R s0 (f s0) he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, hoom y R s0 (f s0) ho2⟩))

private theorem hookSat_map_local {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem memsetRegion_of_libcMemset {prog : Program} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok prog addr (libcMemsetSpec stk)) :
    subroutine_ok prog addr (withStack memsetRegionSpec stk) := by
  refine subroutine_ok_map h ?_
  rintro ⟨ptr, c, len⟩ R s0 hpre
  refine ⟨(ptr, c, len), R, ?_, ?_⟩
  · dsimp only [libcMemsetSpec, withStack, memsetRegionSpec] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
  · intro sf hpost
    dsimp only [libcMemsetSpec, withStack, memsetRegionSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

private theorem sessionMemsetRegion_of_sessionMemset {prog : Program} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok prog addr (sessionMemsetSpec stk)) :
    subroutine_ok prog addr (withStack sessionMemsetRegionSpec stk) := by
  refine subroutine_ok_map h ?_
  rintro ⟨ptr, c, len⟩ R s0 hpre
  refine ⟨(ptr, c, len), R, ?_, ?_⟩
  · dsimp only [sessionMemsetSpec, libcMemsetSpec, withStack, sessionMemsetRegionSpec,
      memsetRegionSpec] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
  · intro sf hpost
    dsimp only [sessionMemsetSpec, withStack, sessionMemsetRegionSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem allocContractsX_of_allocContracts4K {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    AllocContractsX img A ext where
  alloc := subroutine_ok_inImage_of_subroutine_ok img (rustAllocWithStack_of_rustAlloc hA.alloc)
  dealloc := subroutine_ok_inImage_of_subroutine_ok img
    (rustDeallocExternWithStack_of_rustDealloc hA.dealloc)
  realloc := subroutine_ok_inImage_of_subroutine_ok img
    (rustReallocExternWithStack_of_rustRealloc hA.realloc)
  shim := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_withStack_of_subroutine_ok hA.shim hookStack)
  memcpy := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.memcpy hookStack (Nat.le_trans (by decide) hlo) hhi)
  session_memcpy := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.session_memcpy hookStack (Nat.le_trans (by decide) hlo) hhi)
  memcpy_region := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.memcpy_region hookStack (Nat.le_trans (by decide) hlo) hhi)
  session_memcpy_region := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.session_memcpy_region hookStack (Nat.le_trans (by decide) hlo) hhi)
  memmove := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.memmove hookStack (Nat.le_trans (by decide) hlo) hhi)
  session_memmove := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.session_memmove hookStack (Nat.le_trans (by decide) hlo) hhi)
  memset := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.memset hookStack (Nat.le_trans (by decide) hlo) hhi)
  session_memset := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.session_memset hookStack (Nat.le_trans (by decide) hlo) hhi)
  memset_region := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (memsetRegion_of_libcMemset (hA.memset hookStack (Nat.le_trans (by decide) hlo) hhi))
  session_memset_region := fun hookStack hlo hhi =>
    subroutine_ok_inImage_of_subroutine_ok img
      (sessionMemsetRegion_of_sessionMemset
        (hA.session_memset hookStack (Nat.le_trans (by decide) hlo) hhi))

private theorem sliceConcat2_of_cliHooks {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext shimName noAllocShimSpec)
    (halloc : HookSat ext allocName (rustAllocSpec A))
    (hmc : HookSat ext memcpyName CliExt.memcpySpec)
    (hRO : HookSat ext memcpyName CliExt.memcpyROSpec) :
    SliceConcat2OkX img A ext := by
  have hmc4K : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack) :=
    hookSat_map_local hmc fun _ hh =>
      hookOk_map_local (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
        (fun _ _ _ hp => by
          simpa only [CliExt.memcpySpec, libcMemcpySpec, memcpyRegionSpec,
            withStack, sessionMemcpyRegionSpec, session2MemcpySpecWithStack,
            allocHookStack, CliExt.memHookStack, sepConj_assoc] using hp)
        (fun _ _ _ _ _ _ hq => by
          simpa only [CliExt.memcpySpec, libcMemcpySpec, memcpyRegionSpec,
            withStack, sessionMemcpyRegionSpec, session2MemcpySpecWithStack,
            allocHookStack, CliExt.memHookStack, sepConj_assoc] using hq)
        (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have hRO4K : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack) :=
    hookSat_map_local hRO fun _ hh =>
      hookOk_map_local (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
        (fun _ _ _ hp => by
          simpa only [CliExt.memcpyROSpec, CliExt.withStack,
            sessionMemcpyRegionROSpecWithStack, allocHookStack,
            CliExt.memHookStack, sepConj_assoc] using hp)
        (fun _ _ _ _ _ _ hq => by
          simpa only [CliExt.memcpyROSpec, CliExt.withStack,
            sessionMemcpyRegionROSpecWithStack, allocHookStack,
            CliExt.memHookStack, sepConj_assoc] using hq)
        (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  exact slice_concat_2_ok_x_of_hooks hshim halloc hmc4K hRO4K

theorem authUpdatePinned_ok_of_hook_ext {img : Obj.Image}
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext) (hA : AllocContractsX img A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpecExt F A).inImage img) :=
  authUpdatePinned_ok_of_contracts_ext himg hconcat hhkdf hA (allocZeroedWithStackOkX_of_hook hZero)

theorem authUpdatePinned_ok_of_allocContracts4K {img : Obj.Image}
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext)
    (hA : AllocContracts4K img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpecExt F A).inImage img) :=
  authUpdatePinned_ok_of_hook_ext himg hconcat hhkdf (allocContractsX_of_allocContracts4K hA) hZero

theorem authUpdate_ok_of_allocContracts4K {img : Obj.Image}
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext)
    (hA : AllocContracts4K img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    AuthUpdateOkExt img F A ext :=
  authUpdate_ok_of_hook_ext himg hconcat hhkdf (allocContractsX_of_allocContracts4K hA) hZero

theorem authUpdatePinned_ok_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext')
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext')
      ((tripleRatchetProgAtExt img.base ext').fnAddr authUpdateName)
      ((authUpdatePinnedSpecExt P.C.F A).inImage img) :=
  authUpdatePinned_ok_of_hook_ext himg
    (sliceConcat2_of_cliHooks
      (hAg.hookSat (by decide) hOk.shim)
      (hAg.hookSat (by decide) hOk.alloc.alloc)
      (hAg.hookSat (by decide) hOk.memcpy)
      (hAg.hookSat (by decide) hOk.memcpyRO))
    (hkdf_to_slice_spqr_ok_of_hooks_ext img himg
      (SpqrKdfHooksExt.of_hookSat img P.C ext'
        (hAg.hookSat (by decide) hOk.compress256)
        (hAg.hookSat (by decide) hOk.memcpy)
        (hAg.hookSat (by decide) hOk.memcpyRO)
        (hAg.hookSat (by decide) hOk.memset)))
    (allocContractsX_of_externsOk_on hOk hAg img)
    (hAg.hookSat (by decide) hOk.allocZeroed)

theorem authUpdatePinned_ok_of_externsOk {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr authUpdateName)
      ((authUpdatePinnedSpecExt P.C.F A).inImage img) :=
  authUpdatePinned_ok_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img himg

theorem authUpdate_ok_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext')
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img) :
    AuthUpdateOkExt img P.C.F A ext' :=
  authUpdate_ok_of_hook_ext himg
    (sliceConcat2_of_cliHooks
      (hAg.hookSat (by decide) hOk.shim)
      (hAg.hookSat (by decide) hOk.alloc.alloc)
      (hAg.hookSat (by decide) hOk.memcpy)
      (hAg.hookSat (by decide) hOk.memcpyRO))
    (hkdf_to_slice_spqr_ok_of_hooks_ext img himg
      (SpqrKdfHooksExt.of_hookSat img P.C ext'
        (hAg.hookSat (by decide) hOk.compress256)
        (hAg.hookSat (by decide) hOk.memcpy)
        (hAg.hookSat (by decide) hOk.memcpyRO)
        (hAg.hookSat (by decide) hOk.memset)))
    (allocContractsX_of_externsOk_on hOk hAg img)
    (hAg.hookSat (by decide) hOk.allocZeroed)

/-- `AuthUpdateOkExt img P.C.F A (cliExternsWith ext)` directly from `CliExternsOk P A ext`. -/
theorem authUpdate_ok_of_externsOk {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    AuthUpdateOkExt img P.C.F A (cliExternsWith ext) :=
  authUpdate_ok_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img himg

theorem authUpdate_ok_of_externsOk_raw {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext) :
    AuthUpdateOkExt img P.C.F A ext :=
  authUpdate_ok_of_hook_ext himg
    (sliceConcat2_of_cliHooks hOk.shim hOk.alloc.alloc hOk.memcpy hOk.memcpyRO)
    (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_ok_of_externsOk_raw
      img himg hOk)
    hA hOk.allocZeroed

end CryptoVerification.SpqrV1.Auth
