/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt

@[expose] public section

set_option autoImplicit false

/-!
# `CliExternsOk` Corollaries for `slice::Concat`

Lifts 2-slice and 3-slice `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]`
contracts (`SliceConcat2OkX{,A}`, `SliceConcat3OkX{,A}`) onto `CliExternsOk P A ext`,
`cliExternsWith ext`, and hook tables satisfying `AgreeOnCliHooks ext ext'`.
-/

set_option maxRecDepth 200000

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
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

/-- Transports `CliExt.memcpySpec` onto `session2MemcpySpecWithStack allocHookStack`. -/
theorem hookSat_session2Memcpy4K_of_cliExt {ext : String → Option (State → State)}
    (h : HookSat ext memcpyName CliExt.memcpySpec) :
    HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack) :=
  hookSat_map_local h fun _ hh =>
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

/-- Transports `CliExt.memcpyROSpec` onto `sessionMemcpyRegionROSpecWithStack allocHookStack`. -/
theorem hookSat_sessionMemcpyRO4K_of_cliExt {ext : String → Option (State → State)}
    (h : HookSat ext memcpyName CliExt.memcpyROSpec) :
    HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack) :=
  hookSat_map_local h fun _ hh =>
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

theorem hookSat_session2Memcpy4K_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    HookSat ext' memcpyName (session2MemcpySpecWithStack allocHookStack) :=
  hookSat_session2Memcpy4K_of_cliExt (hAg.hookSat (by decide) hOk.memcpy)

theorem hookSat_sessionMemcpyRO4K_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    HookSat ext' memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack) :=
  hookSat_sessionMemcpyRO4K_of_cliExt (hAg.hookSat (by decide) hOk.memcpyRO)

theorem memcpyROOkExtX_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (img : Obj.Image) :
    MemcpyROOkExtX img ext' :=
  memcpyROOkExtX_of_hookSat_withStack (by decide)
    (hookSat_sessionMemcpyRO4K_of_externsOk_on hOk hAg)

theorem memcpyROOkExtX_of_externsOk {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    MemcpyROOkExtX img (cliExternsWith ext) :=
  memcpyROOkExtX_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img

/-- `SliceConcat2OkX img A ext'` from `CliExternsOk P A ext` and `AgreeOnCliHooks ext ext'`. -/
theorem sliceConcat2_ok_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (img : Obj.Image) :
    ChainProofs.SliceConcat2OkX img A ext' :=
  slice_concat_2_ok_x_of_hooks
    (hAg.hookSat (by decide) hOk.shim)
    (hAg.hookSat (by decide) hOk.alloc.alloc)
    (hookSat_session2Memcpy4K_of_externsOk_on hOk hAg)
    (hookSat_sessionMemcpyRO4K_of_externsOk_on hOk hAg)

theorem sliceConcat2_ok_of_externsOk {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    ChainProofs.SliceConcat2OkX img A (cliExternsWith ext) :=
  sliceConcat2_ok_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img

theorem sliceConcat2_ok_of_externsOk_raw {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    ChainProofs.SliceConcat2OkX img A ext :=
  slice_concat_2_ok_x_of_hooks hOk.shim hOk.alloc.alloc
    (hookSat_session2Memcpy4K_of_cliExt hOk.memcpy)
    (hookSat_sessionMemcpyRO4K_of_cliExt hOk.memcpyRO)

/-- `SliceConcat2OkXA img A ext'` from `CliExternsOk P A ext` and `AgreeOnCliHooks ext ext'`. -/
theorem sliceConcat2_ok_xa_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (img : Obj.Image) :
    SliceConcat2OkXA img A ext' :=
  slice_concat_2_ok_x_roX
    (allocContractsX_of_externsOk_on hOk hAg img)
    (memcpyROOkExtX_of_externsOk_on hOk hAg img)

theorem sliceConcat2_ok_xa_of_externsOk {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    SliceConcat2OkXA img A (cliExternsWith ext) :=
  sliceConcat2_ok_xa_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img

/-- `SliceConcat3OkX img A ext'` from `CliExternsOk P A ext` and `AgreeOnCliHooks ext ext'`. -/
theorem sliceConcat3_ok_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (img : Obj.Image) :
    SliceConcat3OkX img A ext' :=
  slice_concat_3_ok_x_of_hooks
    (hAg.hookSat (by decide) hOk.shim)
    (hAg.hookSat (by decide) hOk.alloc.alloc)
    (hookSat_session2Memcpy4K_of_externsOk_on hOk hAg)
    (hookSat_sessionMemcpyRO4K_of_externsOk_on hOk hAg)

theorem sliceConcat3_ok_of_externsOk {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    SliceConcat3OkX img A (cliExternsWith ext) :=
  sliceConcat3_ok_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img

theorem sliceConcat3_ok_of_externsOk_raw {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    SliceConcat3OkX img A ext :=
  slice_concat_3_ok_x_of_hooks hOk.shim hOk.alloc.alloc
    (hookSat_session2Memcpy4K_of_cliExt hOk.memcpy)
    (hookSat_sessionMemcpyRO4K_of_cliExt hOk.memcpyRO)

/-- `SliceConcat3OkXA img A ext'` from `CliExternsOk P A ext` and `AgreeOnCliHooks ext ext'`. -/
theorem sliceConcat3_ok_xa_of_externsOk_on {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (img : Obj.Image) :
    SliceConcat3OkXA img A ext' :=
  slice_concat_3_ok_x_roX
    (allocContractsX_of_externsOk_on hOk hAg img)
    (memcpyROOkExtX_of_externsOk_on hOk hAg img)

theorem sliceConcat3_ok_xa_of_externsOk {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    SliceConcat3OkXA img A (cliExternsWith ext) :=
  sliceConcat3_ok_xa_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img

end CryptoVerification.SpqrV1.Alloc

namespace CryptoVerification.SpqrV1.ChainProofs

export Alloc (sliceConcat2_ok_of_externsOk_on sliceConcat2_ok_of_externsOk
  sliceConcat2_ok_of_externsOk_raw sliceConcat2_ok_xa_of_externsOk_on
  sliceConcat2_ok_xa_of_externsOk sliceConcat3_ok_of_externsOk_on
  sliceConcat3_ok_of_externsOk sliceConcat3_ok_of_externsOk_raw
  sliceConcat3_ok_xa_of_externsOk_on sliceConcat3_ok_xa_of_externsOk)

end CryptoVerification.SpqrV1.ChainProofs
