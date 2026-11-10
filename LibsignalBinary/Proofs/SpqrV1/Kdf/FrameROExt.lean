/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.GenDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import ProofLib.SepLogic.HeapIntro

/-!
# Contract-Backed SPQR KDF Hooks and Read-Only Frame Combinators

Defines `SpqrKdfHooksExt` at `extHookStack` (`16384` B) from `CliExternsOk`, the read-only-aware
frame relation `S2FrameRO`, and the input-slice invariant `KdfSliceInv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout

/-! ## Stack Budgets, Hook Specs, and `SpqrKdfHooksExt` Bundle -/

/-- Stack budget of `finalize_fixed [local#3]` (`0x6ce50`) under `extHookStack` (`144 + 16384 = 16528` B). -/
abbrev finalizeFixed3StackExt : Nat := 144 + extHookStack

/-- Stack budget of `new_from_slice [local#3]` (`0x66fa0`) under `extHookStack` (`544 + 16384 = 16928` B). -/
abbrev newFromSlice3StackExt : Nat := 544 + extHookStack

/-- Stack-equipped read-only `memcpy` spec at configurable `hookStack`. -/
abbrev spqrMemcpyROExtSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack

/-- `ShaState`-indexed `compress256` contract with stack slack `hookStack`. -/
def spqrCompress256ExternSpec (F : ShaCompress) (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × ShaState × List (BitVec 8)) where
  pre := fun (stA, blkA, st, bs) s =>
    ⌜s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = blkA ∧
      64 * (s.readReg64 .x2).toNat = bs.length⌝ ∗
      (blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackAt s.sp hookStack
  post := fun (stA, blkA, st, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (blkA ↦ₛ bs) ∗
      (stA ↦ₛ shaStateBytes ((HMAC.chunks64 bs).foldl F st)) ∗
      stackAt s0.sp hookStack

/-- `memset` contract with 64-bit `.x1` low-byte truncation and stack slack `hookStack`. -/
def spqrMemsetExternSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (dst, val, n) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ (s0.readReg64 .x1).truncate 8 = val ∧
      (s0.readReg64 .x2).toNat = n⌝ ∗
      memRegion dst n ∗ stackAt s0.sp hookStack
  post := fun (dst, val, n) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ List.replicate n val) ∗ stackAt s0.sp hookStack

/-- Extern contract bundle required by SPQR KDF (`finalize_fixed [local#3]`,
`new_from_slice [local#3]`, and `spqr::kdf::hkdf_to_slice`) on `tripleRatchetProgAtExt img.base ext`
at `extHookStack` (`16384` B). -/
structure SpqrKdfHooksExt (img : Obj.Image) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop where
  compress256 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((spqrCompress256ExternSpec F extHookStack).inImage img)
  memcpy :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img)
  memcpyRO :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + bv% (ls_off% "memcpy"))
      ((spqrMemcpyROExtSpec extHookStack).inImage img)
  memset :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + bv% (ls_off% "memset"))
      ((spqrMemsetExternSpec extHookStack).inImage img)

namespace SpqrKdfHooksExt

private theorem hookOk_map_pure {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (g : β → α) (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0, (f s0).mem ⊨ s₁.post (g y) s0 (f s0) ∗ R →
      (f s0).mem ⊨ s₂.post y s0 (f s0) ∗ R)
    (hpan : ∀ x s0 sf, s₁.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, s₁.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, s₁.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f s₂ := by
  intro y R s0 hrun hp hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hp) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp'⟩ | ⟨code, _, he'⟩ | ⟨_, ho'⟩
  · exact Or.inl ⟨hret, hcc, hpost y R s0 hq⟩
  · rw [hpan (g y) s0 (f s0), satisfies_pure_sepConj] at hp'; exact False.elim hp'.1
  · rw [hex (g y) code s0 (f s0), satisfies_pure_sepConj] at he'; exact False.elim he'.1
  · rw [hoom (g y) s0 (f s0), satisfies_pure_sepConj] at ho'; exact False.elim ho'.1

private theorem hookSat_map {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem hookOk_stack_mono {α : Type} {f : State → State} {base : Spec α}
    {s1 s2 : Nat} (hh : HookOk f (SignalSession.CliExt.withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (SignalSession.CliExt.withStack base s2) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (SignalSession.CliExt.withStack base s1).pre x s0 ∗ R' := by
    dsimp only [SignalSession.CliExt.withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [SignalSession.CliExt.withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [SignalSession.CliExt.withStack] at hp
    rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [SignalSession.CliExt.withStack] at he
    rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [SignalSession.CliExt.withStack] at ho
    rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem stub_inImage_of_hookSat {α : Type} (img : Obj.Image)
    {ext : String → Option (State → State)} {hname : String} {off : Nat} {spec : Spec α}
    (hlt : off < 2 ^ 64)
    (hhook : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? off = H hname)
    (hnp : Rust.isPanicSymbol hname = false)
    (hsat : HookSat ext hname spec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + BitVec.ofNat 64 off) (spec.inImage img) := by
  refine subroutine_ok_inImage_of_subroutine_ok img ?_
  obtain ⟨f, hf, hok⟩ := hsat
  exact hook_ok_stub (code := libsignalSessionCode) hlt hhook
    ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩

private theorem readReg32_truncate8_eq (s : State) (r : Reg) :
    (s.readReg32 r).truncate 8 = (s.readReg64 r).truncate 8 := by
  change ((s.readReg64 r).setWidth 32).setWidth 8 = (s.readReg64 r).setWidth 8
  exact BitVec.setWidth_setWidth_of_le (s.readReg64 r) (by decide : 8 ≤ 32)

private theorem isPanic_compress256 :
    Rust.isPanicSymbol "sha2::sha256::compress256" = false := by simp [Rust.isPanicSymbol]

private theorem isPanic_memcpy : Rust.isPanicSymbol "memcpy" = false := by simp [Rust.isPanicSymbol]

private theorem isPanic_memset : Rust.isPanicSymbol "memset" = false := by simp [Rust.isPanicSymbol]

/-- Build `SpqrKdfHooksExt img C.F ext` from `HookSat` contracts on `ext`. -/
theorem of_hookSat (img : Obj.Image) (C : Crypto) (ext : String → Option (State → State))
    (hComp : HookSat ext "sha2::sha256::compress256" (SignalSession.CliExt.compress256Spec C))
    (hMemcpy : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec)
    (hMemcpyRO : HookSat ext "memcpy" SignalSession.CliExt.memcpyROSpec)
    (hMemset : HookSat ext "memset" SignalSession.CliExt.memsetSpec) :
    SpqrKdfHooksExt img C.F ext where
  compress256 := by
    have hsat : HookSat ext "sha2::sha256::compress256"
        (spqrCompress256ExternSpec C.F extHookStack) := by
      refine hookSat_map hComp fun f hf => ?_
      refine hookOk_map_pure (fun (stA, blkA, st, bs) => (stA, st, blkA, bs, (bs.length / 64))) hf
        (fun ⟨stA, blkA, st, bs⟩ R s0 hp => ?_)
        (fun ⟨stA, blkA, st, bs⟩ R s0 hq => ?_)
      · dsimp only [spqrCompress256ExternSpec, SignalSession.CliExt.compress256Spec,
          SignalSession.CliExt.withStack] at hp ⊢
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
        rcases hp with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
        have hn : (s0.readReg64 .x2).toNat = bs.length / 64 := by omega
        have hlen : bs.length = 64 * (bs.length / 64) := by omega
        refine ⟨⟨hx0, hx1, hn, hlen⟩, ?_⟩
        ac_nf at hmem ⊢
      · dsimp only [spqrCompress256ExternSpec, SignalSession.CliExt.compress256Spec,
          SignalSession.CliExt.withStack] at hq ⊢
        ac_nf at hq ⊢
    exact stub_inImage_of_hookSat img (by decide)
      (ls_hook% "sha2::sha256::compress256") isPanic_compress256 hsat
  memcpy := by
    let base : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
      { pre := fun (dst, src, bs) s0 =>
          ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
            memRegion dst bs.length ∗ (src ↦ₛ bs)
        post := fun (dst, src, bs) s0 sf =>
          ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) }
    have hsat : HookSat ext "memcpy" (sessionMemcpySpec extHookStack) := by
      refine hookSat_map hMemcpy fun f hf => ?_
      have h1 : HookOk f (SignalSession.CliExt.withStack base SignalSession.CliExt.memHookStack) :=
        hookOk_map_pure (fun x => x) hf
          (fun ⟨dst, src, bs⟩ R s0 hp => by
            dsimp only [SignalSession.CliExt.memcpySpec, libcMemcpySpec,
              SignalSession.CliExt.withStack, base] at hp ⊢
            ac_nf at hp ⊢)
          (fun ⟨dst, src, bs⟩ R s0 hq => by
            dsimp only [SignalSession.CliExt.memcpySpec,
              SignalSession.CliExt.withStack, base] at hq ⊢
            ac_nf at hq ⊢)
      have h2 := hookOk_stack_mono h1 (by decide : SignalSession.CliExt.memHookStack ≤ extHookStack)
        (by decide)
      exact hookOk_map_pure (fun x => x) h2
        (fun ⟨dst, src, bs⟩ R s0 hp => by
          dsimp only [sessionMemcpySpec, libcMemcpySpec,
            SignalSession.CliExt.withStack, base] at hp ⊢
          ac_nf at hp ⊢)
        (fun ⟨dst, src, bs⟩ R s0 hq => by
          dsimp only [sessionMemcpySpec,
            SignalSession.CliExt.withStack, base] at hq ⊢
          ac_nf at hq ⊢)
    exact stub_inImage_of_hookSat img (by decide)
      (ls_hook% "memcpy") isPanic_memcpy hsat
  memcpyRO := by
    let base : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
      { pre := fun (dst, src, bs) s0 =>
          ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
            bs.length ≤ 2 ^ 64⌝ ∗ memRegion dst bs.length ∗ (src ↦ᵣ bs)
        post := fun (dst, src, bs) s0 sf =>
          ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) }
    have hsat : HookSat ext "memcpy" (spqrMemcpyROExtSpec extHookStack) := by
      refine hookSat_map hMemcpyRO fun f hf => ?_
      have h2 := hookOk_stack_mono (base := base) hf
        (by decide : SignalSession.CliExt.memHookStack ≤ extHookStack) (by decide)
      exact hookOk_map_pure (fun x => x) h2
        (fun ⟨dst, src, bs⟩ R s0 hp => by
          dsimp only [spqrMemcpyROExtSpec, SignalSession.CliExt.withStack, base] at hp ⊢
          ac_nf at hp ⊢)
        (fun ⟨dst, src, bs⟩ R s0 hq => by
          dsimp only [spqrMemcpyROExtSpec, SignalSession.CliExt.withStack, base] at hq ⊢
          ac_nf at hq ⊢)
    exact stub_inImage_of_hookSat img (by decide)
      (ls_hook% "memcpy") isPanic_memcpy hsat
  memset := by
    let base : Spec (BitVec 64 × BitVec 8 × Nat) :=
      { pre := fun (ptr, c, len) s0 =>
          ⌜s0.readReg64 .x0 = ptr ∧ (s0.readReg64 .x1).truncate 8 = c ∧
            (s0.readReg64 .x2).toNat = len⌝ ∗ memRegion ptr len
        post := fun (ptr, c, len) s0 sf =>
          ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c) }
    have hsat : HookSat ext "memset" (spqrMemsetExternSpec extHookStack) := by
      refine hookSat_map hMemset fun f hf => ?_
      have h1 : HookOk f (SignalSession.CliExt.withStack base SignalSession.CliExt.memHookStack) :=
        hookOk_map_pure (fun x => x) hf
          (fun ⟨ptr, c, len⟩ R s0 hp => by
            dsimp only [SignalSession.CliExt.memsetSpec, libcMemsetSpec,
              SignalSession.CliExt.withStack, base] at hp ⊢
            simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
            rcases hp with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
            refine ⟨⟨hx0, (readReg32_truncate8_eq s0 .x1).trans hx1, hx2⟩, ?_⟩
            ac_nf at hmem ⊢)
          (fun ⟨ptr, c, len⟩ R s0 hq => by
            dsimp only [SignalSession.CliExt.memsetSpec,
              SignalSession.CliExt.withStack, base] at hq ⊢
            ac_nf at hq ⊢)
      have h2 := hookOk_stack_mono h1 (by decide : SignalSession.CliExt.memHookStack ≤ extHookStack)
        (by decide)
      exact hookOk_map_pure (fun x => x) h2
        (fun ⟨ptr, c, len⟩ R s0 hp => by
          dsimp only [spqrMemsetExternSpec, SignalSession.CliExt.withStack, base] at hp ⊢
          ac_nf at hp ⊢)
        (fun ⟨ptr, c, len⟩ R s0 hq => by
          dsimp only [spqrMemsetExternSpec, SignalSession.CliExt.withStack, base] at hq ⊢
          ac_nf at hq ⊢)
    exact stub_inImage_of_hookSat img (by decide)
      (ls_hook% "memset") isPanic_memset hsat

private theorem hookSat_cliExternsWith_of_not_panic {α : Type}
    {ext : String → Option (State → State)} {n : String} {spec : Spec α}
    (hn : E2E.isImagePanicSymbol n = false) (h : HookSat ext n spec) :
    HookSat (SignalSession.cliExternsWith ext) n spec := by
  obtain ⟨f, hf, hok⟩ := h
  have heq : SignalSession.cliExternsWith ext n = ext n := by
    simp [SignalSession.cliExternsWith, E2E.withImagePanics, hn]
  exact ⟨f, heq.trans hf, hok⟩

private theorem isPanicE_compress256 :
    E2E.isImagePanicSymbol "sha2::sha256::compress256" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_compress256, E2E.extraImagePanicNames]

private theorem isPanicE_memcpy :
    E2E.isImagePanicSymbol "memcpy" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_memcpy, E2E.extraImagePanicNames]

private theorem isPanicE_memset :
    E2E.isImagePanicSymbol "memset" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_memset, E2E.extraImagePanicNames]

/-- Build `SpqrKdfHooksExt img P.C.F ext` directly from `CliExternsOk P A ext`. -/
theorem of_externsOk_raw (img : Obj.Image) {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : SignalSession.CliExternsOk P A ext) :
    SpqrKdfHooksExt img P.C.F ext :=
  of_hookSat img P.C ext hOk.compress256 hOk.memcpy hOk.memcpyRO hOk.memset

/-- Build `SpqrKdfHooksExt img P.C.F (cliExternsWith ext)` from `CliExternsOk P A ext`. -/
theorem of_externsOk (img : Obj.Image) {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : SignalSession.CliExternsOk P A ext) :
    SpqrKdfHooksExt img P.C.F (SignalSession.cliExternsWith ext) :=
  of_hookSat img P.C (SignalSession.cliExternsWith ext)
    (hookSat_cliExternsWith_of_not_panic isPanicE_compress256 hOk.compress256)
    (hookSat_cliExternsWith_of_not_panic isPanicE_memcpy hOk.memcpy)
    (hookSat_cliExternsWith_of_not_panic isPanicE_memcpy hOk.memcpyRO)
    (hookSat_cliExternsWith_of_not_panic isPanicE_memset hOk.memset)

end SpqrKdfHooksExt

/-! ## `RunsToE`, `AgreesOn`, `S2Frame`, and `S2FrameRO` Combinators -/

namespace SpqrKdfExt

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union Heap.Matches Heap.complement
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepImp
  SepProp.sepExists pointsTo8 pointsToBytes regionHeap regionHeapRO regionBlock memRegion

theorem runsTo_toE {prog : Program} {s₀ : State} {P : State → Prop} (h : RunsTo prog s₀ P) :
    RunsToE prog s₀ P :=
  fun hL => by
    obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
    exact ⟨sf, hst, htr, hP, hLf⟩

/-- Sequence two `RunsToE` transitions while automatically propagating `img.FrozenLoaded`
and `symtab = img.symtab` across the first transition via `Steps.frozenLoaded` and `Steps.symtab_eq`. -/
theorem RunsToE.trans_frozen {prog : Program} {img : Obj.Image} {s₀ : State}
    {P Q : State → Prop}
    (hfrz : img.FrozenLoaded s₀) (hsym : s₀.symtab = img.symtab)
    (h1 : RunsToE prog s₀ P)
    (h2 : ∀ s₁, img.FrozenLoaded s₁ → s₁.symtab = img.symtab → P s₁ → RunsToE prog s₁ Q) :
    RunsToE prog s₀ Q := by
  intro hL0
  obtain ⟨s₁, hst1, ⟨htr1, hev1⟩, hP1, hL1⟩ := h1 hL0
  have hfrz1 : img.FrozenLoaded s₁ := hst1.frozenLoaded hfrz
  have hsym1 : s₁.symtab = img.symtab := hst1.symtab_eq.trans hsym
  obtain ⟨s₂, hst2, ⟨htr2, hev2⟩, hQ2, hL2⟩ := h2 s₁ hfrz1 hsym1 hP1 hL1
  exact ⟨s₂, hst1.trans hst2, ⟨htr2.trans htr1, hev2.trans hev1⟩, hQ2, hL2⟩

theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

theorem S2Frame.trans_agreesOutside {m₁ m₂ m₃ : Memory} {regs : List (BitVec 64 × ℕ)}
    {base : BitVec 64} {len : ℕ}
    (hf : S2Frame m₁ m₂ regs) (hmem : (base, len) ∈ regs)
    (hag : AgreesOutside m₂ m₃ base len) :
    S2Frame m₁ m₃ regs :=
  hf.trans (S2Frame.of_frame (Frame.trans_agreesOutside (Frame.refl m₂ regs) hmem hag))

theorem S2Frame.trans_agreesOutside_sub {m₁ m₂ m₃ : Memory} {regs : List (BitVec 64 × ℕ)}
    {rbase base : BitVec 64} {rlen len : ℕ}
    (hf : S2Frame m₁ m₂ regs) (hmem : (rbase, rlen) ∈ regs)
    (hsub : (base - rbase).toNat + len ≤ rlen)
    (hag : AgreesOutside m₂ m₃ base len) :
    S2Frame m₁ m₃ regs :=
  hf.trans (S2Frame.of_frame (Frame.trans_agreesOutside_sub (Frame.refl m₂ regs) hmem hsub hag))

theorem S2Frame.readable_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {a : BitVec 64} {n : ℕ} (hr : m₁.Readable a n) :
    m₂.Readable a n :=
  fun x hx => hf.2.2 x (hr x hx).1 (hr x hx).2

/-- Multi-region read-only-aware frame relation: regions in `roRegs` may lose `Perm.rw` if an
extern read-only contract re-materializes `(src ↦ᵣ bs)`, while all RW addresses outside `roRegs`
preserve `Perm.rw`, all readable addresses preserve `(perm a).r = true`, and all readable addresses
outside `regs` preserve `read8`. -/
def S2FrameRO (roRegs : List (BitVec 64 × ℕ)) (m₁ m₂ : Memory)
    (regs : List (BitVec 64 × ℕ)) : Prop :=
  (∀ a, (m₁.perm a).r = true → m₁.isLazyFree a = false →
    (∀ r ∈ regs, OutsideRegion r.1 r.2 a) → m₂.read8 a = m₁.read8 a) ∧
  (((∀ a, (∀ ro ∈ roRegs, OutsideRegion ro.1 ro.2 a) → m₁.permNoLazy a = some Perm.rw → m₂.permNoLazy a = some Perm.rw) ∧
    (∀ a, (∀ ro ∈ roRegs, OutsideRegion ro.1 ro.2 a) → m₁.perm a = some Perm.rw → m₂.perm a = some Perm.rw)) ∧
   ((∀ a, (m₁.perm a).mapped = true ∧ m₁.isAnon a = true →
      (m₂.perm a).mapped = true ∧ m₂.isAnon a = true) ∧
    (∀ a, m₁.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m₂.perm a = some Perm.protNone ∧
      (m₁.isLazyFree a = false → m₂.read8 a = m₁.read8 a ∧ m₂.isLazyFree a = false)))) ∧
  (∀ a, (m₁.perm a).r = true → m₁.isLazyFree a = false →
    (m₂.perm a).r = true ∧ m₂.isLazyFree a = false)

namespace S2FrameRO

theorem refl (roRegs : List (BitVec 64 × ℕ)) (m : Memory) (regs : List (BitVec 64 × ℕ)) :
    S2FrameRO roRegs m m regs :=
  ⟨fun _ _ _ _ => rfl,
   ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, ⟨fun _ h => h, fun _ h _ => ⟨h, fun hlf => ⟨rfl, hlf⟩⟩⟩⟩,
   fun _ hr hlf => ⟨hr, hlf⟩⟩

theorem of_s2frame {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)} (h : S2Frame m₁ m₂ regs) :
    S2FrameRO roRegs m₁ m₂ regs :=
  ⟨h.1, ⟨⟨fun a _ hnl => h.2.1.1.1 a hnl, fun a _ hrw => h.2.1.1.2 a hrw⟩, h.2.1.2⟩, h.2.2⟩

theorem of_frame {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)} (h : Frame m₁ m₂ regs) :
    S2FrameRO roRegs m₁ m₂ regs :=
  of_s2frame (S2Frame.of_frame h)

theorem trans {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ m₃ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h12 : S2FrameRO roRegs m₁ m₂ regs)
    (h23 : S2FrameRO roRegs m₂ m₃ regs) :
    S2FrameRO roRegs m₁ m₃ regs :=
  ⟨fun a hr hlf hout =>
     let ⟨hr₂, hlf₂⟩ := h12.2.2 a hr hlf
     (h23.1 a hr₂ hlf₂ hout).trans (h12.1 a hr hlf hout),
   ⟨⟨fun a hro hnl => h23.2.1.1.1 a hro (h12.2.1.1.1 a hro hnl),
     fun a hro hrw => h23.2.1.1.2 a hro (h12.2.1.1.2 a hro hrw)⟩,
    ⟨fun a hm => h23.2.1.2.1 a (h12.2.1.2.1 a hm),
     fun a hpn hout =>
       let ⟨hp₁, hlf₁⟩ := h12.2.1.2.2 a hpn hout
       let ⟨hp₂, hlf₂⟩ := h23.2.1.2.2 a hp₁ hout
       ⟨hp₂, fun hlf =>
         let ⟨hr₁, hlf₁'⟩ := hlf₁ hlf
         let ⟨hr₂, hlf₂'⟩ := hlf₂ hlf₁'
         ⟨hr₂.trans hr₁, hlf₂'⟩⟩⟩⟩,
   fun a hr hlf =>
     let ⟨hr₂, hlf₂⟩ := h12.2.2 a hr hlf
     h23.2.2 a hr₂ hlf₂⟩

theorem mono {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs₁ regs₂ : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roRegs m₁ m₂ regs₁)
    (hsub : ∀ a, (∀ r ∈ regs₂, OutsideRegion r.1 r.2 a) → ∀ r ∈ regs₁, OutsideRegion r.1 r.2 a) :
    S2FrameRO roRegs m₁ m₂ regs₂ :=
  ⟨fun a hr hlf hout => h.1 a hr hlf (hsub a hout),
   ⟨h.2.1.1,
    ⟨h.2.1.2.1, fun a hpn hout => h.2.1.2.2 a hpn (hsub a hout)⟩⟩,
   h.2.2⟩

theorem mono_ro {roRegs₁ roRegs₂ : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roRegs₁ m₁ m₂ regs)
    (hro : ∀ a, (∀ ro ∈ roRegs₂, OutsideRegion ro.1 ro.2 a) →
      ∀ ro ∈ roRegs₁, OutsideRegion ro.1 ro.2 a) :
    S2FrameRO roRegs₂ m₁ m₂ regs :=
  ⟨h.1,
   ⟨⟨fun a hout hnl => h.2.1.1.1 a (hro a hout) hnl,
     fun a hout hrw => h.2.1.1.2 a (hro a hout) hrw⟩,
    h.2.1.2⟩,
   h.2.2⟩

theorem trans_agreesOutside {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ m₃ : Memory}
    {regs : List (BitVec 64 × ℕ)} {base : BitVec 64} {len : ℕ}
    (hf : S2FrameRO roRegs m₁ m₂ regs) (hmem : (base, len) ∈ regs)
    (hag : AgreesOutside m₂ m₃ base len) :
    S2FrameRO roRegs m₁ m₃ regs :=
  hf.trans (of_frame (Frame.trans_agreesOutside (Frame.refl m₂ regs) hmem hag))

theorem trans_agreesOutside_sub {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ m₃ : Memory}
    {regs : List (BitVec 64 × ℕ)} {rbase base : BitVec 64} {rlen len : ℕ}
    (hf : S2FrameRO roRegs m₁ m₂ regs) (hmem : (rbase, rlen) ∈ regs)
    (hsub : (base - rbase).toNat + len ≤ rlen)
    (hag : AgreesOutside m₂ m₃ base len) :
    S2FrameRO roRegs m₁ m₃ regs :=
  hf.trans (of_frame (Frame.trans_agreesOutside_sub (Frame.refl m₂ regs) hmem hsub hag))

theorem readable_of_readable {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roRegs m₁ m₂ regs) (a : BitVec 64) (n : ℕ)
    (hr : m₁.Readable a n) : m₂.Readable a n :=
  fun x hx => h.2.2 x (hr x hx).1 (hr x hx).2

theorem rw_of_rw {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roRegs m₁ m₂ regs) (a : BitVec 64) (n : ℕ)
    (hout : ∀ ro ∈ roRegs, ∀ x, InRegion ro.1 ro.2 x → OutsideRegion a n x)
    (hrw : RW m₁ a n) : RW m₂ a n := by
  intro x hx
  refine h.2.1.1.1 x (fun ro hro => ?_) (hrw x hx)
  rw [outsideRegion_iff_not_inRegion]
  intro hin
  exact (outsideRegion_iff_not_inRegion a n x).mp (hout ro hro x hin) hx

theorem readBytes_eq_of_readable {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roRegs m₁ m₂ regs) {addr : BitVec 64} {len : ℕ}
    (hread : m₁.Readable addr len)
    (hout : ∀ r ∈ regs, ∀ x, InRegion addr len x → OutsideRegion r.1 r.2 x)
    (hlen : len ≤ 2 ^ 64 := by decide) :
    m₂.readBytes addr len = m₁.readBytes addr len := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < len := by simpa using h1
  have hin : InRegion addr len (addr + BitVec.ofNat 64 i) :=
    inRegion_base_add addr len i hi hlen
  exact hf.1 _ (hread _ hin).1 (hread _ hin).2 (fun r hr => hout r hr _ hin)

theorem readBytes_eq {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roRegs m₁ m₂ regs) {addr : BitVec 64} {len : ℕ}
    (hread : m₁.Readable addr len)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr len) (hlen : len ≤ 2 ^ 64 := by decide) :
    m₂.readBytes addr len = m₁.readBytes addr len :=
  hf.readBytes_eq_of_readable hread (fun r hr _ hin => (hd r hr).outside hin hlen) hlen

theorem read64_eq_of_readable {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roRegs m₁ m₂ regs) {addr : BitVec 64}
    (hread : m₁.Readable addr 8)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr 8) :
    m₂.read64 addr = m₁.read64 addr := by
  have hbytes := hf.readBytes_eq hread hd (by decide)
  rw [Bytes.readBytes_8_eq, Bytes.readBytes_8_eq] at hbytes
  simp only [List.cons.injEq, and_true] at hbytes
  rcases hbytes with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]

end S2FrameRO

/-- Every heap satisfying `P` owns read-only cells across `ro = (base, len)`. -/
def HasROAt (ro : BitVec 64 × ℕ) (P : SepProp) : Prop :=
  ∀ h, P h → ∀ a, InRegion ro.1 ro.2 a → ∃ v, h a = some (.ro v)

namespace HasROAt

theorem pointsToBytesRO {p : BitVec 64} {bs : List (BitVec 8)} (hle : bs.length ≤ 2 ^ 64) :
    HasROAt (p, bs.length) (p ↦ᵣ bs) := by
  intro h hp a ha
  obtain ⟨m₀, -, rfl⟩ := ((IsBlockRO.pointsToBytesRO p bs hle).iff h).mp hp
  exact ⟨m₀.read8 a, by simp [regionHeapRO, ha]⟩

theorem sepConj_left {ro : BitVec 64 × ℕ} {P Q : SepProp} (hP : HasROAt ro P) :
    HasROAt ro (P ∗ Q) := by
  intro h hh a ha
  obtain ⟨h1, h2, _, rfl, hp1, _⟩ := SepProp.holds_sepConj_elim hh
  obtain ⟨v, hv⟩ := hP h1 hp1 a ha
  exact ⟨v, by simp [Heap.union, hv]⟩

theorem sepConj_right {ro : BitVec 64 × ℕ} {P Q : SepProp} (hQ : HasROAt ro Q) :
    HasROAt ro (P ∗ Q) := by
  intro h hh a ha
  obtain ⟨h1, h2, hd, rfl, _, hp2⟩ := SepProp.holds_sepConj_elim hh
  obtain ⟨v, hv⟩ := hQ h2 hp2 a ha
  rcases hd.1 a with h1n | h2n | ⟨_, h1ro, _⟩
  · have h1n' : h1 a = none := h1n
    exact ⟨v, by simp [Heap.union, h1n', hv]⟩
  · have h2n' : h2 a = none := h2n
    rw [hv] at h2n'; cases h2n'
  · cases hc : h1 a with
    | none => exact ⟨v, by simp [Heap.union, hc, hv]⟩
    | some c =>
      have hc' : h1.phys a = some c := hc
      rw [hc'] at h1ro
      cases c with
      | ro v1 => exact ⟨v1, by simp [Heap.union, hc]⟩
      | rw _ => cases h1ro
      | protNone _ => cases h1ro
      | lazy => cases h1ro
      | protNoneLazy => cases h1ro

end HasROAt

/-- Update two RW `IsBlock` regions across `S2FrameRO roRegs` while preserving `R`, provided every
`ro ∈ roRegs` is backed by read-only cells in `R` (`HasROAt ro R`). -/
theorem S2FrameRO.update_two_blocks_ro {roRegs : List (BitVec 64 × ℕ)}
    {P1 P1' P2 P2' R : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ1' Φ2 Φ2' : Memory → Prop} {m m' : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (hro_R : ∀ ro ∈ roRegs, HasROAt ro R)
    (h : m ⊨ P1 ∗ (P2 ∗ R))
    (hf : S2FrameRO roRegs m m' [(b1, n1), (b2, n2)])
    (hΦ1' : Φ1' m') (hΦ2' : Φ2' m') :
    m' ⊨ P1' ∗ (P2' ∗ R) := by
  have hrw1 : RW m b1 n1 := fun a ha => hb1.permNoLazy_rw h ha
  have h_swap : m ⊨ P2 ∗ (P1 ∗ R) := by rw [sepConj_left_comm]; exact h
  have hrw2 : RW m b2 n2 := fun a ha => hb2.permNoLazy_rw h_swap ha
  obtain ⟨h1, h2R, hd1, hp1, hp2R, hm⟩ := Satisfies.sepConj_elim h
  obtain ⟨h2, hR, hd2, rfl, hp2, hpR⟩ := SepProp.holds_sepConj_elim hp2R
  have hm2R : (h2.union hR).Matches m := Heap.Matches.of_union_right hd1 hm
  have hmR : hR.Matches m := Heap.Matches.of_union_right hd2 hm2R
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  have hout_ro_1 : ∀ ro ∈ roRegs, ∀ a, InRegion ro.1 ro.2 a → OutsideRegion b1 n1 a := by
    intro ro hro_mem a ha_ro
    rw [outsideRegion_iff_not_inRegion]
    intro ha1
    obtain ⟨v_ro, hRa⟩ := hro_R ro hro_mem hR hpR a ha_ro
    rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
    · simp [regionHeap, ha1] at h1n
    · by_cases ha2 : InRegion b2 n2 a
      · simp [Heap.union, regionHeap, ha2] at h2Rn
      · simp [Heap.union, regionHeap, ha2, hRa] at h2Rn
    · simp [regionHeap, ha1] at h1ro
  have hout_ro_2 : ∀ ro ∈ roRegs, ∀ a, InRegion ro.1 ro.2 a → OutsideRegion b2 n2 a := by
    intro ro hro_mem a ha_ro
    rw [outsideRegion_iff_not_inRegion]
    intro ha2
    obtain ⟨v_ro, hRa⟩ := hro_R ro hro_mem hR hpR a ha_ro
    rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
    · simp [regionHeap, ha2] at h2n
    · rw [hRa] at hRn; cases hRn
    · simp [regionHeap, ha2] at h2ro
  have hrw1' : RW m' b1 n1 := hf.rw_of_rw b1 n1 hout_ro_1 hrw1
  have hrw2' : RW m' b2 n2 := hf.rw_of_rw b2 n2 hout_ro_2 hrw2
  let h1' := regionHeap b1 n1 m'
  let h2' := regionHeap b2 n2 m'
  have hp1' : P1' h1' := (hb1'.iff h1').mpr ⟨m', hΦ1', rfl⟩
  have hp2' : P2' h2' := (hb2'.iff h2').mpr ⟨m', hΦ2', rfl⟩
  have hm1' : h1'.Matches m' := IsBlock.regionHeap_matches b1 n1 m' hrw1'
  have hm2' : h2'.Matches m' := IsBlock.regionHeap_matches b2 n2 m' hrw2'
  have hd2' : h2'.Disjoint hR := by
    apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
    intro a
    by_cases ha2 : InRegion b2 n2 a
    · rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
      · simp [regionHeap, ha2] at h2n
      · exact Or.inr (Or.inl hRn)
      · simp [regionHeap, ha2] at h2ro
    · exact Or.inl (by simp [h2', regionHeap, ha2])
  have hd1' : h1'.Disjoint (h2'.union hR) := by
    apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
    intro a
    by_cases ha1 : InRegion b1 n1 a
    · rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
      · simp [regionHeap, ha1] at h1n
      · refine Or.inr (Or.inl ?_)
        by_cases ha2 : InRegion b2 n2 a
        · simp [Heap.union, regionHeap, ha2] at h2Rn
        · simp [Heap.union, regionHeap, ha2] at h2Rn
          simp [Heap.union, h2', regionHeap, ha2, h2Rn]
      · simp [regionHeap, ha1] at h1ro
    · exact Or.inl (by simp [h1', regionHeap, ha1])
  have hmR' : hR.Matches m' := by
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => hf.2.1.2.1 a (hmR.2.2 a hmap)⟩
    have hn2 : ¬ InRegion b2 n2 a := by
      intro ha2
      rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
      · simp [regionHeap, ha2] at h2n
      · rw [hc] at hRn; cases hRn
      · simp [regionHeap, ha2] at h2ro
    have hn1 : ¬ InRegion b1 n1 a := by
      intro ha1
      rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
      · simp [regionHeap, ha1] at h1n
      · simp [Heap.union, regionHeap, hn2, hc] at h2Rn
      · simp [regionHeap, ha1] at h1ro
    have ha_out : ∀ r ∈ [(b1, n1), (b2, n2)], OutsideRegion r.1 r.2 a := by
      intro r hr_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl
      · exact (outsideRegion_iff_not_inRegion b1 n1 a).mpr hn1
      · exact (outsideRegion_iff_not_inRegion b2 n2 a).mpr hn2
    cases c with
    | rw v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.rw v) hc
      have hr_true : (m.perm a).r = true := by rw [hperm]; rfl
      have hout_ro : ∀ ro ∈ roRegs, OutsideRegion ro.1 ro.2 a := by
        intro ro hro_mem
        rw [outsideRegion_iff_not_inRegion]
        intro hin_ro
        obtain ⟨v_ro, hRa⟩ := hro_R ro hro_mem hR hpR a hin_ro
        rw [hRa] at hc
        cases hc
      have hnl : m.permNoLazy a = some Perm.rw :=
        Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hperm, hlf⟩
      obtain ⟨hperm', hlf'⟩ :=
        Memory.permNoLazy_eq_some_rw_iff.mp (hf.2.1.1.1 a hout_ro hnl)
      exact ⟨(hf.1 a hr_true hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | ro v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.ro v) hc
      obtain ⟨hperm', hlf'⟩ := hf.2.2 a hperm hlf
      exact ⟨(hf.1 a hperm hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | protNone v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.protNone v) hc
      obtain ⟨hperm_m', hlf_fn⟩ := hf.2.1.2.2 a hperm ha_out
      obtain ⟨hr_m', hlf_m'⟩ := hlf_fn hlf
      exact ⟨hr_m'.trans hr_eq, hperm_m', hlf_m'⟩
    | lazy =>
      have hperm := hmR.1 a .lazy hc
      have hout_ro : ∀ ro ∈ roRegs, OutsideRegion ro.1 ro.2 a := by
        intro ro hro_mem
        rw [outsideRegion_iff_not_inRegion]
        intro hin_ro
        obtain ⟨v_ro, hRa⟩ := hro_R ro hro_mem hR hpR a hin_ro
        rw [hRa] at hc
        cases hc
      exact hf.2.1.1.2 a hout_ro hperm
    | protNoneLazy =>
      have hperm := hmR.1 a .protNoneLazy hc
      exact (hf.2.1.2.2 a hperm ha_out).1
  exact Satisfies.sepConj_intro hd1' hp1' (SepProp.holds_sepConj_intro hd2' hp2' hpR)
    (Heap.Matches.union hm1' (Heap.Matches.union hm2' hmR'))

/-- Pointwise byte agreement on `P : BitVec 64 → Prop`. -/
def AgreesOn (P : BitVec 64 → Prop) (m₁ m₂ : Memory) : Prop :=
  ∀ a, P a → m₁.read8 a = m₂.read8 a

namespace AgreesOn

theorem readBytes_eq {P : BitVec 64 → Prop} {m₁ m₂ : Memory} (h : AgreesOn P m₁ m₂)
    (base : BitVec 64) (len : ℕ) (hlen : len ≤ 2 ^ 64)
    (hP : ∀ a, InRegion base len a → P a) :
    m₁.readBytes base len = m₂.readBytes base len :=
  Memory.readBytes_congr_region hlen fun a ha => h a (hP a ha)

theorem read64_eq {P : BitVec 64 → Prop} {m₁ m₂ : Memory} (h : AgreesOn P m₁ m₂)
    (base : BitVec 64) (hP : ∀ a, InRegion base 8 a → P a) :
    m₁.read64 base = m₂.read64 base :=
  Memory.read64_congr fun a ha => h a (hP a ha)

theorem finSaved_of {P : BitVec 64 → Prop} {s0 : State} {fsp : BitVec 64} {m₁ m₂ : Memory}
    (h : AgreesOn P m₁ m₂) (hs : FinSaved s0 fsp m₂)
    (hP : ∀ a, InRegion (fsp + 0x40#64) 0x50 a → P a) :
    FinSaved s0 fsp m₁ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hsub (off : BitVec 64) (hoff : (off - (fsp + 0x40#64)).toNat + 8 ≤ 0x50) :
      ∀ a, InRegion off 8 a → P a := by
    intro a ha; apply hP; unfold InRegion at ha ⊢; bv_omega
  exact ⟨(h.read64_eq (fsp + 0x40#64) (hsub _ (by bv_omega))).trans h1,
         (h.read64_eq (fsp + 0x48#64) (hsub _ (by bv_omega))).trans h2,
         (h.read64_eq (fsp + 0x50#64) (hsub _ (by bv_omega))).trans h3,
         (h.read64_eq (fsp + 0x60#64) (hsub _ (by bv_omega))).trans h4,
         (h.read64_eq (fsp + 0x68#64) (hsub _ (by bv_omega))).trans h5,
         (h.read64_eq (fsp + 0x70#64) (hsub _ (by bv_omega))).trans h6,
         (h.read64_eq (fsp + 0x78#64) (hsub _ (by bv_omega))).trans h7,
         (h.read64_eq (fsp + 0x80#64) (hsub _ (by bv_omega))).trans h8,
         (h.read64_eq (fsp + 0x88#64) (hsub _ (by bv_omega))).trans h9⟩

theorem hmacSt_of {P : BitVec 64 → Prop} {m₁ m₂ : Memory} {hm : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key msg : List (BitVec 8)}
    (h : AgreesOn P m₁ m₂) (hst : HmacSt m₂ hm F key msg)
    (hP : ∀ a, InRegion hm 0x90 a → P a) :
    HmacSt m₁ hm F key msg := by
  rcases hst with ⟨hlen, hmsg, hpos, hin, hibl, hout, hobl⟩
  have hsub (off : BitVec 64) (sz : ℕ) (hoff : 0 < sz ∧ (off - hm).toNat + sz ≤ 0x90) :
      ∀ a, InRegion off sz a → P a := by
    intro a ha; apply hP; rcases hoff with ⟨_, _⟩; unfold InRegion at ha ⊢; bv_omega
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm0 : msg.length = 0
    · simp [hm0] at hmsg ⊢; exact hmsg
    · exact (h.readBytes_eq hm msg.length (by omega)
        (hsub hm msg.length ⟨by omega, by simp; omega⟩)).trans hmsg
  · exact (h (hm + 0x3f#64) (hP _ (by unfold InRegion; bv_omega))).trans hpos
  · exact (h.readBytes_eq (hm + 0x40#64) 32 (by decide)
      (hsub (hm + 0x40#64) 32 ⟨by decide, by bv_omega⟩)).trans hin
  · exact (h.read64_eq (hm + 0x60#64)
      (hsub (hm + 0x60#64) 8 ⟨by decide, by bv_omega⟩)).trans hibl
  · exact (h.readBytes_eq (hm + 0x68#64) 32 (by decide)
      (hsub (hm + 0x68#64) 32 ⟨by decide, by bv_omega⟩)).trans hout
  · exact (h.read64_eq (hm + 0x88#64)
      (hsub (hm + 0x88#64) 8 ⟨by decide, by bv_omega⟩)).trans hobl

theorem hmacStN_of {P : BitVec 64 → Prop} {m₁ m₂ : Memory} {hm : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key pfx tail : List (BitVec 8)}
    (h : AgreesOn P m₁ m₂) (hst : HmacStN m₂ hm F key pfx tail)
    (hP : ∀ a, InRegion hm 0x90 a → P a) :
    HmacStN m₁ hm F key pfx tail := by
  rcases hst with ⟨hmod, hlen, hmsg, hpos, hin, hibl, hout, hobl⟩
  have hsub (off : BitVec 64) (sz : ℕ) (hoff : 0 < sz ∧ (off - hm).toNat + sz ≤ 0x90) :
      ∀ a, InRegion off sz a → P a := by
    intro a ha; apply hP; rcases hoff with ⟨_, _⟩; unfold InRegion at ha ⊢; bv_omega
  refine ⟨hmod, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm0 : tail.length = 0
    · simp [hm0] at hmsg ⊢; exact hmsg
    · exact (h.readBytes_eq hm tail.length (by omega)
        (hsub hm tail.length ⟨by omega, by simp; omega⟩)).trans hmsg
  · exact (h (hm + 0x3f#64) (hP _ (by unfold InRegion; bv_omega))).trans hpos
  · exact (h.readBytes_eq (hm + 0x40#64) 32 (by decide)
      (hsub (hm + 0x40#64) 32 ⟨by decide, by bv_omega⟩)).trans hin
  · exact (h.read64_eq (hm + 0x60#64)
      (hsub (hm + 0x60#64) 8 ⟨by decide, by bv_omega⟩)).trans hibl
  · exact (h.readBytes_eq (hm + 0x68#64) 32 (by decide)
      (hsub (hm + 0x68#64) 32 ⟨by decide, by bv_omega⟩)).trans hout
  · exact (h.read64_eq (hm + 0x88#64)
      (hsub (hm + 0x88#64) 8 ⟨by decide, by bv_omega⟩)).trans hobl

theorem of_s2FrameRO_writeBytes {roRegs : List (BitVec 64 × ℕ)} {m m' : Memory}
    {dst stk : BitVec 64} {bs : List (BitVec 8)} {stkLen : ℕ}
    (hdst : m'.readBytes dst bs.length = bs)
    (hframe : S2FrameRO roRegs m m' [(dst, bs.length), (stk, stkLen)])
    (hlen : bs.length ≤ 2 ^ 64) :
    AgreesOn (fun a => ((m.perm a).r = true ∧ m.isLazyFree a = false) ∧ OutsideRegion stk stkLen a)
      m' (m.writeBytes dst bs) := by
  intro a ⟨⟨hr, hlf⟩, hstk⟩
  by_cases hin : InRegion dst bs.length a
  · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset dst bs.length a hlen).mp hin
    have hwb : (m.writeBytes dst bs).readBytes dst bs.length = bs :=
      Memory.readBytes_writeBytes_same m dst bs hlen
    exact read8_eq_of_readBytes_eq (hdst.trans hwb.symm) hi
  · have hout_dst : OutsideRegion dst bs.length a :=
      (outsideRegion_iff_not_inRegion dst bs.length a).mpr hin
    have h1 : m'.read8 a = m.read8 a := by
      refine hframe.1 a hr hlf fun r hr_mem => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl
      · exact hout_dst
      · exact hstk
    have h2 : (m.writeBytes dst bs).read8 a = m.read8 a :=
      (ProofLib.AgreesOutside.writeBytes_self m dst bs).1 a hout_dst
    exact h1.trans h2.symm

theorem of_s2Frame_writeBytes {m m' : Memory} {dst stk : BitVec 64} {bs : List (BitVec 8)}
    {stkLen : ℕ}
    (hdst : m'.readBytes dst bs.length = bs)
    (hframe : S2Frame m m' [(dst, bs.length), (stk, stkLen)])
    (hlen : bs.length ≤ 2 ^ 64) :
    AgreesOn (fun a => ((m.perm a).r = true ∧ m.isLazyFree a = false) ∧ OutsideRegion stk stkLen a)
      m' (m.writeBytes dst bs) :=
  of_s2FrameRO_writeBytes hdst (S2FrameRO.of_s2frame (roRegs := []) hframe) hlen

end AgreesOn

theorem disjointRegions_of_outside {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hout : ∀ a, InRegion b₁ n₁ a → OutsideRegion b₂ n₂ a) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  have hdisj : ∀ a, ¬ (InRegion b₁ n₁ a ∧ InRegion b₂ n₂ a) := by
    intro a ⟨h1, h2⟩
    exact (outsideRegion_iff_not_inRegion b₂ n₂ a).mp (hout a h1) h2
  constructor
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₂ ⟨by simp only [InRegion]; omega,
      by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₁ ⟨by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega,
      by simp only [InRegion]; omega⟩

/-! ## Unified Input-Slice Invariant `KdfSliceInv` & Subroutine Cut-Point Interfaces -/

/-- Unified RO/RW slice invariant preserved across `S2FrameRO roRegs` and subslicing. -/
structure KdfSliceInv (ro : Bool) (roRegs : List (BitVec 64 × ℕ)) (m : Memory)
    (p : BitVec 64) (bs : List (BitVec 8)) (stkBase : BitVec 64) (stkLen : ℕ)
    (okmA : BitVec 64) (okmLen : ℕ) : Prop where
  bytes_eq : m.readBytes p bs.length = bs
  readable : m.Readable p bs.length
  perm_inv : if ro then ∀ a, InRegion p bs.length a → ∃ r ∈ roRegs, InRegion r.1 r.2 a
             else RW m p bs.length ∧ ∀ r ∈ roRegs, ∀ a, InRegion r.1 r.2 a → OutsideRegion p bs.length a
  out_stk  : ∀ a, InRegion p bs.length a → OutsideRegion stkBase stkLen a
  out_okm  : ∀ a, InRegion p bs.length a → OutsideRegion okmA okmLen a

namespace KdfSliceInv

theorem of_s2FrameRO {ro : Bool} {roRegs : List (BitVec 64 × ℕ)} {m₁ m₂ : Memory}
    {p : BitVec 64} {bs : List (BitVec 8)} {stkBase : BitVec 64} {stkLen : ℕ}
    {okmA : BitVec 64} {okmLen : ℕ}
    (hs : KdfSliceInv ro roRegs m₁ p bs stkBase stkLen okmA okmLen)
    (hf : S2FrameRO roRegs m₁ m₂ [(okmA, okmLen), (stkBase, stkLen)])
    (hlen : bs.length ≤ 2 ^ 64) :
    KdfSliceInv ro roRegs m₂ p bs stkBase stkLen okmA okmLen where
  bytes_eq := by
    refine (hf.readBytes_eq_of_readable hs.readable (fun r hr x hx => ?_) hlen).trans hs.bytes_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.out_okm x hx
    · exact hs.out_stk x hx
  readable := hf.readable_of_readable p bs.length hs.readable
  perm_inv := by
    cases ro
    · simp only [Bool.false_eq_true, ↓reduceIte] at hs ⊢
      exact ⟨hf.rw_of_rw p bs.length hs.perm_inv.2 hs.perm_inv.1, hs.perm_inv.2⟩
    · simp only [↓reduceIte] at hs ⊢
      exact hs.perm_inv
  out_stk := hs.out_stk
  out_okm := hs.out_okm

end KdfSliceInv

/-- Bundled entry preconditions of `finalize_fixed [local#2]` at `16528` B stack. -/
structure FinPre3GenExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s₀ : State) : Prop where
  frz          : img.FrozenLoaded s₀
  sym          : s₀.symtab = img.symtab
  pc_eq        : s₀.pc = img.base + bv% (ls_off% finalizeFixed3Name)
  status       : s₀.status = .Running
  pfx_lt       : pfx.length < 2 ^ 63
  tail_lt      : tail.length < 64
  hmac_st      : HmacStN s₀.mem (s₀.readReg64 .x1) F (effectiveHmacKey F key) pfx tail
  rw_out       : RW s₀.mem (s₀.readReg64 .x0) 32
  rw_hm        : RW s₀.mem (s₀.readReg64 .x1) 0x90
  rw_fsp       : RW s₀.mem (s₀.sp - 16528#64) 16528
  disj_out_hm  : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.sp - 16528#64) 16528
  disj_hm_fsp  : DisjointRegions (s₀.readReg64 .x1) 0x90 (s₀.sp - 16528#64) 16528
  sp_aligned   : (s₀.sp &&& 15#64) = 0#64

/-- Generalized `RunsToE` contract of `finalize_fixed [local#2]` at `16528` B stack. -/
def Fin3GenRunsToEExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {key pfx tail : List (BitVec 8)} {s₀ : State},
    FinPre3GenExt img F key pfx tail s₀ →
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key (pfx ++ tail) ∧
      S2Frame s₀.mem s'.mem
        [(s₀.readReg64 .x0, 32), (s₀.readReg64 .x1, 0x90), (s₀.sp - 16528#64, 16528)])

/-- Bundled entry preconditions of `new_from_slice [local#2]` at `16928` B stack. -/
structure Nfs3GenPreExt (img : Obj.Image) (keyRO : Bool) (roRegs : List (BitVec 64 × ℕ))
    (s₀ : State) : Prop where
  frz          : img.FrozenLoaded s₀
  sym          : s₀.symtab = img.symtab
  pc_eq        : s₀.pc = img.base + bv% (ls_off% newFromSlice3Name)
  status       : s₀.status = .Running
  key_lt       : (s₀.readReg64 .x2).toNat < 2 ^ 63
  ro_iv_bytes  : s₀.mem.readBytes (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV
  base_al      : (img.base &&& 0xfff#64) = 0#64
  ro_iv_read   : s₀.mem.Readable (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32
  disj_iv_stk  : DisjointRegions (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 16928#64) 16928
  rw_out       : RW s₀.mem (s₀.readReg64 .x0) 0x98
  rw_stk       : RW s₀.mem (s₀.sp - 16928#64) 16928
  disj_out_stk : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 16928#64) 16928
  key_read     : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
  key_perm     : if keyRO then (s₀.readReg64 .x2).toNat ≤ 64 ∧
                   (∀ a, InRegion (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat a →
                     ∃ r ∈ roRegs, InRegion r.1 r.2 a)
                 else RW s₀.mem (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
  out_key_stk  : ∀ a, InRegion (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat a →
                   OutsideRegion (s₀.sp - 16928#64) 16928 a
  out_key_out  : ∀ a, InRegion (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat a →
                   OutsideRegion (s₀.readReg64 .x0) 0x98 a
  sp_aligned   : (s₀.sp &&& 15#64) = 0#64

/-- Generalized `RunsToE` contract of `new_from_slice [local#2]` at `16928` B stack. -/
def Nfs3GenRunsToEExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {keyRO : Bool} {roRegs : List (BitVec 64 × ℕ)} {s₀ : State},
    Nfs3GenPreExt img keyRO roRegs s₀ →
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F
        (effectiveHmacKey F (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)) [] ∧
      S2FrameRO roRegs s₀.mem s'.mem
        [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)])

end SpqrKdfExt

end CryptoVerification.SpqrV1.Kdf
