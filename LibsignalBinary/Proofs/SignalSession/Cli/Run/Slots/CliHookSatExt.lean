/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.E2E.HooksE.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed Hook Satisfaction and `trapUnlisted` Projections

Derives `HookSat` bundles, individual extern-hook projections, `AllocContractsX`, and `TraceFsSound`
on `cliExternsWith ext` and `trapUnlisted ext` directly from `CliExternsOk P A ext`, without
unfolding `cliHookTable` or importing `CliExternsWitness`. Also re-exports `trapUnlisted` transfer
lemmas via `TrapBridge`.
-/

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 Arm64.Process ProofLib ProofLib.Variant CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

local macro "not_panic" : tactic => `(tactic|
  simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames,
    E2E.rustAllocName, allocName, deallocName, reallocName, shimName,
    memcpyName, memmoveName, memsetName, allocZeroedName,
    aesEncName, aesDecName, formatInnerName, fmtWriteName,
    E2E.timeAddName, timeAddHookName,
    E2E.bcmpName, cliBcmpName,
    SignalSession.readFileName, SignalSession.writeFileName,
    SignalSession.readStdinName, SignalSession.writeStdoutName,
    E2E.durationSinceName, durationSinceHookName,
    pubFromSecretName, dhName, staticDropName, sharedDropName,
    E2E.compress512Name, E2E.toEdwardsName, E2E.compressName, E2E.edNegName,
    E2E.torsionFreeName, E2E.dsmbName, E2E.scalarModName, E2E.scalarWideName,
    E2E.kemEncapsName, E2E.kemDecapsName,
    mlkemFromSeedName, mlkemPk1Name, mlkemPk2Name, mlkemEncaps1Name,
    mlkemEncaps2Name, mlkemDecapsName, mlkemValidatePkName, libcruxHmacName])

/-! ## 1. Spec-transport, `.keepsFs`, and stack-monotonicity combinators -/

private theorem hookOk_map {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β} (g : β → α)
    (I : State → State → Prop) (hI : ∀ s, I s (f s))
    (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0 sf, I s0 sf → s0.mem ⊨ s₂.pre y s0 ∗ R →
      sf.mem ⊨ s₁.post (g y) s0 sf ∗ R → sf.mem ⊨ s₂.post y s0 sf ∗ R)
    (hpanic : ∀ y R s0 sf, sf.mem ⊨ s₁.onPanic (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onPanic y s0 sf ∗ R)
    (hexit : ∀ y c R s0 sf,
      sf.mem ⊨ s₁.onExit (g y) c s0 sf ∗ R → sf.mem ⊨ s₂.onExit y c s0 sf ∗ R)
    (hoom : ∀ y R s0 sf, sf.mem ⊨ s₁.onOom (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onOom y s0 sf ∗ R) :
    HookOk f s₂ := by
  intro y R s0 hrun hp hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hp) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hr, hc, hq⟩ | ⟨hs, hq⟩ | ⟨c, hs, hq⟩ | ⟨hs, hq⟩
  · exact Or.inl ⟨hr, hc, hpost y R s0 (f s0) (hI s0) hp hq⟩
  · exact Or.inr (Or.inl ⟨hs, hpanic y R s0 (f s0) hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hs, hexit y c R s0 (f s0) hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hs, hoom y R s0 (f s0) hq⟩))

theorem hookSat_map {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁) (hm : ∀ f, HookOk f s₁ → HookOk f s₂) :
    HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

theorem fsKept_cliExternsWith {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {n : String} {f : State → State}
    (hOk : CliExternsOk P A ext) (hf : cliExternsWith ext n = some f)
    (hio : n ∉ CliExt.ioNames) (s : State) : (f s).fs = s.fs :=
  (cliExternsOk_cliExternsWith hOk).fsKept n f hf hio s

theorem hookOk_stack_mono {α : Type} {f : State → State} {base : Spec α} {stk₁ stk₂ : Nat}
    (hh : HookOk f (withStack base stk₁))
    (hle : stk₁ ≤ stk₂) (hmax : stk₂ ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x c s0 sf, base.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withStack base stk₂) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp stk₂ =
      memRegion (s0.sp - BitVec.ofNat 64 stk₂) (stk₂ - stk₁) ∗ stackAt s0.sp stk₁ := by
    have h1 := stackAt_split_bottom s0.sp stk₁ (stk₂ - stk₁) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk₂) (stk₂ - stk₁) ∗ R
  have hpre' : s0.mem ⊨ (withStack base stk₁).pre x s0 ∗ R' := by
    dsimp only [withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hr, hc, hq⟩ | ⟨_, hp⟩ | ⟨c, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hr, hc, ?_⟩
    dsimp only [withStack, R'] at hq ⊢
    rw [hsplit]
    ac_nf at hq ⊢
  · dsimp only [withStack] at hp; rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [withStack] at he; rw [hex x c s0 (f s0), satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [withStack] at ho; rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho
    exact False.elim ho.1

/-! ## 2. `CliHookSat` projections on `cliExternsWith ext` -/

theorem ext_allocHooks {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) : AllocHooks A (cliExternsWith ext) where
  alloc := hookSat_cliExternsWith (by not_panic) hOk.alloc.alloc
  dealloc := hookSat_cliExternsWith (by not_panic) hOk.alloc.dealloc
  realloc := hookSat_cliExternsWith (by not_panic) hOk.alloc.realloc

abbrev cliExternsWith_allocHooks := @ext_allocHooks

theorem ext_allocZeroed {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) allocZeroedName (rustAllocZeroedSpec A) :=
  hookSat_cliExternsWith (by not_panic) hOk.allocZeroed

abbrev cliExternsWith_allocZeroed := @ext_allocZeroed

theorem ext_shim {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "__rustc::__rust_no_alloc_shim_is_unstable_v2" CliExt.shimSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.shim

abbrev cliExternsWith_shim := @ext_shim

theorem ext_aesEnc {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) aesEncName (aesEncSpec P.C.E A) :=
  hookSat_cliExternsWith (by not_panic) hOk.aesEnc

abbrev cliExternsWith_aesEnc := @ext_aesEnc

theorem ext_aesDec {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) aesDecName (aesDecSpec P.C.D A) :=
  hookSat_cliExternsWith (by not_panic) hOk.aesDec

abbrev cliExternsWith_aesDec := @ext_aesDec

theorem ext_formatInner {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) formatInnerName (formatInnerSpec A) :=
  hookSat_cliExternsWith (by not_panic) hOk.formatInner

abbrev cliExternsWith_formatInner := @ext_formatInner

theorem ext_fmtWrite {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) fmtWriteName (fmtWriteSpec A) :=
  hookSat_cliExternsWith (by not_panic) hOk.fmtWrite

abbrev cliExternsWith_fmtWrite := @ext_fmtWrite

theorem ext_tripleRatchetHooks {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (Sm : SpqrModel) :
    TripleRatchetHooks P.C A Sm (cliExternsWith ext) :=
  ⟨ext_allocHooks hOk, ext_allocZeroed hOk, ext_aesEnc hOk, ext_aesDec hOk,
    ext_formatInner hOk, ext_fmtWrite hOk⟩

abbrev cliExternsWith_tripleRatchetHooks := @ext_tripleRatchetHooks

theorem ext_timeAdd {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.timeAddName timeAddSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.timeAdd

abbrev cliExternsWith_timeAdd := @ext_timeAdd

theorem ext_bcmpSpec {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "bcmp" CliExt.bcmpSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.bcmp

abbrev cliExternsWith_bcmpSpec := @ext_bcmpSpec

theorem ext_bcmp {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) cliBcmpName cliBcmpSpec := by
  obtain ⟨f, hf, hok⟩ := hookSat_cliExternsWith (n := "bcmp") (by not_panic) hOk.bcmp
  exact ⟨f, hf, hookOk_map (s₁ := CliExt.bcmpSpec)
    (fun x => ⟨x.a, x.aRo, x.bsA, x.b, x.bRo, x.bsB⟩)
    (fun _ _ => True) (fun _ => trivial) hok
    (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)⟩

abbrev cliExternsWith_bcmp := @ext_bcmp

theorem ext_e2eBcmp {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.bcmpName E2E.HooksE.e2eBcmpSpec := by
  obtain ⟨f, hf, hok⟩ := hookSat_cliExternsWith (n := "bcmp") (by not_panic) hOk.bcmp
  refine ⟨f, hf, hookOk_map (s₁ := CliExt.bcmpSpec)
    (fun x => ⟨x.a, false, x.bsA, x.b, false, x.bsB⟩)
    (fun _ _ => True) (fun _ => trivial) hok
    (fun _ _ _ hp => ?_) (fun _ _ _ _ _ _ hq => ?_)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)⟩
  · simpa only [CliExt.bcmpSpec, E2E.HooksE.e2eBcmpSpec, CliExt.bytesAt,
      Bool.false_eq_true, ↓reduceIte] using hp
  · simpa only [CliExt.bcmpSpec, E2E.HooksE.e2eBcmpSpec, CliExt.bytesAt,
      Bool.false_eq_true, ↓reduceIte] using hq

abbrev cliExternsWith_e2eBcmp := @ext_e2eBcmp

theorem ext_spqrHooks {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    SpqrHooks P.C A P.Q.K (cliExternsWith ext) where
  fromSeed := hookSat_cliExternsWith (by not_panic) hOk.spqr.fromSeed
  pk1 := hookSat_cliExternsWith (by not_panic) hOk.spqr.pk1
  pk2 := hookSat_cliExternsWith (by not_panic) hOk.spqr.pk2
  encaps1 := hookSat_cliExternsWith (by not_panic) hOk.spqr.encaps1
  encaps2 := hookSat_cliExternsWith (by not_panic) hOk.spqr.encaps2
  decaps := hookSat_cliExternsWith (by not_panic) hOk.spqr.decaps
  validatePk := hookSat_cliExternsWith (by not_panic) hOk.spqr.validatePk
  hmac := hookSat_cliExternsWith (by not_panic) hOk.spqr.hmac

abbrev cliExternsWith_spqrHooks := @ext_spqrHooks

theorem ext_durationSinceEpoch {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.durationSinceName CliExt.durationSinceEpochSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.durationSince

abbrev cliExternsWith_durationSinceEpoch := @ext_durationSinceEpoch

/-! ## 3. `libc`, `core`, I/O, session, and PQXDH projections -/

theorem ext_memset {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "memset" CliExt.memsetSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.memset

abbrev cliExternsWith_memset := @ext_memset

theorem ext_memmove {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "memmove" CliExt.memmoveSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.memmove

abbrev cliExternsWith_memmove := @ext_memmove

theorem ext_memcpy {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "memcpy" CliExt.memcpySpec :=
  hookSat_cliExternsWith (by not_panic) hOk.memcpy

abbrev cliExternsWith_memcpy := @ext_memcpy

theorem ext_memcpyRO {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "memcpy" CliExt.memcpyROSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.memcpyRO

abbrev cliExternsWith_memcpyRO := @ext_memcpyRO

theorem ext_strlen {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "strlen" CliExt.strlenSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.strlen

abbrev cliExternsWith_strlen := @ext_strlen

theorem ext_memrchr {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "core::slice::memchr::memrchr" CliExt.memrchrSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.memrchr

abbrev cliExternsWith_memrchr := @ext_memrchr

theorem ext_fromUtf8 {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "core::str::converts::from_utf8" CliExt.fromUtf8Spec :=
  hookSat_cliExternsWith (by not_panic) hOk.fromUtf8

abbrev cliExternsWith_fromUtf8 := @ext_fromUtf8

theorem ext_readFile {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    HookSat (cliExternsWith ext) SignalSession.readFileName (CliExt.readFileSpec A img) :=
  hookSat_cliExternsWith (by not_panic) (hOk.readFile img)

abbrev cliExternsWith_readFile := @ext_readFile

theorem ext_writeFile {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    HookSat (cliExternsWith ext) SignalSession.writeFileName (CliExt.writeFileSpec img) :=
  hookSat_cliExternsWith (by not_panic) (hOk.writeFile img)

abbrev cliExternsWith_writeFile := @ext_writeFile

theorem ext_readStdin {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    HookSat (cliExternsWith ext) SignalSession.readStdinName (CliExt.readStdinSpec A img) :=
  hookSat_cliExternsWith (by not_panic) (hOk.readStdin img)

abbrev cliExternsWith_readStdin := @ext_readStdin

theorem ext_writeStdout {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    HookSat (cliExternsWith ext) SignalSession.writeStdoutName (CliExt.writeStdoutSpec img) :=
  hookSat_cliExternsWith (by not_panic) (hOk.writeStdout img)

abbrev cliExternsWith_writeStdout := @ext_writeStdout

theorem ext_blackBox {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "subtle::black_box::<u8>" CliExt.blackBoxSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.blackBox

abbrev cliExternsWith_blackBox := @ext_blackBox

theorem ext_compress256 {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "sha2::sha256::compress256" (CliExt.compress256Spec P.C) :=
  hookSat_cliExternsWith (by not_panic) hOk.compress256

abbrev cliExternsWith_compress256 := @ext_compress256

theorem ext_pubFromSecret {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) pubFromSecretName (CliExt.pubFromSecretSpec P.C) :=
  hookSat_cliExternsWith (by not_panic) hOk.pubFromSecret

abbrev cliExternsWith_pubFromSecret := @ext_pubFromSecret

theorem ext_dh {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) dhName (CliExt.dhSpec P.C) :=
  hookSat_cliExternsWith (by not_panic) hOk.dh

abbrev cliExternsWith_dh := @ext_dh

theorem ext_staticDrop {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) staticDropName CliExt.zeroizeSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.staticDrop

abbrev cliExternsWith_staticDrop := @ext_staticDrop

theorem ext_sharedDrop {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) sharedDropName CliExt.zeroizeSpec :=
  hookSat_cliExternsWith (by not_panic) hOk.sharedDrop

abbrev cliExternsWith_sharedDrop := @ext_sharedDrop

theorem ext_compress512 {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.compress512Name (CliExt.compress512Spec P.Q) :=
  hookSat_cliExternsWith (by not_panic) hOk.compress512

abbrev cliExternsWith_compress512 := @ext_compress512

theorem ext_toEdwards {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.toEdwardsName (CliExt.toEdwardsSpec P.Q) :=
  hookSat_cliExternsWith (by not_panic) hOk.toEdwards

abbrev cliExternsWith_toEdwards := @ext_toEdwards

theorem ext_compress {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.compressName (CliExt.pureByteFunctionSpec P.Q.compress false) :=
  hookSat_cliExternsWith (by not_panic) hOk.compress

abbrev cliExternsWith_compress := @ext_compress

theorem ext_edNeg {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.edNegName (CliExt.pureByteFunctionSpec P.Q.edNeg true) :=
  hookSat_cliExternsWith (by not_panic) hOk.edNeg

abbrev cliExternsWith_edNeg := @ext_edNeg

theorem ext_torsionFree {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.torsionFreeName (CliExt.torsionFreeSpec P.Q) :=
  hookSat_cliExternsWith (by not_panic) hOk.torsionFree

abbrev cliExternsWith_torsionFree := @ext_torsionFree

theorem ext_dsmb {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.dsmbName (CliExt.dsmbSpec P.Q) :=
  hookSat_cliExternsWith (by not_panic) hOk.dsmb

abbrev cliExternsWith_dsmb := @ext_dsmb

theorem ext_scalarMod {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.scalarModName (CliExt.pureByteFunctionSpec P.Q.scalarMod true) :=
  hookSat_cliExternsWith (by not_panic) hOk.scalarMod

abbrev cliExternsWith_scalarMod := @ext_scalarMod

theorem ext_scalarWide {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.scalarWideName (CliExt.pureByteFunctionSpec P.Q.scalarWide false) :=
  hookSat_cliExternsWith (by not_panic) hOk.scalarWide

abbrev cliExternsWith_scalarWide := @ext_scalarWide

theorem ext_kemEncaps {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.kemEncapsName (CliExt.kemEncapsSpec P.Q) :=
  hookSat_cliExternsWith (by not_panic) hOk.kemEncaps

abbrev cliExternsWith_kemEncaps := @ext_kemEncaps

theorem ext_kemDecaps {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) E2E.kemDecapsName (CliExt.kemDecapsSpec P.Q) :=
  hookSat_cliExternsWith (by not_panic) hOk.kemDecaps

abbrev cliExternsWith_kemDecaps := @ext_kemDecaps

/-! ## 4. Stack-framed `mem*` helpers, `AllocContractsX`, and `TraceFsSound` -/

theorem hookOk_sessionMemcpy_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpySpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpySpec stk) := by
  have h1 : HookOk f (withStack sessionMemcpyRegionSpec CliExt.memHookStack) :=
    hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memcpySpec, libcMemcpySpec, withStack,
        sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memcpySpec, withStack,
        sessionMemcpyRegionSpec, sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono h1 hle hmax
  exact hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_libcMemcpy_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemcpySpec stk)) : HookOk f (libcMemcpySpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_sessionMemcpyRegion_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemcpySpec stk)) :
    HookOk f (withStack sessionMemcpyRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_memcpyRegion_of_libc {f : State → State} {stk : Nat}
    (hh : HookOk f (libcMemcpySpec stk)) : HookOk f (withStack memcpyRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_sessionMemmove_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memmoveSpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemmoveSpec stk) := by
  let base : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
    { pre := fun (b, buf, dst, src, len) s0 =>
        ⌜s0.readReg64 .x0 = b + BitVec.ofNat 64 dst ∧
         s0.readReg64 .x1 = b + BitVec.ofNat 64 src ∧
         (s0.readReg64 .x2).toNat = len ∧
         dst + len ≤ buf.length ∧ src + len ≤ buf.length⌝ ∗ (b ↦ₛ buf)
      post := fun (b, buf, dst, src, len) s0 sf =>
        ⌜sf.readReg64 .x0 = b + BitVec.ofNat 64 dst ∧ sf.trace = s0.trace⌝ ∗
          (b ↦ₛ listMove buf dst src len) }
  have h1 : HookOk f (withStack base CliExt.memHookStack) :=
    hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memmoveSpec, libcMemmoveSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memmoveSpec, withStack, base,
        sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono h1 hle hmax
  exact hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemmoveSpec, libcMemmoveSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemmoveSpec, withStack, base,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_libcMemmove_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemmoveSpec stk)) : HookOk f (libcMemmoveSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemmoveSpec, libcMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_sessionMemset_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memsetSpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemsetSpec stk) := by
  let base : Spec (BitVec 64 × BitVec 8 × Nat) :=
    { pre := fun (ptr, c, len) s0 =>
        ⌜s0.readReg64 .x0 = ptr ∧ (s0.readReg32 .x1).truncate 8 = c ∧
         (s0.readReg64 .x2).toNat = len⌝ ∗ memRegion ptr len
      post := fun (ptr, c, len) s0 sf =>
        ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c) }
  have h1 : HookOk f (withStack base CliExt.memHookStack) :=
    hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memsetSpec, libcMemsetSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memsetSpec, withStack, base,
        sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono h1 hle hmax
  exact hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemsetSpec, libcMemsetSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack, base,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_libcMemset_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemsetSpec stk)) : HookOk f (libcMemsetSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemsetSpec, libcMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_sessionMemsetRegion_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemsetSpec stk)) :
    HookOk f (withStack sessionMemsetRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by
      simp only [sessionMemsetSpec, libcMemsetSpec, withStack, sessionMemsetRegionSpec,
        memsetRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩, hp.2⟩)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack,
      sessionMemsetRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem hookOk_memsetRegion_of_libc {f : State → State} {stk : Nat}
    (hh : HookOk f (libcMemsetSpec stk)) :
    HookOk f (withStack memsetRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by
      simp only [libcMemsetSpec, withStack, memsetRegionSpec, sepConj_assoc,
        satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩, hp.2⟩)
    (fun _ _ _ _ _ _ hq => by simpa only [libcMemsetSpec, withStack, memsetRegionSpec,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem stub_inImage_of_hookSat {α : Type} (img : Obj.Image)
    {ext : String → Option (State → State)} {fnName hname : String} {off : Nat} {spec : Spec α}
    (hoff : libsignalSessionCode.fnOff fnName = off)
    (hlt : off < 2 ^ 64)
    (hhook : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? off = H hname)
    (hnp : Rust.isPanicSymbol hname = false)
    (hsat : HookSat ext hname spec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr fnName) (spec.inImage img) := by
  refine subroutine_ok_inImage_of_subroutine_ok img ?_
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
    (hname := hname) (k := 0) hoff (Nat.add_zero _) hlt hhook hnp hsat
  simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

private theorem memHookStack_le_of_ext {stk : Nat} (hle : extHookStack ≤ stk) :
    CliExt.memHookStack ≤ stk :=
  Nat.le_trans (by decide : CliExt.memHookStack ≤ extHookStack) hle

private theorem hookOk_withStack' {α : Type} {h : State → State} {spec : Spec α}
    (hh : HookOk h spec) (stk : Nat)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk h (withStack spec stk) := by
  intro x R s0 hrun hpre hsp
  dsimp only [withStack] at hpre
  rw [sepConj_assoc] at hpre
  obtain ⟨hkf, hsym, hout⟩ := hh x (stackAt s0.sp stk ∗ R) s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan_sat⟩ | ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack]
    rwa [sepConj_assoc]
  · rw [hpan x s0 (h s0), satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rw [hex x code s0 (h s0), satisfies_pure_sepConj] at hex_sat
    exact False.elim hex_sat.1
  · rw [hoom x s0 (h s0), satisfies_pure_sepConj] at hoom_sat
    exact False.elim hoom_sat.1

private theorem hookOk_rustAllocWithStack' {h : State → State} {A : RustAlloc} {stk : Nat}
    (hh : HookOk h (rustAllocSpec A))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk h (rustAllocSpecWithStack A stk) := by
  intro ⟨size, align⟩ R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (stk - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustAllocSpec A).pre (size, align) s0 ∗ R' := by
    dsimp only [rustAllocSpecWithStack, rustAllocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh (size, align) R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocSpecWithStack, rustAllocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustAllocSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · dsimp only [rustAllocSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
  · dsimp only [rustAllocSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim

private theorem hookOk_rustDeallocExternWithStack' {h : State → State} {A : RustAlloc} {stk : Nat}
    (hh : HookOk h (rustDeallocSpec A))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk h (rustDeallocExternSpecWithStack A stk) := by
  intro ⟨p, size, align⟩ R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (stk - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustDeallocSpec A).pre (p, size, align) s0 ∗ R' := by
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hpure, hmem⟩
    refine ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1⟩, ?_⟩
    ac_nf at hmem ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh (p, size, align) R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustDeallocSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · dsimp only [rustDeallocSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
  · dsimp only [rustDeallocSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim

private theorem hookOk_rustReallocExternWithStack' {h : State → State} {A : RustAlloc} {stk : Nat}
    (hh : HookOk h (rustReallocSpec A))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk h (rustReallocExternSpecWithStack A stk) := by
  intro ⟨p, old, align, new, bs⟩ R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (stk - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustReallocSpec A).pre (p, old, align, new, bs) s0 ∗ R' := by
    dsimp only [rustReallocExternSpecWithStack, rustReallocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hpure, hmem⟩
    refine ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1,
      hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2⟩, ?_⟩
    ac_nf at hmem ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh (p, old, align, new, bs) R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustReallocExternSpecWithStack, rustReallocSpecWithStack, rustReallocSpec, R']
      at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustReallocSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · dsimp only [rustReallocSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
  · dsimp only [rustReallocSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim

/-- Full `AllocContractsX` on `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem ext_allocContractsX {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    AllocContractsX img A (cliExternsWith ext) where
  alloc := stub_inImage_of_hookSat img (ls_stub% "__rustc::__rust_alloc") (by decide)
    (ls_hook% "__rustc::__rust_alloc") (by simp [Rust.isPanicSymbol])
    (hookSat_map (ext_allocHooks hOk).alloc fun _ hh =>
      hookOk_rustAllocWithStack' hh (by decide) (by decide))
  dealloc := stub_inImage_of_hookSat img (ls_stub% "__rustc::__rust_dealloc") (by decide)
    (ls_hook% "__rustc::__rust_dealloc") (by simp [Rust.isPanicSymbol])
    (hookSat_map (ext_allocHooks hOk).dealloc fun _ hh =>
      hookOk_rustDeallocExternWithStack' hh (by decide) (by decide))
  realloc := stub_inImage_of_hookSat img (ls_stub% "__rustc::__rust_realloc") (by decide)
    (ls_hook% "__rustc::__rust_realloc") (by simp [Rust.isPanicSymbol])
    (hookSat_map (ext_allocHooks hOk).realloc fun _ hh =>
      hookOk_rustReallocExternWithStack' hh (by decide) (by decide))
  shim stk _ _ := stub_inImage_of_hookSat img
    (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.shim) fun _ hh =>
      hookOk_withStack' hh stk)
  memcpy stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memcpy") (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memcpy) fun _ hh =>
      hookOk_libcMemcpy_of_session (hookOk_sessionMemcpy_of_cliExt hh (memHookStack_le_of_ext hle) hmax))
  session_memcpy stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memcpy") (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memcpy) fun _ hh =>
      hookOk_sessionMemcpy_of_cliExt hh (memHookStack_le_of_ext hle) hmax)
  memcpy_region stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memcpy") (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memcpy) fun _ hh =>
      hookOk_memcpyRegion_of_libc
        (hookOk_libcMemcpy_of_session (hookOk_sessionMemcpy_of_cliExt hh (memHookStack_le_of_ext hle) hmax)))
  session_memcpy_region stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memcpy") (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memcpy) fun _ hh =>
      hookOk_sessionMemcpyRegion_of_session (hookOk_sessionMemcpy_of_cliExt hh (memHookStack_le_of_ext hle) hmax))
  memmove stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memmove") (by decide)
    (ls_hook% "memmove") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memmove) fun _ hh =>
      hookOk_libcMemmove_of_session (hookOk_sessionMemmove_of_cliExt hh (memHookStack_le_of_ext hle) hmax))
  session_memmove stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memmove") (by decide)
    (ls_hook% "memmove") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memmove) fun _ hh =>
      hookOk_sessionMemmove_of_cliExt hh (memHookStack_le_of_ext hle) hmax)
  memset stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memset") (by decide)
    (ls_hook% "memset") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memset) fun _ hh =>
      hookOk_libcMemset_of_session (hookOk_sessionMemset_of_cliExt hh (memHookStack_le_of_ext hle) hmax))
  session_memset stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memset") (by decide)
    (ls_hook% "memset") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memset) fun _ hh =>
      hookOk_sessionMemset_of_cliExt hh (memHookStack_le_of_ext hle) hmax)
  memset_region stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memset") (by decide)
    (ls_hook% "memset") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memset) fun _ hh =>
      hookOk_memsetRegion_of_libc
        (hookOk_libcMemset_of_session (hookOk_sessionMemset_of_cliExt hh (memHookStack_le_of_ext hle) hmax)))
  session_memset_region stk hle hmax := stub_inImage_of_hookSat img (ls_stub% "memset") (by decide)
    (ls_hook% "memset") (by simp [Rust.isPanicSymbol])
    (hookSat_map (hookSat_cliExternsWith (by not_panic) hOk.memset) fun _ hh =>
      hookOk_sessionMemsetRegion_of_session (hookOk_sessionMemset_of_cliExt hh (memHookStack_le_of_ext hle) hmax))

abbrev cliExternsWith_allocContractsX := @ext_allocContractsX
abbrev allocContractsX_of_externsOk := @ext_allocContractsX

private def IsFsChangeEv (e : TraceEvent) : Prop := e.isFsChange = true

private theorem isFsChangeEv_not_quiet (e : TraceEvent) (h : IsFsChangeEv e) : ¬ QuietEv e := by
  intro hq
  unfold IsFsChangeEv at h
  unfold QuietEv at hq
  cases e with
  | writeByte st b => cases st <;> simp [TraceEvent.isFsChange, quietEv] at h hq
  | userDefined tag p => simp [TraceEvent.isFsChange] at h
  | fileChanged p => simp [quietEv] at hq

private theorem externAt_fsTraced {P : Program}
    (hX : ∀ n f, P.externs n = some f → HookFsTraced IsFsChangeEv f)
    (hO : ∀ n f, P.overrides n = some f → HookFsTraced IsFsChangeEv f)
    {pc : BitVec 64} {f : State → State} (h : P.externAt? pc = some f) :
    HookFsTraced IsFsChangeEv f := by
  unfold Program.externAt? Program.hookAtOff? at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hX n f hno
    · cases hno
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hO n f hno
    · cases hno

/-- `TraceFsSound` on `tripleRatchetProgAtExt b (cliExternsWith ext)` from `hOk.fsTraced`. -/
theorem ext_traceFsSound {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    TraceFsSound (tripleRatchetProgAtExt b (cliExternsWith ext)) := by
  refine TraceFsSound.of_isFs isFsChangeEv_not_quiet fun _ _ hst =>
    Steps.files_eq_of_noFs (fun _ h => h) (fun _ _ h => externAt_fsTraced ?_ ?_ h) hst rfl
  · intro n f hf
    dsimp only [tripleRatchetProgAtExt, Program.rebase] at hf
    rw [withPanics_cliExternsWith] at hf
    exact (cliExternsOk_cliExternsWith hOk).fsTraced n f hf
  · intro _ _ hf
    dsimp only [tripleRatchetProgAtExt, Program.rebase] at hf
    cases hf

abbrev cliExternsWith_traceFsSound := @ext_traceFsSound
abbrev traceFsSound_cliExternsWith := @ext_traceFsSound

/-! ## 5. `trapUnlisted ext` corollaries -/

theorem trapUnlisted_allocHooks {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    AllocHooks A (trapUnlisted ext) := by
  simpa only [cliExternsWith_trapUnlisted] using ext_allocHooks (cliExternsOk_trapUnlisted hOk)

theorem trapUnlisted_tripleRatchetHooks {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (Sm : SpqrModel) :
    TripleRatchetHooks P.C A Sm (trapUnlisted ext) := by
  simpa only [cliExternsWith_trapUnlisted] using
    ext_tripleRatchetHooks (cliExternsOk_trapUnlisted hOk) Sm

theorem trapUnlisted_spqrHooks {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    SpqrHooks P.C A P.Q.K (trapUnlisted ext) := by
  simpa only [cliExternsWith_trapUnlisted] using ext_spqrHooks (cliExternsOk_trapUnlisted hOk)

theorem trapUnlisted_bcmp {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (trapUnlisted ext) cliBcmpName cliBcmpSpec := by
  simpa only [cliExternsWith_trapUnlisted] using ext_bcmp (cliExternsOk_trapUnlisted hOk)

theorem trapUnlisted_e2eBcmp {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (trapUnlisted ext) E2E.bcmpName E2E.HooksE.e2eBcmpSpec := by
  simpa only [cliExternsWith_trapUnlisted] using ext_e2eBcmp (cliExternsOk_trapUnlisted hOk)

theorem trapUnlisted_durationSinceEpoch {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (trapUnlisted ext) E2E.durationSinceName CliExt.durationSinceEpochSpec := by
  simpa only [cliExternsWith_trapUnlisted] using
    ext_durationSinceEpoch (cliExternsOk_trapUnlisted hOk)

theorem trapUnlisted_timeAdd {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (trapUnlisted ext) E2E.timeAddName timeAddSpec := by
  simpa only [cliExternsWith_trapUnlisted] using ext_timeAdd (cliExternsOk_trapUnlisted hOk)

theorem trapUnlisted_allocContractsX {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    AllocContractsX img A (trapUnlisted ext) := by
  simpa only [cliExternsWith_trapUnlisted] using
    ext_allocContractsX (cliExternsOk_trapUnlisted hOk) img

theorem trapUnlisted_traceFsSound {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    TraceFsSound (tripleRatchetProgAtExt b (trapUnlisted ext)) := by
  simpa only [cliExternsWith_trapUnlisted] using
    ext_traceFsSound (cliExternsOk_trapUnlisted hOk) b

abbrev traceFsSound_trapUnlisted := @trapUnlisted_traceFsSound

end CryptoVerification.SignalSession.Cli.Slots
