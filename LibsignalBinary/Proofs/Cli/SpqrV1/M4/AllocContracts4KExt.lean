/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack Allocator and Memory Contract Bundle (`AllocContracts4K`)

`recordDecryptSpec` (`signal_session_ratchet::decrypt_signal`) and `dropSessionStructureLocal2Spec`
allocate only `allocHookStack = 4096` B below their call frames (`CliExt.memHookStack = 4096` B),
and `DropSessionStructureLocal2OkExt` carries no `img.FrozenLoaded` hypothesis. This module packages
the raw `4096`-byte `alloc` / `dealloc` / `realloc` / `shim` / `memcpy` / `memmove` / `memset`
contracts on `tripleRatchetProgAtExt b ext` and proves them from `CliExternsOk P A ext` on any
`ext'` satisfying `Slots.AgreeOnCliHooks ext ext'`.
-/

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots (AgreeOnCliHooks)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem hookOk_map4k {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
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

private theorem hookSat_map4k {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem hookOk_stack_mono4k {α : Type} {f : State → State} {base : Spec α}
    {s1 s2 : Nat} (hh : HookOk f (withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withStack base s2) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (withStack base s1).pre x s0 ∗ R' := by
    dsimp only [withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [withStack] at hp; rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [withStack] at he; rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [withStack] at ho; rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho
    exact False.elim ho.1

private theorem hookOk_sessionMemcpy_of_cliExt4k {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpySpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpySpec stk) := by
  have h1 : HookOk f (withStack sessionMemcpyRegionSpec CliExt.memHookStack) :=
    hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memcpySpec, libcMemcpySpec, withStack,
        sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memcpySpec, withStack,
        sessionMemcpyRegionSpec, sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono4k h1 hle hmax
  exact hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
       sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_libcMemcpy_of_session4k {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemcpySpec stk)) : HookOk f (libcMemcpySpec stk) :=
  hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionMemcpyRegion_of_session4k {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemcpySpec stk)) :
    HookOk f (withStack sessionMemcpyRegionSpec stk) :=
  hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_memcpyRegion_of_libc4k {f : State → State} {stk : Nat}
    (hh : HookOk f (libcMemcpySpec stk)) : HookOk f (withStack memcpyRegionSpec stk) :=
  hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_memcpyRO_of_cliExt4k {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpyROSpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (Slots.memcpyROSpecWithStack stk) :=
  hookOk_stack_mono4k hh hle hmax

private theorem hookOk_sessionMemmove_of_cliExt4k {f : State → State} {stk : Nat}
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
    hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memmoveSpec, libcMemmoveSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memmoveSpec, withStack, base,
        sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono4k h1 hle hmax
  exact hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemmoveSpec, libcMemmoveSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemmoveSpec, withStack, base,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_libcMemmove_of_session4k {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemmoveSpec stk)) : HookOk f (libcMemmoveSpec stk) :=
  hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemmoveSpec, libcMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionMemset_of_cliExt4k {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memsetSpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemsetSpec stk) := by
  let base : Spec (BitVec 64 × BitVec 8 × Nat) :=
    { pre := fun (ptr, c, len) s0 =>
        ⌜s0.readReg64 .x0 = ptr ∧ (s0.readReg32 .x1).truncate 8 = c ∧
         (s0.readReg64 .x2).toNat = len⌝ ∗ memRegion ptr len
      post := fun (ptr, c, len) s0 sf =>
        ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c) }
  have h1 : HookOk f (withStack base CliExt.memHookStack) :=
    hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memsetSpec, libcMemsetSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memsetSpec, withStack, base,
        sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono4k h1 hle hmax
  exact hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemsetSpec, libcMemsetSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack, base,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_libcMemset_of_session4k {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemsetSpec stk)) : HookOk f (libcMemsetSpec stk) :=
  hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemsetSpec, libcMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionShim_of_cliExt4k {f : State → State}
    (hh : HookOk f CliExt.shimSpec) : HookOk f sessionShimSpec :=
  hookOk_map4k (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem stub_raw_of_hookSat4k {α : Type} (b : BitVec 64)
    {ext : String → Option (State → State)} {fnName hname : String} {spec : Spec α}
    (hlt : libsignalSessionCode.fnOff fnName < 2 ^ 64)
    (hhook : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff?
      (libsignalSessionCode.fnOff fnName) = H hname)
    (hnp : Rust.isPanicSymbol hname = false)
    (hsat : HookSat ext hname spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fnName) spec := by
  have h := hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext)
    (name := fnName) (hname := hname) (stub := libsignalSessionCode.fnOff fnName) (k := 0)
    rfl (Nat.add_zero _) hlt hhook hnp hsat
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

/-- Raw `4096`-byte (`allocHookStack`) allocator + `mem*` + `shim` contract bundle on
`tripleRatchetProgAtExt b ext` (no `img.FrozenLoaded` requirement). -/
structure AllocContracts4K (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A)
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)
  realloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustReallocSpec A)
  shim :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec
  memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (libcMemcpySpec hookStack)
  session_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec hookStack)
  memcpy_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (withStack memcpyRegionSpec hookStack)
  session_memcpy_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack sessionMemcpyRegionSpec hookStack)
  memmove : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (libcMemmoveSpec hookStack)
  session_memmove : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (sessionMemmoveSpec hookStack)
  memset : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (libcMemsetSpec hookStack)
  session_memset : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (sessionMemsetSpec hookStack)

namespace AllocContracts4K

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

theorem alloc_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem dealloc_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  sub_ok_at_of_fnAddr hA.realloc name k hk

theorem shim_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem session_shim_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem memcpy_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (libcMemcpySpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memcpy hookStack hstack hstack_le) name k hk

theorem session_memcpy_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpySpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy hookStack hstack hstack_le) name k hk

theorem memcpy_region_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack memcpyRegionSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memcpy_region hookStack hstack hstack_le) name k hk

theorem session_memcpy_region_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack sessionMemcpyRegionSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region hookStack hstack hstack_le) name k hk

theorem memmove_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (libcMemmoveSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memmove hookStack hstack hstack_le) name k hk

theorem session_memmove_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemmoveSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memmove hookStack hstack hstack_le) name k hk

theorem memset_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (libcMemsetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memset hookStack hstack hstack_le) name k hk

theorem session_memset_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemsetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memset hookStack hstack hstack_le) name k hk

theorem of_AllocContracts (hA : AllocContracts b A ext) : AllocContracts4K b A ext where
  alloc := hA.alloc
  dealloc := hA.dealloc
  realloc := hA.realloc
  shim := hA.shim
  memcpy stk _ _ := hA.memcpy stk
  session_memcpy stk _ _ := hA.session_memcpy stk
  memcpy_region stk _ _ := subroutine_ok_withStack_of_subroutine_ok hA.memcpy_region stk
  session_memcpy_region stk _ _ :=
    subroutine_ok_withStack_of_subroutine_ok hA.session_memcpy_region stk
  memmove stk _ _ := hA.memmove stk
  session_memmove stk _ _ := hA.session_memmove stk
  memset stk hle _ := hA.memset stk (Nat.lt_of_lt_of_le (by decide : 0 < allocHookStack) hle)
  session_memset stk hle _ :=
    hA.session_memset stk (Nat.lt_of_lt_of_le (by decide : 0 < allocHookStack) hle)

theorem of_externsOk_on {P : E2E.PEParams}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (b : BitVec 64) :
    AllocContracts4K b A ext' where
  alloc := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hAg.hookSat (by decide) hOk.alloc.alloc)
  dealloc := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hAg.hookSat (by decide) hOk.alloc.dealloc)
  realloc := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hAg.hookSat (by decide) hOk.alloc.realloc)
  shim := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.shim) fun _ hh =>
      hookOk_sessionShim_of_cliExt4k hh)
  memcpy stk hle hmax := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_libcMemcpy_of_session4k (hookOk_sessionMemcpy_of_cliExt4k hh hle hmax))
  session_memcpy stk hle hmax := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_sessionMemcpy_of_cliExt4k hh hle hmax)
  memcpy_region stk hle hmax := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_memcpyRegion_of_libc4k
        (hookOk_libcMemcpy_of_session4k (hookOk_sessionMemcpy_of_cliExt4k hh hle hmax)))
  session_memcpy_region stk hle hmax := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_sessionMemcpyRegion_of_session4k (hookOk_sessionMemcpy_of_cliExt4k hh hle hmax))
  memmove stk hle hmax := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.memmove) fun _ hh =>
      hookOk_libcMemmove_of_session4k (hookOk_sessionMemmove_of_cliExt4k hh hle hmax))
  session_memmove stk hle hmax := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.memmove) fun _ hh =>
      hookOk_sessionMemmove_of_cliExt4k hh hle hmax)
  memset stk hle hmax := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
      hookOk_libcMemset_of_session4k (hookOk_sessionMemset_of_cliExt4k hh hle hmax))
  session_memset stk hle hmax := stub_raw_of_hookSat4k b (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map4k (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
      hookOk_sessionMemset_of_cliExt4k hh hle hmax)

theorem of_externsOk {P : E2E.PEParams}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    AllocContracts4K b A (SignalSession.cliExternsWith ext) :=
  of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) b

end AllocContracts4K

end CryptoVerification.Cli.LibsignalSpqrV1.M4
