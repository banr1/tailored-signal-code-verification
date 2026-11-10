/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.StringCloneFlatX
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorFrom
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorPush
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.VarintSlow
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.InImage.Uuid

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed `Stage2ContractsExt` and `Stage2ContractsWeak` from `CliExternsOk`

Derives `AllocContractsX`, `Stage2ContractsWeak`, and the extended `Stage2ContractsExt` bundle on
`tripleRatchetProgAtExt img.base ext'` directly from `CliExternsOk P A ext` for any hook table
`ext'` agreeing with `ext` on `cliHookNames` (`AgreeOnCliHooks`, covering both `cliExternsWith ext`
and `trapUnlisted ext`).
-/

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. `HookOk`/`HookSat` transport, stack monotonicity, and `AgreeOnCliHooks` -/

private theorem hookOk_map {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
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

private theorem hookSat_map {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem hookOk_withStack {α : Type} {f : State → State} {base : Spec α}
    (hh : HookOk f base) (stk : Nat)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withStack base stk) := by
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ base.pre x s0 ∗ (stackAt s0.sp stk ∗ R) := by
    dsimp only [withStack] at hpre
    rwa [sepConj_assoc] at hpre
  obtain ⟨hkf, hsym, hout⟩ := hh x (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack]
    rwa [← sepConj_assoc] at hpost
  · rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he; exact False.elim he.1
  · rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem hookOk_stack_mono {α : Type} {f : State → State} {base : Spec α}
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

private theorem hookOk_sessionMemcpy_of_cliExt {f : State → State} {stk : Nat}
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

private theorem hookOk_libcMemcpy_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemcpySpec stk)) : HookOk f (libcMemcpySpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionMemcpyRegion_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemcpySpec stk)) :
    HookOk f (withStack sessionMemcpyRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_memcpyRegion_of_libc {f : State → State} {stk : Nat}
    (hh : HookOk f (libcMemcpySpec stk)) : HookOk f (withStack memcpyRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

/-- Stack-equipped read-only `memcpy` specification at `hookStack`. -/
def memcpyROSpecWithStack (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  CliExt.withStack
    { pre := fun (dst, src, bs) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
          bs.length ≤ 2 ^ 64⌝ ∗ memRegion dst bs.length ∗ (src ↦ᵣ bs)
      post := fun (dst, src, bs) s0 sf =>
        ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) }
    hookStack

private theorem hookOk_memcpyRO_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpyROSpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (memcpyROSpecWithStack stk) :=
  hookOk_stack_mono hh hle hmax

private theorem hookOk_sessionMemmove_of_cliExt {f : State → State} {stk : Nat}
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

private theorem hookOk_libcMemmove_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemmoveSpec stk)) : HookOk f (libcMemmoveSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemmoveSpec, libcMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionMemset_of_cliExt {f : State → State} {stk : Nat}
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

private theorem hookOk_libcMemset_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemsetSpec stk)) : HookOk f (libcMemsetSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemsetSpec, libcMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionMemsetRegion_of_session {f : State → State} {stk : Nat}
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

private theorem hookOk_memsetRegion_of_libc {f : State → State} {stk : Nat}
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

private theorem hookOk_blackBoxU8_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.blackBoxSpec) :
    HookOk f (withStack blackBoxU8Spec extHookStack) := by
  refine hookOk_map (fun v => v) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp) (fun v _ s0 sf _ _ hq => ?_)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  simp only [CliExt.blackBoxSpec, CliExt.withStack, withStack, blackBoxU8Spec,
    sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨⟨hx0, htr⟩, hstk⟩
  have h8 : (sf.readReg64 .x0).setWidth 8 = v.setWidth 8 := by
    have h1 := congrArg (fun w : BitVec 32 => w.setWidth 8) hx0
    have hlhs : ((sf.readReg64 .x0).setWidth 32).setWidth 8 = (sf.readReg64 .x0).setWidth 8 :=
      BitVec.setWidth_setWidth_of_le (sf.readReg64 .x0) (by decide : 8 ≤ 32)
    have hrhs : ((v.setWidth 8).zeroExtend 32).setWidth 8 = v.setWidth 8 := by
      change ((v.setWidth 8).setWidth 32).setWidth 8 = v.setWidth 8
      rw [BitVec.setWidth_setWidth_of_le (v.setWidth 8) (by decide : 8 ≤ 32), BitVec.setWidth_eq]
    exact hlhs.symm.trans (h1.trans hrhs)
  exact ⟨⟨h8, htr⟩, hstk⟩

/-- Weakens `CliExt.blackBoxSpec` (32-bit) to `withStack blackBoxU8Spec extHookStack` (8-bit). -/
theorem blackBoxU8_of_cliExtBlackBox {prog : Program} {addr : BitVec 64} {img : Obj.Image}
    (h : subroutine_ok prog addr (CliExt.blackBoxSpec.inImage img)) :
    subroutine_ok prog addr ((withStack blackBoxU8Spec extHookStack).inImage img) := by
  refine subroutine_ok_outcome_intro fun v R s0 hpc hrun hpre hal => ?_
  refine h.mono_outcome v R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (⌜(sf.readReg64 .x0).setWidth 32 = (v.setWidth 8).zeroExtend 32 ∧
      sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack) ∗ R at hpost
    change sf.mem ⊨ (⌜(sf.readReg64 .x0).setWidth 8 = v.setWidth 8 ∧
      sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack) ∗ R
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hrest⟩
    have h8 : (sf.readReg64 .x0).setWidth 8 = v.setWidth 8 := by
      have h1 := congrArg (fun w : BitVec 32 => w.setWidth 8) hx0
      have hlhs : ((sf.readReg64 .x0).setWidth 32).setWidth 8 = (sf.readReg64 .x0).setWidth 8 :=
        BitVec.setWidth_setWidth_of_le (sf.readReg64 .x0) (by decide : 8 ≤ 32)
      have hrhs : ((v.setWidth 8).zeroExtend 32).setWidth 8 = v.setWidth 8 := by
        change ((v.setWidth 8).setWidth 32).setWidth 8 = v.setWidth 8
        rw [BitVec.setWidth_setWidth_of_le (v.setWidth 8) (by decide : 8 ≤ 32), BitVec.setWidth_eq]
      exact hlhs.symm.trans (h1.trans hrhs)
    exact ⟨⟨h8, htr⟩, hrest⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem stub_raw_of_hookSat {α : Type} (b : BitVec 64)
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

private theorem stub_inImage_of_hookSat {α : Type} (img : Obj.Image)
    {ext : String → Option (State → State)} {fnName hname : String} {spec : Spec α}
    (hlt : libsignalSessionCode.fnOff fnName < 2 ^ 64)
    (hhook : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff?
      (libsignalSessionCode.fnOff fnName) = H hname)
    (hnp : Rust.isPanicSymbol hname = false)
    (hsat : HookSat ext hname spec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr fnName) (spec.inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (stub_raw_of_hookSat img.base hlt hhook hnp hsat)

private theorem memHookStack_le_of_ext {stk : Nat} (hle : extHookStack ≤ stk) :
    CliExt.memHookStack ≤ stk :=
  Nat.le_trans (by decide : CliExt.memHookStack ≤ extHookStack) hle

/-- Agreement of `ext'` with `ext` on all `cliHookNames` (satisfied by `cliExternsWith ext` and `trapUnlisted ext`). -/
structure AgreeOnCliHooks (ext ext' : String → Option (State → State)) : Prop where
  hook_eq : ∀ n, n ∈ cliHookNames → ext' n = ext n

theorem AgreeOnCliHooks.cliExternsWith (ext : String → Option (State → State)) :
    AgreeOnCliHooks ext (SignalSession.cliExternsWith ext) where
  hook_eq n hn := by
    have hnp : E2E.isImagePanicSymbol n = false := by
      have hall := List.all_eq_true.mp cliHookNames_notPanic n hn
      simpa using hall
    simp [SignalSession.cliExternsWith, hnp]

theorem AgreeOnCliHooks.hookSat {α : Type} {ext ext' : String → Option (State → State)}
    (hAg : AgreeOnCliHooks ext ext') {n : String} {spec : Spec α}
    (hmem : n ∈ cliHookNames) (hs : HookSat ext n spec) :
    HookSat ext' n spec := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, (hAg.hook_eq n hmem).trans hf, hok⟩

/-! ## 2. Unconditional `spqrRecvEmptyAny` from `AllocContractsX` -/

private theorem spqrRecvEmpty_res_shape' (msg : List (BitVec 8)) :
    LibsignalSpqr.spqrRecvEmpty msg = .ok ([], none) ∨
      (msg ≠ [] ∧ ∃ sd, LibsignalSpqr.spqrRecvEmpty msg = .error sd) := by
  unfold LibsignalSpqr.spqrRecvEmpty
  cases hok : LibsignalSpqr.msgPreambleOk msg with
  | true => exact Or.inl rfl
  | false =>
    refine Or.inr ⟨?_, false, rfl⟩
    intro hnil
    subst hnil
    simp [LibsignalSpqr.msgPreambleOk, LibsignalSpqr.msgPreamble?] at hok

private theorem memcpy_recv_ok_at_of_allocX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
        bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (InImage.SpqrRecvEmpty.memcpyRecvPcsSpecS.inImage img) := by
  have hmc := hA.session_memcpy_ok_at spqrRecvName
    (num% (ls_off% "memcpy" - ls_off% "spqr::recv"))
  refine subroutine_ok_outcome_intro fun ⟨t, c, i⟩ R s0 hpc hrun hpre hal => ?_
  change s0.mem ⊨ (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
    (InImage.SpqrRecvEmpty.memcpyRecvPcsSpec.pre (t, c, i) s0 ∗ stackAt s0.sp extHookStack)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, hpre1⟩
  simp only [InImage.SpqrRecvEmpty.memcpyRecvPcsSpec] at hpre1
  rw [← InImage.SpqrRecvEmpty.pcs_src] at hpre1
  have h2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (InImage.SpqrRecvEmpty.bytes_of_pcs _ c i))))) hpre1
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  have h3' : s0.mem ⊨ ⌜(s0.readReg64 .x0 = t - 4960#64 ∧ s0.readReg64 .x1 = t - 3024#64 ∧
      s0.readReg64 .x2 = 320#64) ∧
      (bs.length = 320 ∧ ∃ b1 b3 b5 : List (BitVec 8),
        b1.length = 16 ∧ b3.length = 72 ∧ b5.length = 216 ∧
        bs = b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))⌝ ∗
      (memRegion (t - 4960#64) 320 ∗ ((t - 3024#64) ↦ₛ bs) ∗
        stackAt s0.sp extHookStack ∗ R) := by
    have htmp : s0.mem ⊨ ⌜s0.readReg64 .x0 = t - 4960#64 ∧ s0.readReg64 .x1 = t - 3024#64 ∧
        s0.readReg64 .x2 = 320#64⌝ ∗
        (⌜bs.length = 320 ∧ ∃ b1 b3 b5 : List (BitVec 8),
          b1.length = 16 ∧ b3.length = 72 ∧ b5.length = 216 ∧
          bs = b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))⌝ ∗
        (memRegion (t - 4960#64) 320 ∗ ((t - 3024#64) ↦ₛ bs) ∗
          stackAt s0.sp extHookStack ∗ R)) := by
      ac_nf at h3 ⊢
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at htmp
    rw [satisfies_pure_sepConj]
    exact ⟨⟨htmp.1, htmp.2.1⟩, htmp.2.2⟩
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨⟨hx0, hx1, hx2⟩, hlen, b1, b3, b5, hb1, hb3, hb5, rfl⟩, hmem0⟩
  have hx2' : (s0.readReg64 .x2).toNat = 320 := by
    rw [hx2]; rfl
  have hmc_pre : s0.mem ⊨ ((sessionMemcpySpec extHookStack).inImage img).pre
      (t - 4960#64, t - 3024#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R := by
    change s0.mem ⊨ (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = t - 4960#64 ∧ s0.readReg64 .x1 = t - 3024#64 ∧
        (s0.readReg64 .x2).toNat = (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))).length⌝ ∗
        memRegion (t - 4960#64) (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))).length ∗
        ((t - 3024#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗
        stackAt s0.sp extHookStack)) ∗ R
    rw [hlen]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨himg0, ⟨hx0, hx1, hx2'⟩, hmem0⟩
  refine hmc.mono_outcome
    (t - 4960#64, t - 3024#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))
    R s0 hpc hrun hmc_pre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (⌜sf.readReg64 .x0 = t - 4960#64 ∧ sf.trace = s0.trace⌝ ∗
      ((t - 4960#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗
      ((t - 3024#64) ↦ₛ (b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))) ∗
      stackAt s0.sp extHookStack) ∗ R at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hfx0, htr⟩, hpost_mem⟩
    simp only [sepConj_assoc] at hpost_mem
    have hw := Satisfies.mono
      (sepConj_mono (InImage.SpqrRecvEmpty.pcs_of_bytes _ c i b1 b3 b5 hb1 hb3 hb5)
        (sepConj_mono_left (InImage.SpqrRecvEmpty.pcs_of_bytes _ c i b1 b3 b5 hb1 hb3 hb5)))
      hpost_mem
    change sf.mem ⊨ (InImage.SpqrRecvEmpty.memcpyRecvPcsSpec.post (t, c, i) s0 sf ∗
      stackAt s0.sp extHookStack) ∗ R
    simp only [InImage.SpqrRecvEmpty.memcpyRecvPcsSpec]
    rw [← InImage.SpqrRecvEmpty.pcs_src, ← InImage.SpqrRecvEmpty.pcs_dst]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, hfx0⟩, hw⟩
  · change sf.mem ⊨ ⌜False⌝ ∗ _ at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · change sf.mem ⊨ ⌜False⌝ ∗ _ at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ _ at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- `spqr::recv` on an empty state satisfies `(spqrRecvEmptyAnySpec A).inImage img` from `AllocContractsX`. -/
theorem spqrRecvEmptyAny_ok_of_allocX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      ((spqrRecvEmptyAnySpec A).inImage img) := by
  let S0 : SpqrModel :=
    { send := fun _ _ => some ([], none, [])
      draws := fun _ _ => 0
      recv := fun _ msg => LibsignalSpqr.spqrRecvEmpty msg
      recvPanics := fun _ _ => false
      sendPanics := fun _ _ => false }
  have hE0 : S0.RecvEmptyOk := { recv := fun _ => rfl, noPanic := fun _ => nofun }
  have hbase := InImage.SpqrRecvEmpty.spqrRecvEmpty_base_F0 img.base (Rust.withPanics ext)
    A S0 img emp hE0 (memcpy_recv_ok_at_of_allocX hA)
  refine subroutine_ok_outcome_intro fun ⟨st, msg, ret⟩ R s0 hpc hrun hpre hal => ?_
  have hpre0 : s0.mem ⊨ (InImage.SpqrRecvEmpty.spqrRecvEmptyCodeSpec0 A S0 img emp).pre
      (st, msg, ret) s0 ∗ R := by
    dsimp only [spqrRecvEmptyAnySpec, InImage.SpqrRecvEmpty.spqrRecvEmptyCodeSpec0,
      InImage.SpqrRecvEmpty.spqrRecvCodeSpec0, Spec.inImage] at hpre ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨himg0, ⟨hx0, hx1, hx8, hst⟩, hrest⟩
    exact ⟨hst, himg0, ⟨hx0, hx1, hx8⟩, hrest⟩
  refine hbase.mono_outcome (st, msg, ret) R s0 hpc hrun hpre0 hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan1, hpan2⟩ | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [InImage.SpqrRecvEmpty.spqrRecvEmptyCodeSpec0,
      InImage.SpqrRecvEmpty.spqrRecvCodeSpec0, spqrRecvEmptyAnySpec, Spec.inImage,
      S0] at hpost ⊢
    rw [emp_sepConj] at hpost
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
    refine Entails.sepExists_right (LibsignalSpqr.spqrRecvEmpty msg.bytes) ?_
    exact Entails.pure_right (spqrRecvEmpty_res_shape' msg.bytes) (Entails.refl _)
  · refine Or.inr (Or.inl ⟨hpan1, ?_⟩)
    dsimp only [InImage.SpqrRecvEmpty.spqrRecvEmptyCodeSpec0,
      InImage.SpqrRecvEmpty.spqrRecvCodeSpec0, spqrRecvEmptyAnySpec, Spec.inImage,
      S0] at hpan2 ⊢
    simp only [Bool.false_eq_true, or_false] at hpan2
    exact hpan2
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-! ## 3. `AllocContractsX`, `Stage2ContractsWeak`, and `Stage2ContractsExt` -/

theorem allocContractsX_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (img : Obj.Image) :
    AllocContractsX img A ext' where
  alloc := subroutine_ok_inImage_of_subroutine_ok img
    (rustAllocWithStack_of_rustAlloc
      (stub_raw_of_hookSat img.base (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
        (hAg.hookSat (by decide) hOk.alloc.alloc)))
  dealloc := subroutine_ok_inImage_of_subroutine_ok img
    (rustDeallocExternWithStack_of_rustDealloc
      (stub_raw_of_hookSat img.base (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
        (hAg.hookSat (by decide) hOk.alloc.dealloc)))
  realloc := subroutine_ok_inImage_of_subroutine_ok img
    (rustReallocExternWithStack_of_rustRealloc
      (stub_raw_of_hookSat img.base (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
        (hAg.hookSat (by decide) hOk.alloc.realloc)))
  shim stk _ _ := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.shim) fun _ hh =>
      hookOk_withStack hh stk)
  memcpy stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_libcMemcpy_of_session (hookOk_sessionMemcpy_of_cliExt hh (memHookStack_le_of_ext hle) hmax))
  session_memcpy stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_sessionMemcpy_of_cliExt hh (memHookStack_le_of_ext hle) hmax)
  memcpy_region stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_memcpyRegion_of_libc
        (hookOk_libcMemcpy_of_session (hookOk_sessionMemcpy_of_cliExt hh (memHookStack_le_of_ext hle) hmax)))
  session_memcpy_region stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_sessionMemcpyRegion_of_session (hookOk_sessionMemcpy_of_cliExt hh (memHookStack_le_of_ext hle) hmax))
  memmove stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memmove) fun _ hh =>
      hookOk_libcMemmove_of_session (hookOk_sessionMemmove_of_cliExt hh (memHookStack_le_of_ext hle) hmax))
  session_memmove stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memmove) fun _ hh =>
      hookOk_sessionMemmove_of_cliExt hh (memHookStack_le_of_ext hle) hmax)
  memset stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
      hookOk_libcMemset_of_session (hookOk_sessionMemset_of_cliExt hh (memHookStack_le_of_ext hle) hmax))
  session_memset stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
      hookOk_sessionMemset_of_cliExt hh (memHookStack_le_of_ext hle) hmax)
  memset_region stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
      hookOk_memsetRegion_of_libc
        (hookOk_libcMemset_of_session (hookOk_sessionMemset_of_cliExt hh (memHookStack_le_of_ext hle) hmax)))
  session_memset_region stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
      hookOk_sessionMemsetRegion_of_session (hookOk_sessionMemset_of_cliExt hh (memHookStack_le_of_ext hle) hmax))

theorem allocContractsX_cliExternsWith_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    AllocContractsX img A (cliExternsWith ext) :=
  allocContractsX_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img

/-- `Stage2ContractsWeak` on any `ext'` satisfying `AgreeOnCliHooks ext ext'`, from `CliExternsOk P A ext`. -/
theorem stage2ContractsWeak_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (img : Obj.Image) :
    Stage2ContractsWeak img P.C A ext' :=
  let hA := allocContractsX_of_externsOk_on hOk hAg img
  { toAllocContractsX := hA
    black_box := stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
      (hookSat_map (hAg.hookSat (by decide) hOk.blackBox) fun _ hh =>
        hookOk_blackBoxU8_of_cliExt hh)
    compress256 := stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
      (hAg.hookSat (by decide) hOk.compress256)
    dh := stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, dhName])
      (hAg.hookSat (by decide) hOk.dh)
    pub_from_secret := stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, pubFromSecretName])
      (hAg.hookSat (by decide) hOk.pubFromSecret)
    static_drop := stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, staticDropName])
      (hAg.hookSat (by decide) hOk.staticDrop)
    shared_drop := stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, sharedDropName])
      (hAg.hookSat (by decide) hOk.sharedDrop)
    uuid_try_parse := subroutine_ok_inImage_of_subroutine_ok img
      (uuidTryParseAnyWithStack_of_code (uuidTryParse_ok_F img.base (Rust.withPanics ext')))
    decode_varint_slow := RunProofs.SigTryFromHelpers.decodeVarintSlow_ok_ext_x hA
    aes_enc := by
      rw [aesEncFnSpec_block_eq]
      exact stub_inImage_of_hookSat img (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, aesEncName])
        (hAg.hookSat (by decide) hOk.aesEnc)
    aes_dec := subroutine_ok_inImage_of_subroutine_ok img
      (aesDecWeak_of_aesDec
        (stub_raw_of_hookSat img.base (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, aesDecName])
          (hAg.hookSat (by decide) hOk.aesDec)))
    spqr_recv := spqrRecvEmptyAny_ok_of_allocX hA
    format_inner := stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, formatInnerName])
      (hAg.hookSat (by decide) hOk.formatInner)
    fmt_write := stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, fmtWriteName])
      (hAg.hookSat (by decide) hOk.fmtWrite)
    decode_error_from := RunProofs.SigTryFromHelpers.decodeErrorFrom_ok_ext_x hA
    decode_error_push := RunProofs.SigTryFromHelpers.decodeErrorPush_ok_ext_x hA }

theorem stage2ContractsWeak_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    Stage2ContractsWeak img P.C A (cliExternsWith ext) :=
  stage2ContractsWeak_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img

/-- Extended Stage-2 contract bundle adding 32-bit `black_box`, `uuid_try_parse_code`,
`decode_state_empty`, `alloc_zeroed`, `aes_dec_exact`, 4096-byte-floored `mem*` contracts, `bcmp`,
`string_clone`, `duration_since`, and `time_add` to `Stage2ContractsWeak`. -/
structure Stage2ContractsExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop extends
    Stage2ContractsWeak img C A ext where
  black_box32 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      (CliExt.blackBoxSpec.inImage img)
  uuid_try_parse_code :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName)
      ((uuidTryParseCodeSpec uuidTryParse).inImage img)
  decode_state_empty :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeStateName)
      (decodeStateEmptySpec A)
  alloc_zeroed :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocZeroedName)
      ((rustAllocZeroedSpec A).inImage img)
  aes_dec_exact :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr aesDecName)
      ((aesDecSpec C.D A).inImage img)
  memcpy_ro : ∀ (hookStack : Nat), CliExt.memHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((memcpyROSpecWithStack hookStack).inImage img)
  memcpy_mem : ∀ (hookStack : Nat), CliExt.memHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((libcMemcpySpec hookStack).inImage img)
  session_memcpy_mem : ∀ (hookStack : Nat), CliExt.memHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((sessionMemcpySpec hookStack).inImage img)
  memmove_mem : ∀ (hookStack : Nat), CliExt.memHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memmoveName)
      ((libcMemmoveSpec hookStack).inImage img)
  session_memmove_mem : ∀ (hookStack : Nat), CliExt.memHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memmoveName)
      ((sessionMemmoveSpec hookStack).inImage img)
  memset_mem : ∀ (hookStack : Nat), CliExt.memHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memsetName)
      ((libcMemsetSpec hookStack).inImage img)
  session_memset_mem : ∀ (hookStack : Nat), CliExt.memHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memsetName)
      ((sessionMemsetSpec hookStack).inImage img)
  bcmp :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr E2E.bcmpName)
      (CliExt.bcmpSpec.inImage img)
  e2e_bcmp :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr E2E.bcmpName)
      (E2E.HooksE.e2eBcmpSpec.inImage img)
  string_clone :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr stringCloneHookName)
      ((stringCloneSpec A).inImage img)
  duration_since :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr durationSinceHookName)
      (CliExt.durationSinceEpochSpec.inImage img)
  time_add :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr timeAddHookName)
      (timeAddSpec.inImage img)

namespace Stage2ContractsExt

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ext : String → Option (State → State)}

theorem black_box32_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff blackBoxName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (CliExt.blackBoxSpec.inImage img) :=
  sub_ok_at_of_fnAddr hC.black_box32 name k hk

theorem uuid_try_parse_code_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((uuidTryParseCodeSpec uuidTryParse).inImage img) :=
  sub_ok_at_of_fnAddr hC.uuid_try_parse_code name k hk

theorem decode_state_empty_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeStateName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (decodeStateEmptySpec A) :=
  sub_ok_at_of_fnAddr hC.decode_state_empty name k hk

theorem alloc_zeroed_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocZeroedName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustAllocZeroedSpec A).inImage img) :=
  sub_ok_at_of_fnAddr hC.alloc_zeroed name k hk

theorem aes_dec_exact_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesDecName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((aesDecSpec C.D A).inImage img) :=
  sub_ok_at_of_fnAddr hC.aes_dec_exact name k hk

theorem memcpy_ro_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm])
    (hookStack : Nat) (hle : CliExt.memHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((memcpyROSpecWithStack hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hC.memcpy_ro hookStack hle hmax) name k hk

theorem memcpy_mem_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm])
    (hookStack : Nat) (hle : CliExt.memHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemcpySpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hC.memcpy_mem hookStack hle hmax) name k hk

theorem session_memcpy_mem_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm])
    (hookStack : Nat) (hle : CliExt.memHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemcpySpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hC.session_memcpy_mem hookStack hle hmax) name k hk

theorem memmove_mem_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm])
    (hookStack : Nat) (hle : CliExt.memHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemmoveSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hC.memmove_mem hookStack hle hmax) name k hk

theorem session_memmove_mem_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm])
    (hookStack : Nat) (hle : CliExt.memHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemmoveSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hC.session_memmove_mem hookStack hle hmax) name k hk

theorem memset_mem_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm])
    (hookStack : Nat) (hle : CliExt.memHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemsetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hC.memset_mem hookStack hle hmax) name k hk

theorem session_memset_mem_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm])
    (hookStack : Nat) (hle : CliExt.memHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemsetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hC.session_memset_mem hookStack hle hmax) name k hk

theorem bcmp_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff E2E.bcmpName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (CliExt.bcmpSpec.inImage img) :=
  sub_ok_at_of_fnAddr hC.bcmp name k hk

theorem e2e_bcmp_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff E2E.bcmpName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (E2E.HooksE.e2eBcmpSpec.inImage img) :=
  sub_ok_at_of_fnAddr hC.e2e_bcmp name k hk

theorem string_clone_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff stringCloneHookName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((stringCloneSpec A).inImage img) :=
  sub_ok_at_of_fnAddr hC.string_clone name k hk

theorem duration_since_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff durationSinceHookName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (CliExt.durationSinceEpochSpec.inImage img) :=
  sub_ok_at_of_fnAddr hC.duration_since name k hk

theorem time_add_ok_at (hC : Stage2ContractsExt img C A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff timeAddHookName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (timeAddSpec.inImage img) :=
  sub_ok_at_of_fnAddr hC.time_add name k hk

theorem of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (img : Obj.Image) :
    Stage2ContractsExt img P.C A ext' where
  toStage2ContractsX := stage2ContractsWeak_of_externsOk_on hOk hAg img
  black_box32 := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hAg.hookSat (by decide) hOk.blackBox)
  uuid_try_parse_code := subroutine_ok_inImage_of_subroutine_ok img
    (uuidTryParse_ok_F img.base (Rust.withPanics ext'))
  decode_state_empty := InImage.DecodeStateEmpty.decodeStateEmpty_ok_F img.base (Rust.withPanics ext') A
  alloc_zeroed := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, allocZeroedName])
    (hAg.hookSat (by decide) hOk.allocZeroed)
  aes_dec_exact := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, aesDecName])
    (hAg.hookSat (by decide) hOk.aesDec)
  memcpy_ro stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memcpyRO) fun _ hh =>
      hookOk_memcpyRO_of_cliExt hh hle hmax)
  memcpy_mem stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_libcMemcpy_of_session (hookOk_sessionMemcpy_of_cliExt hh hle hmax))
  session_memcpy_mem stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
      hookOk_sessionMemcpy_of_cliExt hh hle hmax)
  memmove_mem stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memmove) fun _ hh =>
      hookOk_libcMemmove_of_session (hookOk_sessionMemmove_of_cliExt hh hle hmax))
  session_memmove_mem stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memmove) fun _ hh =>
      hookOk_sessionMemmove_of_cliExt hh hle hmax)
  memset_mem stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
      hookOk_libcMemset_of_session (hookOk_sessionMemset_of_cliExt hh hle hmax))
  session_memset_mem stk hle hmax := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
      hookOk_sessionMemset_of_cliExt hh hle hmax)
  bcmp := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hAg.hookSat (by decide) hOk.bcmp)
  e2e_bcmp := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    (hookSat_map (hAg.hookSat (by decide) hOk.bcmp) fun _ hh =>
      hookOk_map (s₁ := CliExt.bcmpSpec)
        (fun x => ⟨x.a, false, x.bsA, x.b, false, x.bsB⟩)
        (fun _ _ => True) (fun _ => trivial) hh
        (fun _ _ _ hp => by simpa only [CliExt.bcmpSpec, E2E.HooksE.e2eBcmpSpec, CliExt.bytesAt,
          Bool.false_eq_true, ↓reduceIte] using hp)
        (fun _ _ _ _ _ _ hq => by simpa only [CliExt.bcmpSpec, E2E.HooksE.e2eBcmpSpec, CliExt.bytesAt,
          Bool.false_eq_true, ↓reduceIte] using hq)
        (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq))
  string_clone := LibsignalBinary.Proofs.Common.StringCloneFlatX.stringClone_inImage_4k_ok A
    (stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
      (hookSat_map (hAg.hookSat (by decide) hOk.shim) fun _ hh =>
        hookOk_withStack hh allocHookStack))
    (subroutine_ok_inImage_of_subroutine_ok img
      (stub_raw_of_hookSat img.base (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
        (hAg.hookSat (by decide) hOk.alloc.alloc)))
    (stub_inImage_of_hookSat img (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
      (hookSat_map (hAg.hookSat (by decide) hOk.memcpy) fun _ hh =>
        hookOk_sessionMemcpyRegion_of_session
          (hookOk_sessionMemcpy_of_cliExt hh (by decide) (by decide))))
  duration_since := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, durationSinceHookName])
    (hAg.hookSat (by decide) hOk.durationSince)
  time_add := stub_inImage_of_hookSat img (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, timeAddHookName])
    (hAg.hookSat (by decide) hOk.timeAdd)

/-- Constructs `Stage2ContractsExt` on `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    Stage2ContractsExt img P.C A (cliExternsWith ext) :=
  of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) img

end Stage2ContractsExt

end CryptoVerification.SignalSession.Cli.Slots
