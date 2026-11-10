/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees

/-!
# Filesystem and Stack Framing for Hook Contracts (`Spec.keepsFs`)

Lifts `HookOk` contracts to `Spec.keepsFs` (`sf.fs = s0.fs`) and stack-framed allocator specs
(`withStack`, `rustAllocSpecWithStack`, `rustDeallocExternSpecWithStack`,
`rustReallocExternSpecWithStack`) for `allocHookStack ≤ stk ≤ 2 ^ 64`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- A hook that satisfies `spec` and preserves `fs` satisfies `spec.keepsFs`. -/
theorem _root_.Arm64.HookOk.keepsFs {α : Type} {h : State → State} {spec : Spec α}
    (hh : HookOk h spec) (hfs : ∀ s, (h s).fs = s.fs) : HookOk h spec.keepsFs := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hh x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfs s0, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- `retHook f` keeps `fs` when `f` does (`setPC` does not touch `fs`). -/
theorem retHook_fs {f : State → State} (hf : ∀ s, (f s).fs = s.fs) :
    ∀ s, (retHook f s).fs = s.fs := by
  intro s
  simp only [retHook, State.fs_setPC, hf]

/-- `keepsFs` (post) and `Spec.inImage` (pre) touch disjoint fields, so they commute. -/
theorem Spec.keepsFs_inImage {α : Type} (spec : Spec α) (img : Obj.Image) :
    (spec.keepsFs).inImage img = (spec.inImage img).keepsFs := rfl

/-- A hook that satisfies `spec` (with `⌜False⌝` panic, exit, and OOM outcomes) satisfies
`withStack spec stk` by framing `stackAt s0.sp stk`. -/
theorem hookOk_withStack {α : Type} {h : State → State} {spec : Spec α}
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

/-- `HookOk` form of `rustAllocWithStack_of_rustAlloc`: a hook meeting `rustAllocSpec A` meets
`rustAllocSpecWithStack A stk` for `allocHookStack ≤ stk ≤ 2^64`. -/
theorem hookOk_rustAllocWithStack {h : State → State} {A : RustAlloc} {stk : Nat}
    (hh : HookOk h (rustAllocSpec A))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
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
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocSpecWithStack, rustAllocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustAllocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustAllocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustAllocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- `HookOk` form of `rustDeallocExternWithStack_of_rustDealloc`: a hook meeting
`rustDeallocSpec A` meets `rustDeallocExternSpecWithStack A stk` (its extra `LayoutOk` is
dropped) for `allocHookStack ≤ stk ≤ 2^64`. -/
theorem hookOk_rustDeallocExternWithStack {h : State → State} {A : RustAlloc} {stk : Nat}
    (hh : HookOk h (rustDeallocSpec A))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
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
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustDeallocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustDeallocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustDeallocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- `HookOk` form of `rustReallocExternWithStack_of_rustRealloc`: a hook meeting
`rustReallocSpec A` meets `rustReallocExternSpecWithStack A stk` (its extra `LayoutOk old align`
is dropped) for `allocHookStack ≤ stk ≤ 2^64`. -/
theorem hookOk_rustReallocExternWithStack {h : State → State} {A : RustAlloc} {stk : Nat}
    (hh : HookOk h (rustReallocSpec A))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
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
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustReallocExternSpecWithStack, rustReallocSpecWithStack, rustReallocSpec, R']
      at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustReallocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustReallocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustReallocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

end CryptoVerification.SignalSession.Cli.MainHops
