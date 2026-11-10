/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.SpecLemmas.SymtabGhost
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.ObjectLoad

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Symbol-Table Adapter `wrapExtIo` for Placed I/O Hooks

Defines `symtabOnlyImage`, `wrapIoHook`, and `wrapExtIo` so `Obj.Image`-indexed I/O hook contracts
from `CliExternsOk` apply uniformly across relocatable states with arbitrary `s.symtab`.
-/
namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

def symtabOnlyImage (img : Obj.Image) : Obj.Image :=
  { img with code := [], dataAddr := 0#64, data := [], roData := [], gotAddr := 0#64, got := [] }

theorem symtabOnlyImage_symtab (img : Obj.Image) : (symtabOnlyImage img).symtab = img.symtab := rfl

theorem base_align4_of_loads {li : Obj.LinkedImage} {img : Obj.Image} (h : Obj.Loads li img) :
    img.base.toNat % 4 = 0 := by
  have hp := ProofLib.ObjectLoad.Loads.aligned h; unfold Obj.pageSize at hp; omega

theorem symtabOnlyImage_frozenLoaded {img : Obj.Image} (hal : img.base.toNat % 4 = 0) (s : State) :
    (symtabOnlyImage img).FrozenLoaded s := by
  rw [Obj.Image.frozenLoaded_iff]
  refine ⟨Program.CodeLoaded.intro hal
    (by simpa [Program.ofImage, symtabOnlyImage] using Nat.le_of_lt img.base.isLt)
    (fun i hi => by simp [Program.ofImage, symtabOnlyImage] at hi),
    fun i hi => by simp [symtabOnlyImage] at hi,
    by simp [Obj.Image.gotBytes, symtabOnlyImage, Obj.HoldsBytes]⟩

noncomputable def wrapIoHook (img : Obj.Image) (f : State → State) (s : State) : State :=
  letI := Classical.propDecidable
  if s.symtab = img.symtab then f s else (f (s.withSymtab img.symtab)).withSymtab s.symtab

noncomputable def wrapExtIo (img : Obj.Image) (ext : String → Option (State → State))
    (n : String) : Option (State → State) :=
  if n ∈ CliExt.ioNames then (ext n).map (wrapIoHook img) else ext n

theorem wrapIoHook_eq_of_symtab {img : Obj.Image} {f : State → State} {s : State}
    (hs : s.symtab = img.symtab) : wrapIoHook img f s = f s := by
  unfold wrapIoHook; simp [hs]

theorem wrapExtIo_not_io (img : Obj.Image) (ext : String → Option (State → State)) {n : String}
    (h : n ∉ CliExt.ioNames) : wrapExtIo img ext n = ext n := by
  unfold wrapExtIo; simp [h]

theorem wrapExtIo_io (img : Obj.Image) (ext : String → Option (State → State)) {n : String}
    (h : n ∈ CliExt.ioNames) : wrapExtIo img ext n = (ext n).map (wrapIoHook img) := by
  unfold wrapExtIo; simp [h]

theorem wrapExtIo_isSome (img : Obj.Image) (ext : String → Option (State → State)) (n : String) :
    (wrapExtIo img ext n).isSome = (ext n).isSome := by
  unfold wrapExtIo; by_cases h : n ∈ CliExt.ioNames <;> simp [h]

theorem wrapExtIo_tpidr {P : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    ∀ n g, wrapExtIo img ext n = some g → ∀ s, (g s).tpidrEl0 = s.tpidrEl0 := by
  intro n g hg s; unfold wrapExtIo at hg
  by_cases hio : n ∈ CliExt.ioNames
  · simp only [hio, ↓reduceIte, Option.map_eq_some_iff] at hg; obtain ⟨f, hf, rfl⟩ := hg
    unfold wrapIoHook; by_cases hs : s.symtab = img.symtab
    · simp only [hs, ↓reduceIte]; exact hOk.tpidr n f hf s
    · simp only [hs, ↓reduceIte]; exact hOk.tpidr n f hf (s.withSymtab img.symtab)
  · simp only [hio, ↓reduceIte] at hg; exact hOk.tpidr n g hg s

theorem wrapExtIo_noExec {P : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    ∀ n g, wrapExtIo img ext n = some g → ∀ s a, ((g s).mem.perm a).x → (s.mem.perm a).x := by
  intro n g hg s a hx; unfold wrapExtIo at hg
  by_cases hio : n ∈ CliExt.ioNames
  · simp only [hio, ↓reduceIte, Option.map_eq_some_iff] at hg; obtain ⟨f, hf, rfl⟩ := hg
    unfold wrapIoHook at hx; by_cases hs : s.symtab = img.symtab
    · simp only [hs, ↓reduceIte] at hx; exact hOk.noExec n f hf s a hx
    · simp only [hs, ↓reduceIte] at hx; exact hOk.noExec n f hf (s.withSymtab img.symtab) a hx
  · simp only [hio, ↓reduceIte] at hg; exact hOk.noExec n g hg s a hx

theorem wrapExtIo_fsTraced {P : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    ∀ n g, wrapExtIo img ext n = some g → HookFsTraced (fun e => e.isFsChange = true) g := by
  intro n g hg s; unfold wrapExtIo at hg
  by_cases hio : n ∈ CliExt.ioNames
  · simp only [hio, ↓reduceIte, Option.map_eq_some_iff] at hg; obtain ⟨f, hf, rfl⟩ := hg
    unfold wrapIoHook; by_cases hs : s.symtab = img.symtab
    · simp only [hs, ↓reduceIte]; exact hOk.fsTraced n f hf s
    · simp only [hs, ↓reduceIte]; exact hOk.fsTraced n f hf (s.withSymtab img.symtab)
  · simp only [hio, ↓reduceIte] at hg; exact hOk.fsTraced n g hg s

theorem wrapExtIo_fsKept {P : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    ∀ n g, wrapExtIo img ext n = some g → n ∉ CliExt.ioNames → ∀ s, (g s).fs = s.fs := by
  intro n g hg hnio s; rw [wrapExtIo_not_io img ext hnio] at hg; exact hOk.fsKept n g hg hnio s

structure SpecSymtabFree {α : Type} (spec : Spec α) : Prop where
  pre_eq : ∀ x (s : State) t, spec.pre x (s.withSymtab t) = spec.pre x s
  post_eq : ∀ x (s0 sf : State) t0 tf, spec.post x (s0.withSymtab t0) (sf.withSymtab tf) = spec.post x s0 sf
  onPanic_eq : ∀ x (s0 sf : State) t0 tf, spec.onPanic x (s0.withSymtab t0) (sf.withSymtab tf) = spec.onPanic x s0 sf
  onExit_eq : ∀ x c (s0 sf : State) t0 tf, spec.onExit x c (s0.withSymtab t0) (sf.withSymtab tf) = spec.onExit x c s0 sf
  onOom_eq : ∀ x (s0 sf : State) t0 tf, spec.onOom x (s0.withSymtab t0) (sf.withSymtab tf) = spec.onOom x s0 sf

theorem rfl_specSymtabFree {α : Type} (spec : Spec α)
    (h1 : ∀ x s t, spec.pre x (s.withSymtab t) = spec.pre x s := by intros; rfl)
    (h2 : ∀ x s0 sf t0 tf, spec.post x (s0.withSymtab t0) (sf.withSymtab tf) = spec.post x s0 sf := by intros; rfl)
    (h3 : ∀ x s0 sf t0 tf, spec.onPanic x (s0.withSymtab t0) (sf.withSymtab tf) = spec.onPanic x s0 sf := by intros; rfl)
    (h4 : ∀ x c s0 sf t0 tf, spec.onExit x c (s0.withSymtab t0) (sf.withSymtab tf) = spec.onExit x c s0 sf := by intros; rfl)
    (h5 : ∀ x s0 sf t0 tf, spec.onOom x (s0.withSymtab t0) (sf.withSymtab tf) = spec.onOom x s0 sf := by intros; rfl) :
    SpecSymtabFree spec := ⟨h1, h2, h3, h4, h5⟩

private theorem subroutineOutcome_of_withSymtab {α : Type} {spec : Spec α}
    (hsf : SpecSymtabFree spec) {x : α} {R : SepProp} {s0 r : State}
    {τ : String → String → Option (BitVec 64)}
    (hout : SubroutineOutcome spec x R (s0.withSymtab τ) r) :
    SubroutineOutcome spec x R s0 (r.withSymtab s0.symtab) := by
  have shift : ∀ (F : State → State → SepProp),
      (∀ (a b : State) t0 tf, F (a.withSymtab t0) (b.withSymtab tf) = F a b) →
      F (s0.withSymtab τ) r = F s0 (r.withSymtab s0.symtab) :=
    fun F hF => (hF s0 r τ r.symtab).trans (hF s0 r s0.symtab s0.symtab).symm
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hpan, hp⟩ | ⟨c, hex, hp⟩ | ⟨hoom, hp⟩
  · exact Or.inl ⟨hret, hcc, by simpa [State.withSymtab_mem, ← shift _ (hsf.post_eq x)] using hp⟩
  · exact Or.inr (Or.inl ⟨hpan, by simpa [State.withSymtab_mem, ← shift _ (hsf.onPanic_eq x)] using hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex, by simpa [State.withSymtab_mem, ← shift _ (hsf.onExit_eq x c)] using hp⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, by simpa [State.withSymtab_mem, ← shift _ (hsf.onOom_eq x)] using hp⟩))

theorem hookOk_wrapIoHook_of_inImage {α : Type} {img : Obj.Image} {f : State → State}
    {spec : Spec α} (hal : img.base.toNat % 4 = 0) (hsf : SpecSymtabFree spec)
    (hh : HookOk f (spec.inImage (symtabOnlyImage img))) : HookOk (wrapIoHook img f) spec := by
  intro x R s0 hrun hpre hsp
  by_cases hs : s0.symtab = img.symtab
  · have hpre0 : s0.mem ⊨ (spec.inImage (symtabOnlyImage img)).pre x s0 ∗ R := by
      dsimp only [Spec.inImage]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨symtabOnlyImage_frozenLoaded hal s0, hs⟩, hpre⟩
    obtain ⟨hkf, hsym, hout⟩ := hh x R s0 hrun hpre0 hsp
    rw [wrapIoHook_eq_of_symtab hs]; exact ⟨hkf, hsym, hout⟩
  · have hw : wrapIoHook img f s0 = (f (s0.withSymtab img.symtab)).withSymtab s0.symtab := by
      unfold wrapIoHook; simp [hs]
    have hpre1 : (s0.withSymtab img.symtab).mem ⊨
        (spec.inImage (symtabOnlyImage img)).pre x (s0.withSymtab img.symtab) ∗ R := by
      dsimp only [Spec.inImage]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨symtabOnlyImage_frozenLoaded hal _, rfl⟩,
        by rw [State.withSymtab_mem, hsf.pre_eq]; exact hpre⟩
    obtain ⟨hkf, _, hout⟩ := hh x R (s0.withSymtab img.symtab) hrun hpre1 hsp
    rw [hw]; exact ⟨hkf, rfl, subroutineOutcome_of_withSymtab hsf hout⟩

end CryptoVerification.SignalSession.Cli.MainHops
