/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Top
public import CaseStudies.Hashbrown.Proofs.StdCli.Shims
public import CaseStudies.Hashbrown.Proofs.StdCli.MemOps
public import ProofLib.SepLogic.WPFrozen

/-!
# Placement-Generic `hashbrownLib` Bridge for `hashbrown_cli`

Wires the five external symbols of `hashbrownLib` (`MultiPlacedLib`) to the Rust allocator shims
and `musl` memory routines in `C : HbCliLayout`, discharges `HbMultiExterns`, and lifts the ten
verified `hashbrown_*` exports onto `subroutine_ok P`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

set_option maxRecDepth 200000 in
private theorem hbBlockPlacement_ρ_extern (mpl : Obj.MultiPlacement) (i : Nat) {sym : String}
    (hlook : Obj.lookupBlockSym sym hashbrownLib.blocks = none := by decide) :
    (hashbrownLib.blockPlacement mpl i).ρ sym = mpl.ρ sym := by
  simp [MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hlook]

/-- `CodeLoaded` invariant for `hashbrown_cli`: `P` and all blocks of `hashbrownLib` at `C.hbMpl`. -/
def hbCliCodeInv (P : Program) (C : HbCliLayout) (m : Memory) : Prop :=
  P.CodeLoaded m ∧ hashbrownLib.CodeLoaded C.hbMpl m

theorem hbCliCodeInv_keepsFrozen {P : Program} {C : HbCliLayout} {m1 m2 : Memory}
    (hkf : m1.KeepsFrozen m2) (h : hbCliCodeInv P C m1) : hbCliCodeInv P C m2 :=
  ⟨h.1.of_keepsFrozen hkf, h.2.of_keepsFrozen hkf⟩

/-- Extern symbol equations linking `C.hbMpl.ρ` to the Rust shim and `musl` addresses in `C`. -/
structure HbExternWiring (C : HbCliLayout) : Prop where
  allocShim_eq : C.hbMpl.ρ hbAllocShimSym = C.rustAllocShimAddr
  alloc_eq     : C.hbMpl.ρ hbAllocSym = C.rustAllocAddr
  dealloc_eq   : C.hbMpl.ρ hbDeallocSym = C.rustDeallocAddr
  memset_eq    : C.hbMpl.ρ hbMemsetSym = C.std.memsetAddr
  memmove_eq   : C.hbMpl.ρ hbMemmoveSym = C.memmoveAddr

set_option maxRecDepth 200000 in
theorem hbCliMultiExterns_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hw : HbExternWiring C)
    (hP_ext : ∀ pc, P.externAt? pc = none) (hP_svc : P.svc = Syscall.standard)
    (hShims : HbShimsCode P C) (hMem : HbMemOpsCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (hCodeP : ∀ {m : Memory}, CodeInv m → P.CodeLoaded m) :
    let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
    HbMultiExterns C.hbMpl (fun _ => none) A := by
  intro A i _hi
  have hCode : ∀ {m : Memory}, A.CodeInv m → P.CodeLoaded m := hCodeP
  have h1 : (hashbrownLib.blockPlacement C.hbMpl i).ρ hbAllocShimSym = C.rustAllocShimAddr :=
    (hbBlockPlacement_ρ_extern C.hbMpl i).trans hw.allocShim_eq
  have h2 : (hashbrownLib.blockPlacement C.hbMpl i).ρ hbAllocSym = C.rustAllocAddr :=
    (hbBlockPlacement_ρ_extern C.hbMpl i).trans hw.alloc_eq
  have h3 : (hashbrownLib.blockPlacement C.hbMpl i).ρ hbDeallocSym = C.rustDeallocAddr :=
    (hbBlockPlacement_ρ_extern C.hbMpl i).trans hw.dealloc_eq
  have h4 : (hashbrownLib.blockPlacement C.hbMpl i).ρ hbMemsetSym = C.std.memsetAddr :=
    (hbBlockPlacement_ρ_extern C.hbMpl i).trans hw.memset_eq
  have h5 : (hashbrownLib.blockPlacement C.hbMpl i).ρ hbMemmoveSym = C.memmoveAddr :=
    (hbBlockPlacement_ρ_extern C.hbMpl i).trans hw.memmove_eq
  refine
    { allocShim_ok := h1 ▸ subroutine_ok_hbBlockDirect hCode hP_ext hP_svc (rustAllocShim_ok hShims)
      alloc_ok     := h2 ▸ subroutine_ok_hbBlockDirect hCode hP_ext hP_svc
                        (rustAlloc_ok hShims M γ CodeInv hCodeInv)
      dealloc_ok   := h3 ▸ subroutine_ok_hbBlockDirect hCode hP_ext hP_svc
                        (rustDealloc_ok hShims M γ CodeInv hCodeInv)
      memset_ok    := h4 ▸ subroutine_ok_hbBlockDirect hCode hP_ext hP_svc (hbMemset_ok hMem)
      memmove_ok   := h5 ▸ subroutine_ok_hbBlockDirect hCode hP_ext hP_svc (hbMemmove_disjoint_ok hMem)
      panic_hooks  := fun hao => False.elim hao }

/-- Lift `hashbrownLib.subroutineOk` onto a hook-free `Syscall.standard` program `P` whenever
    `(A mpl).CodeInv` entails `hashbrownLib.CodeLoaded mpl`. -/
theorem subroutine_ok_cli_of_hbSubroutineOk {α : Type} {P : Program} {mpl : Obj.MultiPlacement}
    {fnName : String} {A : Obj.MultiPlacement → HbAlloc} {spec : Obj.MultiPlacement → Spec α}
    (hPlaceable : hashbrownLib.Placeable mpl)
    (hP_ext : ∀ pc, P.externAt? pc = none) (hP_svc : P.svc = Syscall.standard)
    (hCodeHb : ∀ {m : Memory}, (A mpl).CodeInv m → hashbrownLib.CodeLoaded mpl m)
    (hsub : hashbrownLib.subroutineOk fnName (fun m => withCodeInv (A m) (spec m)) (fun _ => none)) :
    subroutine_ok P (hashbrownLib.fnAddr mpl fnName) (withCodeInv (A mpl) (spec mpl)) := by
  obtain ⟨_hexp, i, off, hlook, hok_all⟩ := hsub
  obtain ⟨hi, _⟩ := Obj.lookupBlockSym_some hlook
  have hok_blk := hok_all mpl hPlaceable
  refine subroutine_ok_of_steps_outcome fun x R s0 hpc hrun hpre hsp _ => ?_
  have hci : (A mpl).CodeInv s0.mem := by
    dsimp only [withCodeInv] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1
  have hCL : hashbrownLib.CodeLoaded mpl s0.mem := hCodeHb hci
  have hpre_wcl : s0.mem ⊨
      (hashbrownLib.withCodeLoaded mpl (withCodeInv (A mpl) (spec mpl))).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec]
    exact Satisfies.mono
      (Entails.trans
        (Entails.pure_right hCL (Entails.refl _))
        (by sep_entail)) hpre
  obtain ⟨sf, hsteps_hb, hout⟩ :=
    subroutine_ok_elim_steps_outcome hok_blk x R s0 hpc hrun hpre_wcl hsp (hCL i hi)
  refine ⟨sf, Steps.of_sameHooks
    (fun pc => by rw [MultiPlacedLib.externAt?_blockProgram_none, hP_ext pc])
    (by simp [MultiPlacedLib.blockProgram, PlacedLib.program, hP_svc]) hsteps_hb, hout⟩

/-- All ten verified `hashbrown` subroutines invoked by `hashbrown_cli::main`, lifted onto `P`. -/
structure HbCliLibContracts (P : Program) (C : HbCliLayout) (A : HbAlloc) : Prop where
  new_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_new")
      (withCodeInv A (hashbrownNewSpec C.hbPl A))
  with_capacity_infallible_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_with_capacity")
      (withCodeInv A (hashbrownWithCapacityInfallibleSpec C.hbPl A))
  insert_infallible_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_insert")
      (withCodeInv A (hashbrownInsertInfallibleSpec C.hbPl A))
  get_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_get")
      (withCodeInv A (hashbrownGetSpec C.hbPl A))
  contains_key_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_contains_key")
      (withCodeInv A (hashbrownContainsKeySpec C.hbPl A))
  remove_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_remove")
      (withCodeInv A (hashbrownRemoveSpec C.hbPl A))
  len_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_len")
      (withCodeInv A (hashbrownLenSpec C.hbPl A))
  is_empty_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_is_empty")
      (withCodeInv A (hashbrownIsEmptySpec C.hbPl A))
  clear_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_clear")
      (withCodeInv A (hashbrownClearSpec C.hbPl A))
  drop_ok :
    subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_drop")
      (withCodeInv A (hashbrownDropSpec C.hbPl A))

open Classical in
theorem hbCliLibContracts_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hw : HbExternWiring C)
    (hPlaceable : hashbrownLib.Placeable C.hbMpl)
    (hP_ext : ∀ pc, P.externAt? pc = none) (hP_svc : P.svc = Syscall.standard)
    (hShims : HbShimsCode P C) (hMem : HbMemOpsCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (hCode : ∀ {m : Memory}, CodeInv m → P.CodeLoaded m ∧ hashbrownLib.CodeLoaded C.hbMpl m) :
    HbCliLibContracts P C (HbAlloc.ofMallocng M γ CodeInv hCodeInv) := by
  let A0 := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  let Afam : Obj.MultiPlacement → HbAlloc := fun mpl =>
    if h : mpl = C.hbMpl then A0
    else HbAlloc.ofMallocng M γ (fun _ => False) (fun _ hf => hf)
  have hAfam_eq : Afam C.hbMpl = A0 := by simp [Afam]
  have hext_all : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl (fun _ => none) (Afam mpl) := by
    intro mpl _hpl
    by_cases h : mpl = C.hbMpl
    · subst h
      rw [hAfam_eq]
      exact hbCliMultiExterns_ok hw hP_ext hP_svc hShims hMem M γ CodeInv hCodeInv
        (fun hci => (hCode hci).1)
    · have hAf : (Afam mpl).allowOom = False ∧ ∀ m, (Afam mpl).CodeInv m → False := by
        simp [Afam, h, HbAlloc.ofMallocng]
      intro i _hi
      have hvac : ∀ {α : Type} {entry : BitVec 64} {spec : Spec α},
          subroutine_ok (hashbrownLib.blockProgram mpl i) entry (withCodeInv (Afam mpl) spec) := by
        intro α entry spec
        refine subroutine_ok_of_steps_outcome fun x R s0 _ _ hpre _ _ => ?_
        dsimp only [withCodeInv] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        exact False.elim (hAf.2 s0.mem hpre.1)
      exact
        { allocShim_ok := hvac
          alloc_ok     := hvac
          dealloc_ok   := hvac
          memset_ok    := hvac
          memmove_ok   := hvac
          panic_hooks  := fun hao => False.elim (hAf.1 ▸ hao) }
  have hContracts := hashbrownFunctionalCorrectness_ok Afam (fun _ => none) hext_all
  have hCodeHb : ∀ {m : Memory}, (Afam C.hbMpl).CodeInv m → hashbrownLib.CodeLoaded C.hbMpl m := by
    rw [hAfam_eq]
    exact fun hci => (hCode hci).2
  have lift {α : Type} {fnName : String} {spec : Obj.Placement → HbAlloc → Spec α}
      (hsub : hashbrownLib.subroutineOk fnName
        (fun m => withCodeInv (Afam m) (spec (mplAsPl m) (Afam m))) (fun _ => none)) :
      subroutine_ok P (hashbrownLib.fnAddr C.hbMpl fnName) (withCodeInv A0 (spec C.hbPl A0)) := by
    have h := subroutine_ok_cli_of_hbSubroutineOk hPlaceable hP_ext hP_svc hCodeHb hsub
    rwa [hAfam_eq] at h
  exact
    { new_ok                      := lift hContracts.new_ok
      with_capacity_infallible_ok := lift hContracts.with_capacity_infallible_ok
      insert_infallible_ok        := lift hContracts.insert_infallible_ok
      get_ok                      := lift hContracts.get_ok
      contains_key_ok             := lift hContracts.contains_key_ok
      remove_ok                   := lift hContracts.remove_ok
      len_ok                      := lift hContracts.len_ok
      is_empty_ok                 := lift hContracts.is_empty_ok
      clear_ok                    := lift hContracts.clear_ok
      drop_ok                     := lift hContracts.drop_ok }

end CaseStudies.Hashbrown.Proofs.StdCli
