/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.HooksE.CommonBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun

/-!
# Budget-Threaded Allocator and Memory Hook Bridges for `main`

`RustCliAllocBudget M` counterparts of `AllocFsA1.lean`: defines `CliAllocHooks A lim` and proves
`VmPreserved`-carrying `HookOk` and `HookSat` witnesses for `shim`, `memcpy` (including read-only
source), `memmove`, and `memset` on `cliExterns W` and `cliExternsWith ext` (`CliExternsBudgetOk`).
-/

@[expose] public section

set_option linter.dupNamespace false
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams allocHook0 deallocHook extraImagePanicNames isImagePanicSymbol reallocHook0
   withImagePanics)
open CryptoVerification.LibsignalTripleRatchet
  (allocName deallocName extHookStack memcpyName memmoveName memsetName reallocName
   sessionMemcpyRegionSpec sessionMemcpySpec sessionMemmoveSpec sessionMemsetRegionSpec
   sessionMemsetSpec sessionShimSpec shimName withStack)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliExterns cliExternsWith cliExterns_row readStdinName writeFileName writeStdoutName)
open CryptoVerification.SignalSession.CliExt
  (ioNames memHookStack memcpyROSpec memcpySpec memmoveSpec memsetSpec shimSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (allocHookStack_le_extHookStack extHookStack_le memcpy_row pos_of_extHookStack_le)
open CryptoVerification.SpqrV1.Alloc
  (hookMemcpy_region_ro_trace_ok sessionMemcpyRegionROSpec sessionMemcpyRegionROSpecWithStack
   sessionMemcpyRegionROSpecX)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (CliExternsBudgetOk cliAllocNames withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
  (hookOk_rustAllocWithStack hookOk_rustDeallocExternWithStack hookOk_rustReallocExternWithStack
   hookOk_withStack hookOk_withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (sessionMemcpyBudget_hookOk sessionMemcpyRegionBudget_hookOk sessionMemmoveBudget_hookOk
   sessionMemsetBudget_hookOk sessionMemsetRegionBudget_hookOk sessionShimBudget_hookOk
   vmPreserved_hookMemcpy vmPreserved_hookMemmove vmPreserved_hookMemset vmPreserved_hookNoop)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemmoveBudgetSpec
   sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack rustReallocExternSpecWithStack)

/-! ## Allocator Hook Bundle and Built-In `VmPreserved` Witnesses -/

/-- `HookOk` bundle for `allocHook0`, `deallocHook`, and `reallocHook0` against `(A, lim)`. -/
structure CliAllocHooks [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Prop where
  alloc : HookOk allocHook0 (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookOk deallocHook (rustCliDeallocBudgetSpec M A lim)
  realloc : HookOk reallocHook0 (rustCliReallocBudgetSpec M A lim)

theorem hookMemcpy_vm_ok (stk : Nat) :
    HookOk hookMemcpy (withVmPreserved (libcMemcpySpec stk)) :=
  hookOk_withVmPreserved (hookMemcpy_ok stk) vmPreserved_hookMemcpy

theorem hookMemcpy_region_vm_ok :
    HookOk hookMemcpy (withVmPreserved memcpyRegionSpec) :=
  hookOk_withVmPreserved hookMemcpy_region_ok vmPreserved_hookMemcpy

theorem hookMemmove_vm_ok (stk : Nat) :
    HookOk hookMemmove (withVmPreserved (libcMemmoveSpec stk)) :=
  hookOk_withVmPreserved (hookMemmove_ok stk) vmPreserved_hookMemmove

theorem hookMemset_vm_ok (stk : Nat) (hpos : 0 < stk) :
    HookOk hookMemset (withVmPreserved (libcMemsetSpec stk)) :=
  hookOk_withVmPreserved (hookMemset_ok stk hpos) vmPreserved_hookMemset

theorem hookMemset_region_vm_ok :
    HookOk hookMemset (withVmPreserved memsetRegionSpec) :=
  hookOk_withVmPreserved hookMemset_region_ok vmPreserved_hookMemset

theorem hookMemcpy_region_ro_vm_ok :
    HookOk hookMemcpy (withVmPreserved sessionMemcpyRegionROSpec) :=
  hookOk_withVmPreserved hookMemcpy_region_ro_trace_ok vmPreserved_hookMemcpy

theorem cli_hookSat_memcpy_region_ro_vm (W : CliHooks) :
    HookSat (cliExterns W) memcpyName (withVmPreserved sessionMemcpyRegionROSpec) :=
  ⟨hookMemcpy, cliExterns_row W (memcpy_row W), hookMemcpy_region_ro_vm_ok⟩

/-! ## `VmPreserved` `HookOk` Lifts from `CliExt` Specs -/

theorem hookSat_cliExternsWith_map {α β : Type}
    {ext : String → Option (State → State)} {name : String}
    {s₁ : Spec α} {s₂ : Spec β}
    (hnp : isImagePanicSymbol name = false)
    (hsat : HookSat ext name s₁)
    (hmap : ∀ f, ext name = some f → HookOk f s₁ → HookOk f s₂) :
    HookSat (cliExternsWith ext) name s₂ := by
  obtain ⟨f, hf, hok⟩ := hsat
  refine ⟨f, ?_, hmap f hf hok⟩
  simp [cliExternsWith, hnp, hf]

private theorem hookOk_conseq {α β : Type} {f : State → State} {spec₁ : Spec α} {spec₂ : Spec β}
    (hh : HookOk f spec₁)
    (hstep : ∀ (x : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec₂.pre x s0 ∗ R) →
      ∃ (y : α) (F : SepProp),
        (s0.mem ⊨ spec₁.pre y s0 ∗ (F ∗ R)) ∧
        ∀ sf, (sf.mem ⊨ spec₁.post y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec₂.post x s0 sf ∗ R))
    (hpan₁ : ∀ y s0 sf, spec₁.onPanic y s0 sf = ⌜False⌝ := by intros; rfl)
    (hex₁ : ∀ y code s0 sf, spec₁.onExit y code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom₁ : ∀ y s0 sf, spec₁.onOom y s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f spec₂ := by
  intro x R s0 hrun hpre hsp
  obtain ⟨y, F, hpre₁, hpost₁⟩ := hstep x R s0 hpre
  obtain ⟨hkf, hsym, hout⟩ := hh y (F ∗ R) s0 hrun hpre₁ hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost₁ (f s0) hpost⟩
  · rw [hpan₁ y s0 (f s0), satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · rw [hex₁ y code s0 (f s0), satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · rw [hoom₁ y s0 (f s0), satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem stackAt_split_ge {sp : BitVec 64} {inner stk : Nat}
    (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - inner) ∗ stackAt sp inner := by
  have h1 := ProofLib.stackAt_split_bottom sp inner (stk - inner) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

theorem memHookStack_le_of_ext {stk : Nat} (hle : extHookStack ≤ stk) :
    memHookStack ≤ stk :=
  Nat.le_trans (by decide : memHookStack ≤ extHookStack) hle

private theorem hookOk_shim_plain_of_cliExt {f : State → State}
    (hh : HookOk f shimSpec) :
    HookOk f sessionShimSpec :=
  hookOk_conseq hh fun u R s0 hpre => ⟨u, emp,
    by simpa [shimSpec, sessionShimSpec, emp_sepConj] using hpre,
    fun sf hpost => by simpa [shimSpec, sessionShimSpec, emp_sepConj] using hpost⟩

theorem hookOk_shim_of_cliExt {f : State → State}
    (hh : HookOk f shimSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f sessionShimBudgetSpec :=
  hookOk_withVmPreserved (hookOk_shim_plain_of_cliExt hh) hvm

private theorem hookOk_sessionMemcpy_plain_of_cliExt {f : State → State}
    (hh : HookOk f memcpySpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpySpec stk) := by
  refine hookOk_conseq hh fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(dst, src, bs), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - memHookStack), ?_, ?_⟩
  · dsimp only [sessionMemcpySpec, memcpySpec, libcMemcpySpec] at hpre ⊢
    rw [hsp] at hpre
    exact Eq.mp (by sep_ac_rfl) hpre
  · intro sf hpost
    dsimp only [sessionMemcpySpec, memcpySpec] at hpost ⊢
    rw [hsp]
    exact Eq.mp (by sep_ac_rfl) hpost

theorem hookOk_sessionMemcpy_of_cliExt {f : State → State}
    (hh : HookOk f memcpySpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpyBudgetSpec stk) :=
  hookOk_withVmPreserved (hookOk_sessionMemcpy_plain_of_cliExt hh stk hle hmax) hvm

private theorem hookOk_libcMemcpy_plain_of_cliExt {f : State → State}
    (hh : HookOk f memcpySpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemcpySpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemcpy_plain_of_cliExt hh stk hle hmax)
    fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), emp,
      by simpa [sessionMemcpySpec, libcMemcpySpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

theorem hookOk_libcMemcpy_of_cliExt {f : State → State}
    (hh : HookOk f memcpySpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withVmPreserved (libcMemcpySpec stk)) :=
  hookOk_withVmPreserved (hookOk_libcMemcpy_plain_of_cliExt hh stk hle hmax) hvm

theorem hookOk_sessionMemcpyRegion_of_cliExt {f : State → State}
    (hh : HookOk f memcpySpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack sessionMemcpyRegionBudgetSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemcpy_of_cliExt hh hvm stk hle hmax)
    fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), emp, ?_, ?_⟩
  · dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec, sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec] at hpre ⊢
    simp only [emp_sepConj]
    exact Eq.mp (by sep_ac_rfl) hpre
  · intro sf hpost
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      sessionMemcpyBudgetSpec, sessionMemcpySpec] at hpost ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Eq.mp (by sep_ac_rfl) hpost.2.2⟩

theorem hookOk_memcpyRegion_of_cliExt {f : State → State}
    (hh : HookOk f memcpySpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack (withVmPreserved memcpyRegionSpec) stk) := by
  refine hookOk_conseq (hookOk_sessionMemcpyRegion_of_cliExt hh hvm stk hle hmax)
    fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), emp,
      by simpa [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
        withVmPreserved, memcpyRegionSpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
    withVmPreserved, memcpyRegionSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, hpost.2.1.1, hpost.2.2⟩

private theorem hookOk_sessionMemcpyRegionRO_plain_of_cliExt {f : State → State}
    (hh : HookOk f memcpyROSpec) (stk : Nat)
    (hle : memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack sessionMemcpyRegionROSpec stk) := by
  refine hookOk_conseq hh fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) hle hmax
  refine ⟨(dst, src, bs), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - memHookStack), ?_, ?_⟩
  · dsimp only [withStack, sessionMemcpyRegionROSpec, memcpyROSpec,
      CryptoVerification.SignalSession.CliExt.withStack] at hpre ⊢
    rw [hsp] at hpre
    exact Eq.mp (by sep_ac_rfl) hpre
  · intro sf hpost
    dsimp only [withStack, sessionMemcpyRegionROSpec, memcpyROSpec,
      CryptoVerification.SignalSession.CliExt.withStack] at hpost ⊢
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Eq.mp (by sep_ac_rfl) hpost.2⟩

theorem hookOk_sessionMemcpyRegionRO_of_cliExt {f : State → State}
    (hh : HookOk f memcpyROSpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk) := by
  refine hookOk_conseq
    (hookOk_withVmPreserved (hookOk_sessionMemcpyRegionRO_plain_of_cliExt hh stk hle hmax) hvm)
    fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), emp,
      by simpa [withVmPreserved, withStack, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [withVmPreserved, withStack, sessionMemcpyRegionROSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, hpost.2.1, Eq.mp (by sep_ac_rfl) hpost.2.2⟩

private theorem hookOk_sessionMemmove_plain_of_cliExt {f : State → State}
    (hh : HookOk f memmoveSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemmoveSpec stk) := by
  refine hookOk_conseq hh fun ⟨base, buf, dst, src, len⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(base, buf, dst, src, len),
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - memHookStack), ?_, ?_⟩
  · dsimp only [sessionMemmoveSpec, memmoveSpec, libcMemmoveSpec] at hpre ⊢
    rw [hsp] at hpre
    exact Eq.mp (by sep_ac_rfl) hpre
  · intro sf hpost
    dsimp only [sessionMemmoveSpec, memmoveSpec] at hpost ⊢
    rw [hsp]
    exact Eq.mp (by sep_ac_rfl) hpost

theorem hookOk_sessionMemmove_of_cliExt {f : State → State}
    (hh : HookOk f memmoveSpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemmoveBudgetSpec stk) :=
  hookOk_withVmPreserved (hookOk_sessionMemmove_plain_of_cliExt hh stk hle hmax) hvm

private theorem hookOk_libcMemmove_plain_of_cliExt {f : State → State}
    (hh : HookOk f memmoveSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemmoveSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemmove_plain_of_cliExt hh stk hle hmax)
    fun x R s0 hpre => ⟨x, emp,
      by simpa [sessionMemmoveSpec, libcMemmoveSpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [sessionMemmoveSpec, libcMemmoveSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

theorem hookOk_libcMemmove_of_cliExt {f : State → State}
    (hh : HookOk f memmoveSpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withVmPreserved (libcMemmoveSpec stk)) :=
  hookOk_withVmPreserved (hookOk_libcMemmove_plain_of_cliExt hh stk hle hmax) hvm

private theorem hookOk_sessionMemset_plain_of_cliExt {f : State → State}
    (hh : HookOk f memsetSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemsetSpec stk) := by
  refine hookOk_conseq hh fun ⟨ptr, c, len⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(ptr, c, len), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - memHookStack), ?_, ?_⟩
  · dsimp only [sessionMemsetSpec, memsetSpec, libcMemsetSpec] at hpre ⊢
    rw [hsp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2⟩, Eq.mp (by sep_ac_rfl) hpre.2⟩
  · intro sf hpost
    dsimp only [sessionMemsetSpec, memsetSpec] at hpost ⊢
    rw [hsp]
    exact Eq.mp (by sep_ac_rfl) hpost

theorem hookOk_sessionMemset_of_cliExt {f : State → State}
    (hh : HookOk f memsetSpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemsetBudgetSpec stk) :=
  hookOk_withVmPreserved (hookOk_sessionMemset_plain_of_cliExt hh stk hle hmax) hvm

private theorem hookOk_libcMemset_plain_of_cliExt {f : State → State}
    (hh : HookOk f memsetSpec) (stk : Nat)
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemsetSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemset_plain_of_cliExt hh stk hle hmax)
    fun x R s0 hpre => ⟨x, emp,
      by simpa [sessionMemsetSpec, libcMemsetSpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [sessionMemsetSpec, libcMemsetSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

theorem hookOk_libcMemset_of_cliExt {f : State → State}
    (hh : HookOk f memsetSpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withVmPreserved (libcMemsetSpec stk)) :=
  hookOk_withVmPreserved (hookOk_libcMemset_plain_of_cliExt hh stk hle hmax) hvm

theorem hookOk_sessionMemsetRegion_of_cliExt {f : State → State}
    (hh : HookOk f memsetSpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack sessionMemsetRegionBudgetSpec stk) := by
  refine hookOk_conseq (hookOk_sessionMemset_of_cliExt hh hvm stk hle hmax)
    fun ⟨ptr, c, len⟩ R s0 hpre => ⟨(ptr, c, len), emp, ?_, ?_⟩
  · dsimp only [withStack, sessionMemsetRegionBudgetSpec, sessionMemsetRegionSpec,
      memsetRegionSpec, sessionMemsetBudgetSpec, sessionMemsetSpec, libcMemsetSpec] at hpre ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, Eq.mp (by sep_ac_rfl) hpre.2⟩
  · intro sf hpost
    dsimp only [withStack, sessionMemsetRegionBudgetSpec, sessionMemsetRegionSpec,
      sessionMemsetBudgetSpec, sessionMemsetSpec] at hpost ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Eq.mp (by sep_ac_rfl) hpost.2.2⟩

theorem hookOk_memsetRegion_of_cliExt {f : State → State}
    (hh : HookOk f memsetSpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack (withVmPreserved memsetRegionSpec) stk) := by
  refine hookOk_conseq (hookOk_sessionMemsetRegion_of_cliExt hh hvm stk hle hmax)
    fun x R s0 hpre => ⟨x, emp,
      by simpa [withStack, sessionMemsetRegionBudgetSpec, sessionMemsetRegionSpec,
        withVmPreserved, memsetRegionSpec, emp_sepConj] using hpre, ?_⟩
  intro sf hpost
  dsimp only [withStack, sessionMemsetRegionBudgetSpec, sessionMemsetRegionSpec,
    withVmPreserved, memsetRegionSpec] at hpost ⊢
  simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, hpost.2.1.1, hpost.2.2⟩

/-! ## `HookSat (cliExternsWith ext)` Projections from `CliExternsBudgetOk` -/

theorem alloc_nonPanicE : isImagePanicSymbol allocName = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol, allocName]
theorem dealloc_nonPanicE : isImagePanicSymbol deallocName = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol, deallocName]
theorem realloc_nonPanicE : isImagePanicSymbol reallocName = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol, reallocName]
theorem shim_nonPanicE : isImagePanicSymbol shimName = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol, shimName]
theorem memcpy_nonPanicE : isImagePanicSymbol memcpyName = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol, memcpyName]
theorem memmove_nonPanicE : isImagePanicSymbol memmoveName = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol, memmoveName]
theorem memset_nonPanicE : isImagePanicSymbol memsetName = false := by
  simp [isImagePanicSymbol, extraImagePanicNames, Rust.isPanicSymbol, memsetName]

theorem alloc_notIo : allocName ∉ ioNames := by
  simp [ioNames, allocName, CryptoVerification.SignalSession.readFileName,
    writeFileName, readStdinName, writeStdoutName]
theorem dealloc_notIo : deallocName ∉ ioNames := by
  simp [ioNames, deallocName, CryptoVerification.SignalSession.readFileName,
    writeFileName, readStdinName, writeStdoutName]
theorem realloc_notIo : reallocName ∉ ioNames := by
  simp [ioNames, reallocName, CryptoVerification.SignalSession.readFileName,
    writeFileName, readStdinName, writeStdoutName]
theorem shim_notIo : shimName ∉ ioNames := by
  simp [ioNames, shimName, CryptoVerification.SignalSession.readFileName,
    writeFileName, readStdinName, writeStdoutName]
theorem memcpy_notIo : memcpyName ∉ ioNames := by
  simp [ioNames, memcpyName, CryptoVerification.SignalSession.readFileName,
    writeFileName, readStdinName, writeStdoutName]
theorem memmove_notIo : memmoveName ∉ ioNames := by
  simp [ioNames, memmoveName, CryptoVerification.SignalSession.readFileName,
    writeFileName, readStdinName, writeStdoutName]
theorem memset_notIo : memsetName ∉ ioNames := by
  simp [ioNames, memsetName, CryptoVerification.SignalSession.readFileName,
    writeFileName, readStdinName, writeStdoutName]

theorem shim_notAlloc : shimName ∉ cliAllocNames := by decide
theorem memcpy_notAlloc : memcpyName ∉ cliAllocNames := by decide
theorem memmove_notAlloc : memmoveName ∉ cliAllocNames := by decide
theorem memset_notAlloc : memsetName ∉ cliAllocNames := by decide

section ExternsOk

variable {P : PEParams} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {ext : String → Option (State → State)}

theorem alloc_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) :
    HookSat (cliExternsWith ext) allocName (rustAllocSpecWithStack M A lim false extHookStack) :=
  hookSat_cliExternsWith_map alloc_nonPanicE hOk.alloc.alloc fun _ _ h =>
    hookOk_rustAllocWithStack (stk := extHookStack) h allocHookStack_le_extHookStack extHookStack_le

theorem alloc_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) :
    HookSat (cliExternsWith ext) allocName
      (rustAllocSpecWithStack M A lim false extHookStack).keepsFs :=
  hookSat_cliExternsWith_map alloc_nonPanicE hOk.alloc.alloc fun f hf h =>
    (hookOk_rustAllocWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
      extHookStack_le).keepsFs (hOk.fsKept _ f hf alloc_notIo)

theorem dealloc_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) :
    HookSat (cliExternsWith ext) deallocName
      (rustDeallocExternSpecWithStack M A lim extHookStack) :=
  hookSat_cliExternsWith_map dealloc_nonPanicE hOk.alloc.dealloc fun _ _ h =>
    hookOk_rustDeallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
      extHookStack_le

theorem dealloc_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) :
    HookSat (cliExternsWith ext) deallocName
      (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs :=
  hookSat_cliExternsWith_map dealloc_nonPanicE hOk.alloc.dealloc fun f hf h =>
    (hookOk_rustDeallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
      extHookStack_le).keepsFs (hOk.fsKept _ f hf dealloc_notIo)

theorem realloc_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) :
    HookSat (cliExternsWith ext) reallocName
      (rustReallocExternSpecWithStack M A lim extHookStack) :=
  hookSat_cliExternsWith_map realloc_nonPanicE hOk.alloc.realloc fun _ _ h =>
    hookOk_rustReallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
      extHookStack_le

theorem realloc_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) :
    HookSat (cliExternsWith ext) reallocName
      (rustReallocExternSpecWithStack M A lim extHookStack).keepsFs :=
  hookSat_cliExternsWith_map realloc_nonPanicE hOk.alloc.realloc fun f hf h =>
    (hookOk_rustReallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack
      extHookStack_le).keepsFs (hOk.fsKept _ f hf realloc_notIo)

theorem shim_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) (stk : Nat) :
    HookSat (cliExternsWith ext) shimName (withStack sessionShimBudgetSpec stk) :=
  hookSat_cliExternsWith_map shim_nonPanicE hOk.shim fun f hf h =>
    hookOk_withStack (hookOk_shim_of_cliExt h (hOk.vmKept _ f hf shim_notAlloc)) stk

theorem shim_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) (stk : Nat) :
    HookSat (cliExternsWith ext) shimName (withStack sessionShimBudgetSpec stk).keepsFs :=
  hookSat_cliExternsWith_map shim_nonPanicE hOk.shim fun f hf h =>
    (hookOk_withStack (hookOk_shim_of_cliExt h (hOk.vmKept _ f hf shim_notAlloc)) stk).keepsFs
      (hOk.fsKept _ f hf shim_notIo)

theorem memcpy_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName (withVmPreserved (libcMemcpySpec stk)) :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
    hookOk_libcMemcpy_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax

theorem memcpy_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName (withVmPreserved (libcMemcpySpec stk)).keepsFs :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
    (hookOk_libcMemcpy_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memcpy_notIo)

theorem sessionMemcpy_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName (sessionMemcpyBudgetSpec stk) :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
    hookOk_sessionMemcpy_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax

theorem sessionMemcpy_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName (sessionMemcpyBudgetSpec stk).keepsFs :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
    (hookOk_sessionMemcpy_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memcpy_notIo)

theorem memcpyRegion_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName (withStack (withVmPreserved memcpyRegionSpec) stk) :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
    hookOk_memcpyRegion_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax

theorem memcpyRegion_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName
      (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
    (hookOk_memcpyRegion_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memcpy_notIo)

theorem sessionMemcpyRegion_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName (withStack sessionMemcpyRegionBudgetSpec stk) :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
    hookOk_sessionMemcpyRegion_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax

theorem sessionMemcpyRegion_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName
      (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpy fun f hf h =>
    (hookOk_sessionMemcpyRegion_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memcpy_notIo)

theorem memmove_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memmoveName (withVmPreserved (libcMemmoveSpec stk)) :=
  hookSat_cliExternsWith_map memmove_nonPanicE hOk.memmove fun f hf h =>
    hookOk_libcMemmove_of_cliExt h (hOk.vmKept _ f hf memmove_notAlloc) stk hle hmax

theorem memmove_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memmoveName (withVmPreserved (libcMemmoveSpec stk)).keepsFs :=
  hookSat_cliExternsWith_map memmove_nonPanicE hOk.memmove fun f hf h =>
    (hookOk_libcMemmove_of_cliExt h (hOk.vmKept _ f hf memmove_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memmove_notIo)

theorem sessionMemmove_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memmoveName (sessionMemmoveBudgetSpec stk) :=
  hookSat_cliExternsWith_map memmove_nonPanicE hOk.memmove fun f hf h =>
    hookOk_sessionMemmove_of_cliExt h (hOk.vmKept _ f hf memmove_notAlloc) stk hle hmax

theorem sessionMemmove_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memmoveName (sessionMemmoveBudgetSpec stk).keepsFs :=
  hookSat_cliExternsWith_map memmove_nonPanicE hOk.memmove fun f hf h =>
    (hookOk_sessionMemmove_of_cliExt h (hOk.vmKept _ f hf memmove_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memmove_notIo)

theorem memset_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memsetName (withVmPreserved (libcMemsetSpec stk)) :=
  hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
    hookOk_libcMemset_of_cliExt h (hOk.vmKept _ f hf memset_notAlloc) stk hle hmax

theorem memset_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memsetName (withVmPreserved (libcMemsetSpec stk)).keepsFs :=
  hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
    (hookOk_libcMemset_of_cliExt h (hOk.vmKept _ f hf memset_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memset_notIo)

theorem sessionMemset_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memsetName (sessionMemsetBudgetSpec stk) :=
  hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
    hookOk_sessionMemset_of_cliExt h (hOk.vmKept _ f hf memset_notAlloc) stk hle hmax

theorem sessionMemset_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memsetName (sessionMemsetBudgetSpec stk).keepsFs :=
  hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
    (hookOk_sessionMemset_of_cliExt h (hOk.vmKept _ f hf memset_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memset_notIo)

theorem memsetRegion_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memsetName (withStack (withVmPreserved memsetRegionSpec) stk) :=
  hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
    hookOk_memsetRegion_of_cliExt h (hOk.vmKept _ f hf memset_notAlloc) stk hle hmax

theorem memsetRegion_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memsetName
      (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs :=
  hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
    (hookOk_memsetRegion_of_cliExt h (hOk.vmKept _ f hf memset_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memset_notIo)

theorem sessionMemsetRegion_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memsetName (withStack sessionMemsetRegionBudgetSpec stk) :=
  hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
    hookOk_sessionMemsetRegion_of_cliExt h (hOk.vmKept _ f hf memset_notAlloc) stk hle hmax

theorem sessionMemsetRegion_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memsetName
      (withStack sessionMemsetRegionBudgetSpec stk).keepsFs :=
  hookSat_cliExternsWith_map memset_nonPanicE hOk.memset fun f hf h =>
    (hookOk_sessionMemsetRegion_of_cliExt h (hOk.vmKept _ f hf memset_notAlloc) stk hle hmax).keepsFs
      (hOk.fsKept _ f hf memset_notIo)

theorem sessionMemcpyRegionRO_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName
      (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk) :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpyRO fun f hf h =>
    hookOk_sessionMemcpyRegionRO_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk hle hmax

theorem sessionMemcpyRegionRO_keepsFs_hookSat_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName
      (withStack (withVmPreserved sessionMemcpyRegionROSpec) stk).keepsFs :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpyRO fun f hf h =>
    (hookOk_sessionMemcpyRegionRO_of_cliExt h (hOk.vmKept _ f hf memcpy_notAlloc) stk
      (memHookStack_le_of_ext hle) hmax).keepsFs (hOk.fsKept _ f hf memcpy_notIo)

/-- `HookSat` for `withVmPreserved (sessionMemcpyRegionROSpecWithStack stk)` on `cliExternsWith ext`
(`memHookStack ≤ stk ≤ 2 ^ 64`) from `CliExternsBudgetOk`. -/
theorem memcpyRegionRO_withStack_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext)
    (stk : Nat) (hle : memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookSat (cliExternsWith ext) memcpyName
      (withVmPreserved (sessionMemcpyRegionROSpecWithStack stk)) :=
  hookSat_cliExternsWith_map memcpy_nonPanicE hOk.memcpyRO fun f hf hh =>
    hookOk_withVmPreserved
      (hookOk_conseq (hookOk_sessionMemcpyRegionRO_plain_of_cliExt hh stk hle hmax)
        fun ⟨dst, src, bs⟩ R s0 hpre =>
          ⟨(dst, src, bs), emp,
            by
              dsimp only [withStack, sessionMemcpyRegionROSpecWithStack,
                sessionMemcpyRegionROSpec] at hpre ⊢
              simp only [emp_sepConj]
              exact Eq.mp (by sep_ac_rfl) hpre,
            fun sf hpost => by
              dsimp only [withStack, sessionMemcpyRegionROSpecWithStack,
                sessionMemcpyRegionROSpec] at hpost ⊢
              simp only [emp_sepConj] at hpost
              exact Eq.mp (by sep_ac_rfl) hpost⟩)
      (hOk.vmKept _ f hf memcpy_notAlloc)

theorem memcpyRegionRO_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) :
    HookSat (cliExternsWith ext) memcpyName
      (withVmPreserved (sessionMemcpyRegionROSpecWithStack memHookStack)) :=
  memcpyRegionRO_withStack_of_externsOk hOk memHookStack (Nat.le_refl _) (by decide)

theorem memcpyRegionRO_X_of_externsOk [LibsignalPlacement] (hOk : CliExternsBudgetOk P M A lim ext) :
    HookSat (cliExternsWith ext) memcpyName
      (withVmPreserved sessionMemcpyRegionROSpecX) :=
  memcpyRegionRO_withStack_of_externsOk hOk extHookStack (by decide) extHookStack_le

end ExternsOk

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget
