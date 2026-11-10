/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.AdrpLdst
public import ProofLib.Placed.Multi
public import VerifiedLibraries.Mallocng.Spec

/-!
# Multi-Block Placed `mallocng` Infrastructure

Defines the ambient placement typeclass `MallocngMultiPlacement`, symbol-resolution simp lemmas to
`maddrs.*` and `mbase j`, cross-block `CodeLoaded` combinators (`withCL`, `sepWP_seq_cl`,
`subroutine_ok_block_to_block`), and per-block rebase and `ADRP` relocation step rules.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection VerifiedLibraries.Mallocng

/-! ## Ambient multi-block placement and address normalization -/

/-- Ambient valid multi-block placement and supervisor-call handler for `VerifiedLibraries.mallocngLib`. -/
class MallocngMultiPlacement where
  mpl       : MultiPlacement
  svc       : State → State
  placeable : VerifiedLibraries.mallocngLib.Placeable mpl
  svcValid  : MallocngSvcValid svc

abbrev mmpl [MallocngMultiPlacement] : MultiPlacement := MallocngMultiPlacement.mpl

abbrev msvc [MallocngMultiPlacement] : State → State := MallocngMultiPlacement.svc

abbrev mbase [MallocngMultiPlacement] (i : Nat) : BitVec 64 := MallocngMultiPlacement.mpl.base i

abbrev maddrs [MallocngMultiPlacement] : MallocngAddrs :=
  mallocngAddrsOfPlacement MallocngMultiPlacement.mpl

@[simp] theorem mallocngLib_blocks_length : VerifiedLibraries.mallocngLib.blocks.length = 24 := rfl

@[simp, arm64_norm, wp_norm] theorem resolve_size_classes [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__malloc_size_classes" = maddrs.sizeClasses := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_debruijn4681 [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "debruijn32.4681" = maddrs.debruijnFree := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_med_cnt_tab [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "med_cnt_tab" = maddrs.medCntTab := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_small_cnt_tab [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "small_cnt_tab" = maddrs.smallCntTab := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_debruijn5048 [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "debruijn32.5048" = maddrs.debruijnAlloc := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ctx [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__malloc_context" = maddrs.ctx := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_libc [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__libc" = maddrs.libc := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_lock_sym [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__malloc_lock" = maddrs.lock := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_replaced [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__malloc_replaced" = maddrs.replaced := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_aaReplaced [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__aligned_alloc_replaced" = maddrs.aaReplaced := rfl

@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_size_classes [MallocngMultiPlacement] :
    mmpl.ρ "__malloc_size_classes" = maddrs.sizeClasses := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_debruijn4681 [MallocngMultiPlacement] :
    mmpl.ρ "debruijn32.4681" = maddrs.debruijnFree := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_med_cnt_tab [MallocngMultiPlacement] :
    mmpl.ρ "med_cnt_tab" = maddrs.medCntTab := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_small_cnt_tab [MallocngMultiPlacement] :
    mmpl.ρ "small_cnt_tab" = maddrs.smallCntTab := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_debruijn5048 [MallocngMultiPlacement] :
    mmpl.ρ "debruijn32.5048" = maddrs.debruijnAlloc := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_ctx [MallocngMultiPlacement] :
    mmpl.ρ "__malloc_context" = maddrs.ctx := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_libc [MallocngMultiPlacement] :
    mmpl.ρ "__libc" = maddrs.libc := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_lock [MallocngMultiPlacement] :
    mmpl.ρ "__malloc_lock" = maddrs.lock := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_replaced [MallocngMultiPlacement] :
    mmpl.ρ "__malloc_replaced" = maddrs.replaced := rfl
@[simp, arm64_norm, wp_norm] theorem mmpl_ρ_aaReplaced [MallocngMultiPlacement] :
    mmpl.ρ "__aligned_alloc_replaced" = maddrs.aaReplaced := rfl

-- All 24 blocks define their symbols at offset `0`.
private theorem add_zero_64 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

@[simp, arm64_norm, wp_norm] theorem resolve_errno3 [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "___errno_location" = mbase 0 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_errno2 [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__errno_location" = mbase 0 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_syscall_ret [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__syscall_ret" = mbase 1 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_calloc [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "calloc" = mbase 2 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_free [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "free" = mbase 3 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_default_malloc [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "default_malloc" = mbase 4 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_malloc [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "malloc" = mbase 4 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_libc_malloc [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__libc_malloc" = mbase 4 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_nontrivial_free [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "nontrivial_free" = mbase 5 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_libc_free [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__libc_free" = mbase 6 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_alloc_meta [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__malloc_alloc_meta" = mbase 7 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_alloc_slot [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "alloc_slot" = mbase 8 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_libc_malloc_impl [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__libc_malloc_impl" = mbase 9 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_allzerop [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__malloc_allzerop" = mbase 10 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_posix_memalign [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "posix_memalign" = mbase 11 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_aligned_alloc [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "aligned_alloc" = mbase 12 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_realloc [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "realloc" = mbase 13 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_libc_realloc [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__libc_realloc" = mbase 14 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_vm_wait [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__vm_wait" = mbase 15 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_mmapPriv [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__mmap" = mbase 16 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_mmap [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "mmap" = mbase 16 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_mprotectPriv [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__mprotect" = mbase 17 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_mprotect [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "mprotect" = mbase 17 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_mremapPriv [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__mremap" = mbase 18 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_mremap [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "mremap" = mbase 18 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_munmapPriv [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__munmap" = mbase 19 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_munmap [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "munmap" = mbase 19 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_memcpy [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "memcpy" = mbase 20 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_memset [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "memset" = mbase 21 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_lock_fn [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__lock" = mbase 22 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_unlock_fn [MallocngMultiPlacement] :
    VerifiedLibraries.mallocngLib.resolve mmpl "__unlock" = mbase 23 := add_zero_64 _

@[simp, arm64_norm, wp_norm] theorem fnAddr_calloc (mpl : MultiPlacement) :
    VerifiedLibraries.mallocngLib.fnAddr mpl "calloc" = mpl.base 2 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem fnAddr_free (mpl : MultiPlacement) :
    VerifiedLibraries.mallocngLib.fnAddr mpl "free" = mpl.base 3 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem fnAddr_malloc (mpl : MultiPlacement) :
    VerifiedLibraries.mallocngLib.fnAddr mpl "malloc" = mpl.base 4 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem fnAddr_posix_memalign (mpl : MultiPlacement) :
    VerifiedLibraries.mallocngLib.fnAddr mpl "posix_memalign" = mpl.base 11 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem fnAddr_aligned_alloc (mpl : MultiPlacement) :
    VerifiedLibraries.mallocngLib.fnAddr mpl "aligned_alloc" = mpl.base 12 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem fnAddr_realloc (mpl : MultiPlacement) :
    VerifiedLibraries.mallocngLib.fnAddr mpl "realloc" = mpl.base 13 := add_zero_64 _

/-! ## Cross-block `CodeLoaded` combinators -/

/-- Adjoin `VerifiedLibraries.mallocngLib.CodeLoaded mpl` to both precondition and postcondition of
    `spec` so callers receive `CodeLoaded mpl sf.mem` back after every cross-block `wp_call`. -/
def withCL (mpl : MultiPlacement) {α : Type} (spec : Spec α) : Spec α where
  pre x s0 := spec.pre x s0 ∗ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem⌝
  post x s0 sf := spec.post x s0 sf ∗ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mpl sf.mem⌝
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

/-- Convert an internal `withCL` contract into `VerifiedLibraries.mallocngLib.withCodeLoaded` by dropping
    the postcondition `⌜CodeLoaded mpl sf.mem⌝` copy. -/
theorem withCL_to_withCodeLoaded {α : Type} {prog : Program} {entry : BitVec 64}
    {mpl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withCL mpl spec)) :
    subroutine_ok prog entry (VerifiedLibraries.mallocngLib.withCodeLoaded mpl spec) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun x R s0 sf hq => ?_)
  refine Satisfies.mono ?_ hq
  dsimp only [withCL, MultiPlacedLib.withCodeLoaded]
  rw [sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_left fun _ => Entails.refl R)

/-- Split an arbitrary-`oom` `SepWP` proof at `mid` and re-establish
    `VerifiedLibraries.mallocngLib.CodeLoaded mpl sm.mem` across any preceding instructions (including
    `STP`/`STR` memory writes). -/
theorem sepWP_seq_cl {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {mpl : MultiPlacement}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => VerifiedLibraries.mallocngLib.CodeLoaded mpl sm.mem → SepWP prog target sm Pm post oom)
      oom) :
    SepWP prog target s P post oom :=
  SepWP.seq (SepWP.mono_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcl h
    (fun _ _ _ _ hcl_m hcont => hcont hcl_m))
    (fun _ _ _ _ hnext => hnext)

/-- Re-establish `VerifiedLibraries.mallocngLib.CodeLoaded mpl sf.mem` at return (`target`) in an
    arbitrary-`oom` `SepWP` proof from `hcl : VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem`. -/
theorem sepWP_mono_cl {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post post' : State → SepProp → Prop} {oom : State → SepProp} {mpl : MultiPlacement}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem)
    (h : SepWP prog target s P post oom)
    (himp : ∀ sf Pf, sf.pc = target → sf.status = .Running →
      VerifiedLibraries.mallocngLib.CodeLoaded mpl sf.mem → post sf Pf → post' sf Pf) :
    SepWP prog target s P post' oom :=
  SepWP.mono_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcl h himp

@[simp] theorem externAt?_mallocngBlockProg (mpl : MultiPlacement) (i : Nat)
    (svc : State → State) (pc : BitVec 64) :
    (mallocngBlockProg mpl i svc).externAt? pc = none :=
  MultiPlacedLib.externAt?_blockProgram_none VerifiedLibraries.mallocngLib mpl i pc

private theorem codeLoaded_mallocngBlockProg {mpl : MultiPlacement} {j : Nat} {svc : State → State}
    {m : Memory} (h : (VerifiedLibraries.mallocngLib.blockProgram mpl j).CodeLoaded m) :
    (mallocngBlockProg mpl j svc).CodeLoaded m :=
  Program.CodeLoaded.of_base_code h rfl rfl

/-- Switch an arbitrary-`oom` `SepWP` goal from hook-free program `P` (with `P.svc = svc`) to
    `mallocngBlockProg mpl j svc` (`j < 24`) using `VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem`. -/
theorem sepWP_of_other_mallocng_block {P : Program} {mpl : MultiPlacement} {svc : State → State}
    {j : Nat} {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hj : j < 24) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem)
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = svc)
    (h : SepWP (mallocngBlockProg mpl j svc) target_pc s Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.of_sameHooks (P := P) (Q := mallocngBlockProg mpl j svc)
    (by intro pc; simp [hext pc])
    (by dsimp [mallocngBlockProg, MultiPlacedLib.blockProgram, PlacedLib.program]; exact hsvc.symm)
    (codeLoaded_mallocngBlockProg (hcl j hj)) h

/-- Transfer a `subroutine_ok` proved on block `j` (`j < 24`) with `withCL mpl spec` to any
    hook-free caller program `P` with `P.svc = svc` (including `mallocngBlockProg mpl i svc` and
    `(blkPC_XX.rebase (mbase i) (fun _ => none))`), enabling `wp_call` across blocks. -/
theorem subroutine_ok_block_to_block {α : Type} {P : Program} {mpl : MultiPlacement}
    {svc : State → State} {j : Nat} {entry : BitVec 64} {spec : Spec α}
    (hj : j < 24)
    (hcall : subroutine_ok (mallocngBlockProg mpl j svc) entry (withCL mpl spec))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = svc := by rfl)
    (h_no_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_no_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P entry (withCL mpl spec) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [withCL]
    rw [sepConj_comm (spec.pre x s0), sepConj_assoc]
    exact Entails.refl _
  rw [satisfies_pure_sepConj] at hpre'
  have hcl : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem := hpre'.1
  refine ⟨(withCL mpl spec).pre x s0, hpre, ?_⟩
  refine SepWP.call_subroutine_frame_other (F := emp)
    (P := P) (Q := mallocngBlockProg mpl j svc)
    hcall
    (by intro pc; simp [hext pc])
    (by dsimp [mallocngBlockProg, MultiPlacedLib.blockProgram, PlacedLib.program]; exact hsvc.symm)
    (codeLoaded_mallocngBlockProg (hcl j hj))
    hpc hrun hsp rfl
    (fun R' hm => by simpa [emp_sepConj] using hm)
    (fun R' sf _ hp => not_satisfies_false_sepConj (h_no_panic x s0 sf ▸ hp))
    (fun R' code sf _ he => not_satisfies_false_sepConj (h_no_exit x code s0 sf ▸ he))
    (fun sf hpc' hrun' hsp' hcs' _ =>
      SepWP.done hpc' hrun' ⟨fun hm => by simpa [sepConj_emp] using hm, hsp', hcs'⟩)
    (fun R' sf _ ho => by simpa [withCL, emp_sepConj] using ho)

/-- Lift any `subroutine_ok P entry spec` (proved without `withCL`, e.g. leaf blocks that make no
    cross-block calls) directly to `subroutine_ok P entry (withCL mpl spec)` via `sepWP_mono_cl`. -/
theorem subroutine_ok_withCL_of_subroutine_ok {α : Type} {P : Program} {mpl : MultiPlacement}
    {entry : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok P entry spec)
    (h_no_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_no_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P entry (withCL mpl spec) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [withCL]
    rw [sepConj_comm (spec.pre x s0), sepConj_assoc]
    exact Entails.refl _
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨hcl, hpre0⟩ := hpre'
  refine ⟨spec.pre x s0, hpre0, ?_⟩
  refine sepWP_mono_cl
    (post := fun sf Pf =>
      (sf.mem ⊨ Pf ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    hcl ?_ (fun sf Pf _ _ hcl_f ⟨hq, hsp', hcs'⟩ => ⟨fun hm => ?_, hsp', hcs'⟩)
  · refine SepWP.call_subroutine_frame (F := emp) hcall hpc hrun hsp rfl
      (fun R' hm => by simpa [emp_sepConj] using hm)
      (fun R' sf _ hp => by rw [h_no_panic x s0 sf] at hp; exact not_satisfies_false_sepConj hp)
      (fun R' code sf _ he => by rw [h_no_exit x code s0 sf] at he; exact not_satisfies_false_sepConj he)
      (fun sf hpc' hrun' hsp' hcs' =>
        SepWP.done hpc' hrun' ⟨fun hm => by simpa [sepConj_emp] using hm, hsp', hcs'⟩)
      (fun R' sf _ ho => by simpa [withCL, emp_sepConj] using ho)
  · refine Satisfies.mono ?_ (hq hm)
    dsimp only [withCL]
    rw [sepConj_assoc]
    exact sepConj_mono_right (Entails.pure_right hcl_f (Entails.refl R))

/-- Convenience wrapper combining `subroutine_ok_withCL_of_subroutine_ok` and
    `subroutine_ok_block_to_block` for leaf blocks `j < 24` proved without `withCL`. -/
theorem subroutine_ok_block_to_block_plain {α : Type} {P : Program} {mpl : MultiPlacement}
    {svc : State → State} {j : Nat} {entry : BitVec 64} {spec : Spec α}
    (hj : j < 24)
    (hcall : subroutine_ok (mallocngBlockProg mpl j svc) entry spec)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = svc := by rfl)
    (h_no_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_no_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P entry (withCL mpl spec) :=
  subroutine_ok_block_to_block hj
    (subroutine_ok_withCL_of_subroutine_ok hcall h_no_panic h_no_exit)
    hext hsvc h_no_panic h_no_exit

/-! ## Per-block rebase and relocation step rules -/

theorem blkProgram_rebase_self (lib : PlacedLib) (pl : Placement) (svc : State → State) :
    lib.program pl (fun _ => none) (fun _ => none) svc =
      (lib.program pl (fun _ => none) (fun _ => none) svc).rebase pl.base (fun _ => none) :=
  rfl

theorem blkProgram_rebase_fetch_svc (lib : PlacedLib) (pl : Placement) (svc : State → State)
    (b : BitVec 64) (X : String → Option (State → State)) (pc : BitVec 64) :
    ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b X).fetch pc =
      ((lib.program pl).rebase b X).fetch pc :=
  rfl

theorem blkProgram_rebase_hookAtOff_svc (lib : PlacedLib) (pl : Placement) (svc : State → State)
    (b : BitVec 64) (X : String → Option (State → State)) (off : Nat) :
    ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b X).hookAtOff? off =
      ((lib.program pl).rebase b X).hookAtOff? off :=
  rfl

theorem externAt?_placedProgram_rebase_none (lib : PlacedLib) (pl : Placement)
    (svc : State → State) (b : BitVec 64) (pc : BitVec 64) :
    ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b (fun _ => none)).externAt? pc = none := by
  dsimp only [Program.externAt?, Program.hookAtOff?, Program.rebase, PlacedLib.program]
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  simp only [ite_self, h0, Option.or_self]

/-- Relaxable `ADRP`+`ADD` pair rule for `(lib.program pl _ _ svc).rebase b X`. -/
theorem sepWP_blk_relaxablePair {lib : PlacedLib} {pl : Placement} {svc : State → State}
    {t : WordTree} {n : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hP : lib.Placeable pl)
    {b : BitVec 64} {X : String → Option (State → State)}
    {off off8 : Nat} {r : RelocEntry} {rd : BitVec 5} {v : BitVec 64}
    (hrel : lib.text.relaxableAt off = true)
    (hr : lib.text.relocAt? off = some r)
    (hrd : (lib.text.wordAt off).extractLsb' 0 5 = rd)
    (hrd31 : rd ≠ 31#5)
    (h8 : off + 8 = off8)
    (hlt0 : off < 4 * n) (hlt4 : off + 4 < 4 * n)
    (hb : b = pl.base)
    (hv : b = pl.base → lib.text.target pl r = v)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    (hnext : SepWP ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b X) tgt
      ((s.writeReg64 (.gpr rd) v).setPC (b + BitVec.ofNat 64 off8)) P post oom) :
    SepWP ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b X) tgt s P post oom := by
  have hv' := hv hb; clear hv; subst hb hv' h8
  have hh0 : ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase pl.base X).hookAtOff? off = none :=
    GenPlacedFetches.hookAtOff?_rebase_of_placeable (b := pl.base) (X := X) hcode hsize hP hlt0
  have hh4 : ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase pl.base X).hookAtOff? (off + 4) = none :=
    GenPlacedFetches.hookAtOff?_rebase_of_placeable (b := pl.base) (X := X) hcode hsize hP hlt4
  exact CodeBlock.sepWP_relaxablePair hP.text rfl rfl hrel hr hrd hrd31 hh0 hh4 hpc hrun hnext

/-- Plain `ADRP` rule for `(lib.program pl _ _ svc).rebase b X`. -/
theorem sepWP_blk_adrpPlain {lib : PlacedLib} {pl : Placement} {svc : State → State}
    {t : WordTree} {n : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hP : lib.Placeable pl)
    {b : BitVec 64} {X : String → Option (State → State)}
    {off off4 : Nat} {r : RelocEntry} {rd : BitVec 5} {w : BitVec 32} {T : BitVec 64}
    (hr : lib.text.relocAt? off = some r)
    (hk : r.kind = .adrpHi21)
    (hnrel : lib.text.relaxableAt off = false)
    (hwd : lib.text.wordAt off = w)
    (hw : w &&& 0x9f000000#32 = 0x90000000#32)
    (hrd : w.extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hT : lib.text.target pl r = T)
    (h4 : off + 4 = off4) (hlt0 : off < 4 * n)
    (hb : b = pl.base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    (hnext : SepWP ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b X) tgt
      ((s.writeReg64 (.gpr rd) (pageOf T)).setPC (b + BitVec.ofNat 64 off4)) P post oom) :
    SepWP ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b X) tgt s P post oom :=
  PlacedLib.sepWP_rebase_adrpPlain hP hb hr hk hnrel hwd hw hrd hrd31 hT h4
    (GenPlacedFetches.hookAtOff?_rebase_of_placeable (b := b) (X := X) hcode hsize hP hlt0) hpc hrun hnext

/-- Reducible abbreviation for `b = mbase idx` that is not syntactically an `Eq`, preventing
    `wp_steps`'s state simplifier from rewriting `b` in `b + off#64` PCs while allowing
    `tryPairStepHook` to discharge `b = mbase idx` by reducible `assumption`. -/
abbrev BlkBase (idx : Nat) [MallocngMultiPlacement] (b : BitVec 64) : Prop := b = mbase idx

theorem mbase_blk_of (idx : Nat) [MallocngMultiPlacement] : BlkBase idx (mbase idx) := rfl

/-- Lift a `subroutine_ok` proof quantified over `(b : BitVec 64) (hb : BlkBase idx b)` on
    `P.rebase b (fun _ => none)` (`P = blkPC_bXX`) to `mallocngBlockProg mmpl idx msvc`. -/
theorem mallocngBlock_subOk [MallocngMultiPlacement] {α : Type} {P : Program}
    {idx : Nat} {name : String} {spec : Spec α}
    (hprog : mallocngBlockProg mmpl idx msvc = P.rebase (mbase idx) (fun _ => none))
    (hfn : (P.rebase (mbase idx) (fun _ => none)).fnAddr name = mbase idx)
    (h : ∀ (b : BitVec 64), BlkBase idx b →
      subroutine_ok (P.rebase b (fun _ => none))
        ((P.rebase b (fun _ => none)).fnAddr name) spec) :
    subroutine_ok (mallocngBlockProg mmpl idx msvc) (mbase idx) spec := by
  have h0 := h (mbase idx) rfl
  rwa [hfn, ← hprog] at h0

end VerifiedLibraries.Mallocng.Proofs
