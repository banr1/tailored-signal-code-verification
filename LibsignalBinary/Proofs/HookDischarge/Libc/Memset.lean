/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.MemsetProof
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common

/-!
# Byte-exact `memset` hook discharge

Discharges the `signal-session` CLI's `memset` call-site contracts (`ProofLib.libcMemsetSpec`,
`ProofLib.memsetRegionSpec`, `sessionMemsetRegionSpec`, `sessionMemsetSpec`) against the 65-word
`musl` `memset` implementation `VerifiedLibraries.Musl.memsetWords`.

Note on SIMD caller-saved state (`DEV-E1`, `Computational/docs/DEVIATIONS.md`): `musl` `memset`
clobbers `v0` via `dup v0.16b, w1`, which is permitted under `CallingConventionPreserved` / `DEV-E1`
since `CalleeSavedVRegsPreserved` preserves only `D8..D15`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Libc.Memset

open Arm64 ProofLib
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open VerifiedLibraries.Musl (memsetWords memsetSpec memset_codeAt_ok libcMemset_ok_of_memset_ok)
open CryptoVerification.LibsignalTripleRatchet (sessionMemsetSpec sessionMemsetRegionSpec extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack subroutine_ok_drop_keepsFs
  subroutine_ok_withStack_keepsFs)

/-! ## `hasWords` and opcode-exclusion witnesses -/

private theorem pureWordsProg_hasWords_memset (entry : BitVec 64) :
    (pureWordsProg entry memsetWords).hasWords entry memsetWords :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range memsetWords.length).all fun i =>
      (pureWordsProg 0#64 memsetWords).readWordOff (4 * i) == memsetWords[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_memset (entry : BitVec 64) :
    (pureWordsProg entry memsetWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 memsetWords) rfl (by prove_all_instrs)

/-! ## `ProofLib` contracts -/

/-- Exact `libc.a` `memset` bytes satisfy `ProofLib.libcMemsetSpec hookStack`. -/
theorem memset_libcMemsetSpec_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasWords entry memsetWords) :
    subroutine_ok prog entry (ProofLib.libcMemsetSpec hookStack) :=
  libcMemset_ok_of_memset_ok hookStack (memset_codeAt_ok prog entry hc)

/-- Exact `libc.a` `memset` bytes satisfy `ProofLib.memsetRegionSpec`. -/
theorem memset_memsetRegionSpec_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry memsetWords) :
    subroutine_ok prog entry ProofLib.memsetRegionSpec := by
  refine subroutine_ok_map (memset_codeAt_ok prog entry hc) ?_
  rintro ⟨ptr, c, len⟩ R s0 hpre
  dsimp only [ProofLib.memsetRegionSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, _hlen⟩, hmem⟩ := hpre
  refine ⟨(ptr, s0.readReg32 .x1, s0.readReg64 .x2), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memsetSpec, CType.MutSlice8, CType.Bytes, CType.U32, CType.SizeT,
      CType.scalarTy, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, hx2]
    exact ⟨⟨hx0, trivial⟩, Satisfies.of_eq hmem⟩
  · dsimp only [memsetSpec, CType.MutSlice8, CType.Bytes] at hpost
    dsimp only [ProofLib.memsetRegionSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and] at hpost ⊢
    have hc_eq : (s0.readReg32 .x1).setWidth 8 = c := hx1
    rw [hx2, hc_eq] at hpost
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

/-! ## Process-preserving CLI contracts (`sf.trace = s0.trace` and `sf.fs = s0.fs`) -/

/-- Exact `libc.a` `memset` bytes satisfy `keepsFs (ProofLib.libcMemsetSpec hookStack)` on any
    hook-free program (`AllocContractsFs.memset`). -/
theorem memset_libcMemsetSpec_keepsFs_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasWords entry memsetWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog entry (keepsFs (ProofLib.libcMemsetSpec hookStack)) := by
  have hpure := memset_libcMemsetSpec_ok hookStack (pureWordsProg_hasWords_memset entry)
  have hlift := subroutine_ok_lift_pureWords_process hpure (pureWordsProg_noSvcMsr_memset entry)
    hc h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)
  refine subroutine_ok_map hlift fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩
  dsimp only [keepsFs] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.2⟩

/-- Exact `libc.a` `memset` bytes satisfy `keepsFs sessionMemsetRegionSpec` on any hook-free program. -/
theorem memset_sessionMemsetRegionSpec_keepsFs_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry memsetWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog entry (keepsFs sessionMemsetRegionSpec) := by
  have hpure := memset_memsetRegionSpec_ok (pureWordsProg_hasWords_memset entry)
  have hlift := subroutine_ok_lift_pureWords_process hpure (pureWordsProg_noSvcMsr_memset entry)
    hc h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)
  refine subroutine_ok_map hlift fun ⟨ptr, c, len⟩ R s0 hpre => ⟨(ptr, c, len), R, hpre, fun sf hpost => ?_⟩
  dsimp only [keepsFs, sessionMemsetRegionSpec, ProofLib.memsetRegionSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, ⟨hpost.2.1, hpost.1.2.1⟩, hpost.2.2⟩

/-- Exact `libc.a` `memset` bytes satisfy `sessionMemsetRegionSpec` on any hook-free program. -/
theorem memset_sessionMemsetRegionSpec_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry memsetWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog entry sessionMemsetRegionSpec :=
  subroutine_ok_drop_keepsFs (memset_sessionMemsetRegionSpec_keepsFs_ok hc h_no_ext)

/-- Exact `libc.a` `memset` bytes satisfy `keepsFs (sessionMemsetSpec hookStack)` on any hook-free
program (`sessionMemsetSpec 4096 = CliExt.memsetSpec`). -/
theorem memset_sessionMemsetSpec_keepsFs_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasWords entry memsetWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog entry (keepsFs (sessionMemsetSpec hookStack)) := by
  have hpure := memset_libcMemsetSpec_ok hookStack (pureWordsProg_hasWords_memset entry)
  have hlift := subroutine_ok_lift_pureWords_process hpure (pureWordsProg_noSvcMsr_memset entry)
    hc h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)
  refine subroutine_ok_map hlift fun ⟨ptr, c, len⟩ R s0 hpre => ⟨(ptr, c, len), R, hpre, fun sf hpost => ?_⟩
  dsimp only [keepsFs, sessionMemsetSpec, ProofLib.libcMemsetSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, ⟨hpost.2.1, hpost.1.2.1⟩, hpost.2.2⟩

/-- Exact `libc.a` `memset` bytes satisfy `sessionMemsetSpec hookStack` on any hook-free program. -/
theorem memset_sessionMemsetSpec_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasWords entry memsetWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog entry (sessionMemsetSpec hookStack) :=
  subroutine_ok_drop_keepsFs (memset_sessionMemsetSpec_keepsFs_ok hookStack hc h_no_ext)

end LibsignalBinary.Proofs.HookDischarge.Libc.Memset
