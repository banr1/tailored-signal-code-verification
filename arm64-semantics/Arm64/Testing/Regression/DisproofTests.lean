/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Disproof

/-!
# Machine-Code Disproof Regression Tests

End-to-end counterexample proofs using `ProofLib.Disproof` (`ReachesException`, strict external
hooks, caller-framed canary bytes, and `.Panicked` termination) to refute underspecified
`safe_subroutine_ok` and `subroutine_ok` contracts on synthetic AArch64 programs.
-/

@[expose] public section

namespace Arm64.Testing.DisproofTests

open Arm64
open ProofLib
open ProofLib.Disproof

/-! ## Out-of-bounds store fault -/

section OobStoreFault

abbrev oobEntry : BitVec 64 := 0x10000#64
abbrev oobBuf : BitVec 64 := 0x30000#64

/-- Machine code for `oob_write`: `add x8, x0, x1; strb w2, [x8]; ret`. -/
def oobProg : Program :=
  { base := oobEntry
    code := [
      0x08#8, 0x00#8, 0x01#8, 0x8b#8,
      0x02#8, 0x01#8, 0x00#8, 0x39#8,
      0xc0#8, 0x03#8, 0x5f#8, 0xd6#8
    ] }

/-- Specification for `oob_write(buf, idx, val)` that omits the index bound `idx < 4`. -/
def naiveOobWriteSpec : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (buf, bs) s =>
    ⌜s.readReg64 .x0 = buf ∧ bs.length = 4⌝ ∗ (buf ↦ₛ bs)
  post := fun (buf, _) _ _ =>
    memRegion buf 4

def oobRegions : List DisproofRegion :=
  [.rwBytes oobBuf [1#8, 2#8, 3#8, 4#8]]

def oobS0 : State :=
  mkDisproofState oobProg oobEntry
    (regs := [(.x0, oobBuf), (.x1, 4#64), (.x2, 0x42#64)])
    (rs := oobRegions)

theorem oobS0_reachesException : ReachesException oobProg oobS0 := by
  have hcode : oobProg.CodeLoaded oobS0.mem :=
    mkDisproofState_codeLoaded oobProg oobEntry
      (regs := [(.x0, oobBuf), (.x1, 4#64), (.x2, 0x42#64)]) (rs := oobRegions)
  refine ReachesException.of_exec_step (hcode := hcode) (hrest := fun hcode1 => ?_)
  have hunmap : oobS0.mem.perm (oobBuf + 4#64) = none :=
    mkDisproofState_perm_none oobProg oobEntry (oobBuf + 4#64)
      (regs := [(.x0, oobBuf), (.x1, 4#64), (.x2, 0x42#64)])
      (rs := oobRegions)
  exact ReachesException.of_store_unmapped_at (hcode := hcode1) (hperm := by rw [hunmap])

theorem oob_write_not_safe_subroutine_ok :
    ¬ safe_subroutine_ok oobProg oobEntry naiveOobWriteSpec := by
  have hsat_raw := mkDisproofState_satisfies oobProg oobEntry
    (regs := [(.x0, oobBuf), (.x1, 4#64), (.x2, 0x42#64)])
    (rs := oobRegions)
  have hpre : oobS0.mem ⊨ naiveOobWriteSpec.pre (oobBuf, [1#8, 2#8, 3#8, 4#8]) oobS0 ∗ SepProp.emp := by
    rw [sepConj_emp]
    unfold naiveOobWriteSpec
    rw [satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl⟩, hsat_raw⟩
  exact oobS0_reachesException.not_safe_subroutine_ok
    (oobBuf, [1#8, 2#8, 3#8, 4#8]) SepProp.emp
    (mkDisproofState_aapcsEntry oobProg oobEntry (regs := [(.x0, oobBuf), (.x1, 4#64), (.x2, 0x42#64)]) (rs := oobRegions))
    (mkDisproofState_codeLoaded oobProg oobEntry (regs := [(.x0, oobBuf), (.x1, 4#64), (.x2, 0x42#64)]) (rs := oobRegions))
    hpre

theorem oob_write_not_subroutine_ok :
    ¬ subroutine_ok oobProg oobEntry naiveOobWriteSpec :=
  fun h => oob_write_not_safe_subroutine_ok h.to_safe

end OobStoreFault

/-! ## Unchecked OOM `NULL` passed to `memcpy` -/

section UncheckedOomToMemcpy

abbrev allocCopyEntry : BitVec 64 := 0x10000#64
abbrev mallocStubOff  : Nat       := 0x10000
abbrev memcpyStubOff  : Nat       := 0x10004
abbrev srcBuf         : BitVec 64 := 0x40000#64

/-- Machine code for `alloc_and_copy`: calls `malloc`, computes `dst + 8` without checking for
    `NULL`, and calls `memcpy(dst + 8, src, 8)`. -/
def allocCopyProg (mallocHook memcpyHook : State → State) : Program :=
  { base := allocCopyEntry
    code := [
      0x00#8, 0x40#8, 0x00#8, 0x94#8,
      0x00#8, 0x20#8, 0x00#8, 0x91#8,
      0xe1#8, 0x03#8, 0x13#8, 0xaa#8,
      0x02#8, 0x01#8, 0x80#8, 0xd2#8,
      0xfd#8, 0x3f#8, 0x00#8, 0x94#8,
      0xc0#8, 0x03#8, 0x5f#8, 0xd6#8
    ]
    stubs := [("malloc", mallocStubOff), ("memcpy", memcpyStubOff)]
    externs := fun name =>
      if name == "malloc" then some mallocHook
      else if name == "memcpy" then some memcpyHook
      else none }

theorem allocCopyHooks_lawful :
    HookOk hookAllocNull oomMallocRegionSpec ∧
    HookOk strictMemcpyRegionHook memcpyRegionSpec :=
  ⟨hookAllocNull_oomMallocRegion_ok, strictMemcpyRegionHook_ok⟩

def naiveAllocCopySpec : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (src, bs) s =>
    ⌜s.readReg64 .x0 = 16#64 ∧ s.readReg64 .x19 = src ∧ bs.length = 8⌝ ∗ (src ↦ₛ bs)
  post := fun (src, bs) _ _ =>
    src ↦ₛ bs

def allocCopyRegions : List DisproofRegion :=
  [.rwBytes srcBuf [10#8, 20#8, 30#8, 40#8, 50#8, 60#8, 70#8, 80#8]]

noncomputable def allocCopyTestProg : Program :=
  allocCopyProg hookAllocNull strictMemcpyRegionHook

noncomputable def allocCopyS0 : State :=
  mkDisproofState allocCopyTestProg allocCopyEntry
    (regs := [(.x0, 16#64), (.x19, srcBuf)])
    (rs := allocCopyRegions)

theorem allocCopyS0_reachesException : ReachesException allocCopyTestProg allocCopyS0 := by
  have hcode : allocCopyTestProg.CodeLoaded allocCopyS0.mem :=
    mkDisproofState_codeLoaded allocCopyTestProg allocCopyEntry
      (regs := [(.x0, 16#64), (.x19, srcBuf)]) (rs := allocCopyRegions)
  refine ReachesException.of_exec_step (hcode := hcode) (hrest := fun hcode1 => ?_)
  refine ReachesException.of_extern_step (hrest := ?_)
  refine ReachesException.of_exec_step (hcode := hcode1) (hrest := fun hcode2 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode2) (hrest := fun hcode3 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode3) (hrest := fun hcode4 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode4) (hrest := fun _ => ?_)
  have hunmap : allocCopyS0.mem.perm 8#64 = none :=
    mkDisproofState_perm_none allocCopyTestProg allocCopyEntry 8#64
      (regs := [(.x0, 16#64), (.x19, srcBuf)])
      (rs := allocCopyRegions)
  have hnot_rw : allocCopyS0.mem.perm 8#64 ≠ some Perm.rw := by
    rw [hunmap]; decide
  exact ReachesException.of_strict_hook_call
    (hinvalid := not_validHookCall_memcpyRegion_of_dst_not_rw (hnot_rw := hnot_rw))

theorem alloc_copy_not_safe_subroutine_ok :
    ¬ safe_subroutine_ok allocCopyTestProg allocCopyEntry naiveAllocCopySpec := by
  have hsat_raw := mkDisproofState_satisfies allocCopyTestProg allocCopyEntry
    (regs := [(.x0, 16#64), (.x19, srcBuf)]) (rs := allocCopyRegions)
  have hpre : allocCopyS0.mem ⊨
      naiveAllocCopySpec.pre (srcBuf, [10#8, 20#8, 30#8, 40#8, 50#8, 60#8, 70#8, 80#8]) allocCopyS0 ∗ SepProp.emp := by
    rw [sepConj_emp]
    unfold naiveAllocCopySpec
    rw [satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl, rfl⟩, hsat_raw⟩
  exact allocCopyS0_reachesException.not_safe_subroutine_ok
    (srcBuf, [10#8, 20#8, 30#8, 40#8, 50#8, 60#8, 70#8, 80#8]) SepProp.emp
    (mkDisproofState_aapcsEntry allocCopyTestProg allocCopyEntry
      (regs := [(.x0, 16#64), (.x19, srcBuf)]) (rs := allocCopyRegions))
    (mkDisproofState_codeLoaded allocCopyTestProg allocCopyEntry
      (regs := [(.x0, 16#64), (.x19, srcBuf)]) (rs := allocCopyRegions))
    hpre

theorem alloc_copy_not_subroutine_ok :
    ¬ subroutine_ok allocCopyTestProg allocCopyEntry naiveAllocCopySpec :=
  fun h => alloc_copy_not_safe_subroutine_ok h.to_safe

end UncheckedOomToMemcpy

/-! ## Adjacent-buffer canary corruption -/

section AdjacentCanaryCorruption

abbrev canaryEntry : BitVec 64 := 0x10000#64
abbrev canaryBuf   : BitVec 64 := 0x30000#64
abbrev canaryAddr  : BitVec 64 := 0x30004#64

/-- Machine code for `overwrite_past_end`: `strb w1, [x0, #4]; ret`. -/
def canaryProg : Program :=
  { base := canaryEntry
    code := [
      0x01#8, 0x10#8, 0x00#8, 0x39#8,
      0xc0#8, 0x03#8, 0x5f#8, 0xd6#8
    ] }

def naiveCanarySpec : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (buf, bs) s =>
    ⌜s.readReg64 .x0 = buf ∧ bs.length = 4⌝ ∗ (buf ↦ₛ bs)
  post := fun (buf, _) _ _ =>
    memRegion buf 4

/-- Maps both `[0x30000, 0x30004)` and the adjacent caller-framed canary byte `0x30004` as `Perm.rw`
    so `strb w1, [x0, #4]` returns `.Halted` after modifying the framed byte. -/
def canaryRegions : List DisproofRegion :=
  [.rwBytes canaryBuf [1#8, 2#8, 3#8, 4#8], .rw8 canaryAddr 0xAA#8]

def canaryS0 : State :=
  mkDisproofState canaryProg canaryEntry
    (regs := [(.x0, canaryBuf), (.x1, 0xFF#64)])
    (rs := canaryRegions)

theorem canary_overwrite_not_subroutine_ok :
    ¬ subroutine_ok canaryProg canaryEntry naiveCanarySpec := by
  have hcode : canaryProg.CodeLoaded canaryS0.mem :=
    mkDisproofState_codeLoaded canaryProg canaryEntry
      (regs := [(.x0, canaryBuf), (.x1, 0xFF#64)]) (rs := canaryRegions)
  have hsat_raw := mkDisproofState_satisfies canaryProg canaryEntry
    (regs := [(.x0, canaryBuf), (.x1, 0xFF#64)]) (rs := canaryRegions)
  have hpre : canaryS0.mem ⊨
      naiveCanarySpec.pre (canaryBuf, [1#8, 2#8, 3#8, 4#8]) canaryS0 ∗ ((canaryAddr ↦₈ 0xAA#8) ∗ SepProp.emp) := by
    dsimp only [naiveCanarySpec]
    rw [sepConj_emp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl⟩, hsat_raw⟩
  let sf := ProofLib.stepInst canaryProg (ProofLib.stepInst canaryProg canaryS0)
  have hsteps : Steps canaryProg canaryS0 sf :=
    Steps.of_exec_step (hcode := hcode) (hrest := fun hcode1 =>
      Steps.of_exec_step (hcode := hcode1) (hrest := fun _ =>
        Steps.refl sf))
  exact not_subroutine_ok_of_frame_canary
    (canaryBuf, [1#8, 2#8, 3#8, 4#8]) SepProp.emp
    (mkDisproofState_aapcsEntry canaryProg canaryEntry
      (regs := [(.x0, canaryBuf), (.x1, 0xFF#64)]) (rs := canaryRegions))
    hcode hpre hsteps ⟨rfl, rfl, rfl⟩ (v1 := 0xFF#8) rfl (by decide)

end AdjacentCanaryCorruption

/-! ## Compiled C `assert(x != 0)` failure -/

section CompiledAssertNonzero

set_option maxRecDepth 20000

abbrev assertEntry     : BitVec 64 := 0x1004c#64
abbrev assertStubOff   : Nat       := 0xa4
abbrev assertStackBase : BitVec 64 := 0x30000#64
abbrev assertSp0       : BitVec 64 := 0x30010#64

def assertRegions : List DisproofRegion :=
  [.rwRegion assertStackBase 16]

/-- 12-instruction `assert_nonzero` sequence (`cbz x0, +8; ret; stp x29, x30, [sp, #-0x10]!;
    adrp/add ...; mov w2, #45; mov x29, sp; bl __assert_fail`). -/
def assertNonzeroWords : List (BitVec 32) :=
  [0xb4000040, 0xd65f03c0, 0xa9bf7bfd, 0xb0000000, 0x91006800, 0xb0000001,
   0x91003c21, 0xb0000003, 0x91000063, 0x528005a2, 0x910003fd, 0x9400001e]

/-- Contract for `assert_nonzero(x)` that supplies the 16-byte stack frame `[sp0 - 16, sp0)`
    but omits `x ≠ 0`. -/
c_spec naiveAssertNonzeroSpec (x : u64) (ghost sp0 : ptr)
  requires_cond s0.sp = sp0
  requires memRegion (sp0 - 16#64) 16
  ensures  memRegion (sp0 - 16#64) 16

def mkAssertProg (h : State → State) : Program :=
  { Program.ofWords assertEntry assertNonzeroWords with
    stubs := [("__assert_fail", assertStubOff)]
    externs := fun name => if name == "__assert_fail" then some h else none }

def assertAbortProg : Program :=
  mkAssertProg (fun s => { s with status := .Exception "__assert_fail" })

def assertAbortS0 : State :=
  mkDisproofState assertAbortProg assertEntry
    (sp0 := assertSp0)
    (regs := [(.x0, 0#64)])
    (rs := assertRegions)

theorem assertAbortS0_reachesException : ReachesException assertAbortProg assertAbortS0 := by
  have hcode : assertAbortProg.CodeLoaded assertAbortS0.mem :=
    mkDisproofState_codeLoaded assertAbortProg assertEntry
      (sp0 := assertSp0) (regs := [(.x0, 0#64)]) (rs := assertRegions)
  refine ReachesException.of_exec_step (hcode := hcode) (hrest := fun hcode1 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode1) (hrest := fun hcode2 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode2) (hrest := fun hcode3 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode3) (hrest := fun hcode4 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode4) (hrest := fun hcode5 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode5) (hrest := fun hcode6 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode6) (hrest := fun hcode7 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode7) (hrest := fun hcode8 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode8) (hrest := fun hcode9 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode9) (hrest := fun hcode10 => ?_)
  refine ReachesException.of_exec_step (hcode := hcode10) (hrest := fun _ => ?_)
  refine ReachesException.of_extern_step (hrest := ?_)
  exact ReachesException.of_exception rfl

theorem assert_nonzero_abort_not_safe_subroutine_ok :
    ¬ safe_subroutine_ok assertAbortProg assertEntry naiveAssertNonzeroSpec := by
  have hsat_raw := mkDisproofState_satisfies assertAbortProg assertEntry
    (sp0 := assertSp0) (regs := [(.x0, 0#64)]) (rs := assertRegions)
  have hpre : assertAbortS0.mem ⊨
      naiveAssertNonzeroSpec.pre (0#64, assertSp0) assertAbortS0 ∗ SepProp.emp := by
    rw [sepConj_emp]
    unfold naiveAssertNonzeroSpec
    rw [satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl⟩, hsat_raw⟩
  exact assertAbortS0_reachesException.not_safe_subroutine_ok
    (0#64, assertSp0) SepProp.emp
    (mkDisproofState_aapcsEntry assertAbortProg assertEntry
      (sp0 := assertSp0) (regs := [(.x0, 0#64)]) (rs := assertRegions))
    (mkDisproofState_codeLoaded assertAbortProg assertEntry
      (sp0 := assertSp0) (regs := [(.x0, 0#64)]) (rs := assertRegions))
    hpre

theorem assert_nonzero_abort_not_subroutine_ok :
    ¬ subroutine_ok assertAbortProg assertEntry naiveAssertNonzeroSpec :=
  fun h => assert_nonzero_abort_not_safe_subroutine_ok h.to_safe

/-- Execution of `prog` starting from state `s` reaches a terminal `.Panicked` state. -/
def ReachesPanicked (prog : Program) (s : State) : Prop :=
  ∃ sf, Steps prog s sf ∧ sf.status = .Panicked

theorem ReachesPanicked.of_exec_step {prog : Program} {s : State}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hcode : prog.CodeLoaded s.mem)
    (hsome : (prog.fetch s.pc).isSome = true := by with_unfolding_all decide)
    (hrest : prog.CodeLoaded (ProofLib.stepInst prog s).mem →
      ReachesPanicked prog (ProofLib.stepInst prog s)) :
    ReachesPanicked prog s := by
  obtain ⟨sf, hsteps, hpan⟩ := hrest (Program.CodeLoaded.stepInst hcode)
  rw [stepInst_eq_execInst_fetchInstD hsome] at hsteps
  exact ⟨sf, .step (Step.exec hrun (Program.fetchMem_of_fetch hcode (fetch_eq_some_fetchInstD hsome))) hsteps, hpan⟩

theorem ReachesPanicked.of_extern_panic {prog : Program} {s : State} {hook : State → State}
    (hrun : s.status = .Running := by with_unfolding_all rfl)
    (hextern : prog.externAt? s.pc = some hook := by with_unfolding_all rfl)
    (hkeep : s.mem.KeepsFrozen (hook s).mem := by exact Memory.KeepsFrozen.refl _)
    (hsym : (hook s).symtab = s.symtab := by with_unfolding_all rfl)
    (hpan : (hook s).status = .Panicked := by with_unfolding_all rfl) :
    ReachesPanicked prog s :=
  ⟨hook s, .step (Step.extern hrun hextern hkeep hsym) (.refl _), hpan⟩

def assertPanicProg : Program :=
  mkAssertProg Rust.panicked

def assertPanicS0 : State :=
  mkDisproofState assertPanicProg assertEntry
    (sp0 := assertSp0)
    (regs := [(.x0, 0#64)])
    (rs := assertRegions)

theorem assert_nonzero_panic_not_subroutine_ok :
    ¬ subroutine_ok assertPanicProg assertEntry naiveAssertNonzeroSpec := by
  have hcode : assertPanicProg.CodeLoaded assertPanicS0.mem :=
    mkDisproofState_codeLoaded assertPanicProg assertEntry
      (sp0 := assertSp0) (regs := [(.x0, 0#64)]) (rs := assertRegions)
  have hsat_raw := mkDisproofState_satisfies assertPanicProg assertEntry
    (sp0 := assertSp0) (regs := [(.x0, 0#64)]) (rs := assertRegions)
  have hpre : assertPanicS0.mem ⊨
      naiveAssertNonzeroSpec.pre (0#64, assertSp0) assertPanicS0 ∗ SepProp.emp := by
    rw [sepConj_emp]
    unfold naiveAssertNonzeroSpec
    rw [satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl⟩, hsat_raw⟩
  have ⟨sf, hsteps, hpan⟩ : ReachesPanicked assertPanicProg assertPanicS0 := by
    refine ReachesPanicked.of_exec_step (hcode := hcode) (hrest := fun hcode1 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode1) (hrest := fun hcode2 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode2) (hrest := fun hcode3 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode3) (hrest := fun hcode4 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode4) (hrest := fun hcode5 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode5) (hrest := fun hcode6 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode6) (hrest := fun hcode7 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode7) (hrest := fun hcode8 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode8) (hrest := fun hcode9 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode9) (hrest := fun hcode10 => ?_)
    refine ReachesPanicked.of_exec_step (hcode := hcode10) (hrest := fun _ => ?_)
    exact ReachesPanicked.of_extern_panic
  have honpanic_false :
      ¬ (sf.mem ⊨ naiveAssertNonzeroSpec.onPanic (0#64, assertSp0) assertPanicS0 sf ∗ SepProp.emp) := by
    rw [sepConj_emp]
    intro h
    simp [naiveAssertNonzeroSpec] at h
  exact not_subroutine_ok_of_panic_post_false
    (0#64, assertSp0) SepProp.emp
    (mkDisproofState_aapcsEntry assertPanicProg assertEntry
      (sp0 := assertSp0) (regs := [(.x0, 0#64)]) (rs := assertRegions))
    hcode hpre hsteps hpan honpanic_false

end CompiledAssertNonzero

end Arm64.Testing.DisproofTests
