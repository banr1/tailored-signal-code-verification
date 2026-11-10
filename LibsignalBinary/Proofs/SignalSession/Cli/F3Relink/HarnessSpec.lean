/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top

/-!
# Normal-Return `libc.need_locks` Exit-Seam Harness Specification

Defines `MuslHarnessNeedLocksN`, the startup/exit harness predicate that hands
`((libcAddr + 3#64) ↦₈ 0#8)` (`__libc.need_locks = 0`) into `MainPre` at `main` entry and accepts
it back alongside `stackAt sm.sp stkRet` on normal `main` return before `musl`'s `exit`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.HarnessSpec

open Arm64 Arm64.Process ProofLib
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (ElfStaticOk cliInputs)

/-- `MuslHarness` variant parameterized by return-stack headroom `stkRet` and `libcAddr`
(`__libc`), receiving `((libcAddr + 3#64) ↦₈ 0#8)` back on normal `main` return. -/
def MuslHarnessNeedLocksN (stkRet : Nat) (libcAddr : BitVec 64)
    (elf : ElfImage) (P : Program) (mainPc : BitVec 64) (Fr : SepProp)
    (Ok : Inputs → Prop) (MainPre : Inputs → State → SepProp) : Prop :=
  ElfStaticOk elf → ∀ i, Ok i → ∃ s0 sm,
    elf.loadState (cliInputs i) = .ok s0 ∧ Steps P s0 sm ∧
    sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
    sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
    (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
    (sm.mem ⊨ MainPre i sm ∗ Fr) ∧
    ∀ sr, Steps P sm sr → Returned sm sr →
      (sr.mem ⊨ stackAt sm.sp stkRet ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗ Fr ∗ anyHeap) →
      ∃ sx, Steps P sr sx ∧
        sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
        sx.fs = sr.fs ∧ sx.trace = sr.trace

/-- Rearrange `((nl ↦₈ 0#8) ∗ stackAt sp stk ∗ anyHeap) ∗ Fr` (`n ≤ stk`) into the return-frame
    order `stackAt sp n ∗ (nl ↦₈ 0#8) ∗ Fr ∗ anyHeap` expected by `MuslHarnessNeedLocksN`. -/
theorem exit_frame_needLocks_n {m : Memory} {nl sp : BitVec 64} {n stk : Nat} {Fr : SepProp}
    (hstk : n ≤ stk) (_hstk' : stk ≤ 2 ^ 64)
    (h : m ⊨ ((nl ↦₈ 0#8) ∗ stackAt sp stk ∗ anyHeap) ∗ Fr) :
    m ⊨ stackAt sp n ∗ (nl ↦₈ 0#8) ∗ Fr ∗ anyHeap := by
  have hsplit := stackAt_split_bottom sp n (stk - n) (by omega)
  rw [show n + (stk - n) = stk by omega] at hsplit
  rw [hsplit] at h
  refine Satisfies.mono ?_ h
  have hEq :
      (((nl ↦₈ 0#8) ∗ (memRegion (sp - BitVec.ofNat 64 stk) (stk - n) ∗ stackAt sp n) ∗
        anyHeap) ∗ Fr) =
      stackAt sp n ∗ (nl ↦₈ 0#8) ∗ Fr ∗
        (memRegion (sp - BitVec.ofNat 64 stk) (stk - n) ∗ anyHeap) := by
    sep_ac_rfl
  rw [hEq]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))

theorem exit_frame_stack_needLocks_n {m : Memory} {nl sp : BitVec 64} {n stk : Nat} {Fr : SepProp}
    (hstk : n ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (h : m ⊨ (stackAt sp stk ∗ (nl ↦₈ 0#8) ∗ anyHeap) ∗ Fr) :
    m ⊨ stackAt sp n ∗ (nl ↦₈ 0#8) ∗ Fr ∗ anyHeap := by
  have hEq :
      (stackAt sp stk ∗ (nl ↦₈ 0#8) ∗ anyHeap) ∗ Fr =
      ((nl ↦₈ 0#8) ∗ stackAt sp stk ∗ anyHeap) ∗ Fr := by
    sep_ac_rfl
  rw [hEq] at h
  exact exit_frame_needLocks_n hstk hstk' h

end LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.HarnessSpec
