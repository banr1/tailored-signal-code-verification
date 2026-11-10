/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
import ProofLib.SepLogic.WPFrozen

/-!
# External Stub Contracts at `externStack = 2^14` and Caller-Block Transport

Restates the external stub contracts in frozen `externsLib` shapes owning `stackAt s.sp externStack`
(`externStack = 16384`), defines the stacked read-only-source `memcpy` contract
`sessionMemcpyROXSpec` (`src ↦ᵣ bs`), and proves caller-block-polymorphic `[LibsignalPlacement]`
hook and subroutine transfer lemmas (`ls_hook_ok_of_caller`, `ls_subroutine_ok_cl_of_callee`,
`ls_subroutine_ok_of_callee`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib

/-! ## Stacked read-only-source `memcpy` -/

/-- `memcpy(dst = x0, src = x1, len = x2)` from a read-only source `src ↦ᵣ bs`, owning
`externStack` bytes of stack and preserving the trace (`(dst, src, bs)`). -/
def sessionMemcpyROXSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack

/-! ## Relocatable `[LibsignalPlacement]` caller-block transport -/

section Placed
set_option autoImplicit false
set_option maxRecDepth 2000000

/-- `IsLsBlockProg` instance for `lsBlkProg lsmpl 0 H` (`libsignalSessionLib.blockProgram lsmpl 0 H`). -/
instance instIsLsBlockProg_lsBlkProg0 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (lsBlkProg lsmpl 0 H) 0 H where
  eq_blockProgram := rfl
  externs_eq := rfl

/-- Look up an external hook `sym ∈ libsignalSessionExterns` in any caller block program `prog`
without requiring `i < 619` on the caller block index `i`. -/
theorem ls_externAt?_of_caller [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  have heq : prog.externAt? (lsρ sym) = (lsBlkProg lsmpl 0 H).externAt? (lsρ sym) := by
    rw [hprog.eq_blockProgram]
    exact congrFun
      (ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hprog.externs_eq.trans (rfl : (libsignalSessionLib.blockLib 0).text.externs = libsignalSessionExterns).symm))
      (lsρ sym)
  exact heq.trans (ls_externAt?_of_mem (prog := lsBlkProg lsmpl 0 H) hmem)

/-- Lift `HookSat H sym spec` to `subroutine_ok prog (lsρ sym) spec` for any caller block program
`prog` without requiring `i < 619`. -/
theorem ls_hook_ok_of_caller [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_of_caller hmem).trans hf) hok

/-- Strengthen `withLsCodeLoaded pl spec` to `withLsCl pl spec` using `Steps.keepsFrozen`. -/
theorem ls_subroutine_ok_cl_of_withLsCodeLoaded {α : Type} {prog : Program} {addr : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeLoaded pl spec)) :
    subroutine_ok prog addr (withLsCl pl spec) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨sf, hsteps, hout, -⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre hsp hL
  have hclf : LibsignalCodeLoaded pl sf.mem := hcl0.of_keepsFrozen hsteps.keepsFrozen
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hclf, hpost⟩
  · exact Or.inr hrest

/-- Strengthen plain `subroutine_ok prog addr spec` to `withLsCl pl spec`. -/
theorem ls_subroutine_ok_cl_of_plain_prog {α : Type} {prog : Program} {addr : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog addr spec) :
    subroutine_ok prog addr (withLsCl pl spec) :=
  ls_subroutine_ok_cl_of_withLsCodeLoaded (subroutine_ok_withLsCodeLoaded_of_plain h)

/-- Transfer `subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec)` from block `j` to any
caller block `i`'s `callerProg` (in `withLsCl` form), without requiring `i < 619`. -/
theorem ls_subroutine_ok_cl_of_callee [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hclf : LibsignalCodeLoaded lsmpl sf.mem := hcl0.of_keepsFrozen hstepsQ.keepsFrozen
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  refine reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hclf, hpost⟩
  · exact Or.inr hrest

/-- Transfer `subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec)` from block `j` to any
caller block `i`'s `callerProg` (preserving `withLsCodeLoaded` form), without requiring `i < 619`. -/
theorem ls_subroutine_ok_of_callee [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-- Caller-block-polymorphic relocatable `memcpy` from read-only `.rodata` (`sessionMemcpyROXSpec`)
under `[LibsignalPlacement]`. -/
def SessionMemcpyROXPlacedOk [LibsignalPlacement] (H : LibsignalHooks) : Prop :=
  ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy") (withLsCl lsmpl sessionMemcpyROXSpec)

theorem SessionMemcpyROXPlacedOk.of_block0 [LibsignalPlacement] {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (h : subroutine_ok blk0Prog (lsρ "memcpy") (withLsCodeLoaded lsmpl sessionMemcpyROXSpec)) :
    SessionMemcpyROXPlacedOk H :=
  fun {_ _} [_] => ls_subroutine_ok_cl_of_callee (j := 0) h

theorem SessionMemcpyROXPlacedOk.of_hook [LibsignalPlacement] {H : LibsignalHooks}
    (hmcpy : HookSat H "memcpy" sessionMemcpyROXSpec) :
    SessionMemcpyROXPlacedOk H :=
  fun {_ _} [_] => ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmcpy)

end Placed

end CryptoVerification.LibsignalTripleRatchet
