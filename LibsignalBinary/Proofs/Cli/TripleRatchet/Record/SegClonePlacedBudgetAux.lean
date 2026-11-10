/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlaced
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneAssemble -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegClone` Sub-Segments 8–9 (`alice_base_key`, `pq_ratchet_state`)

Proves `alice_base_key` and `pq_ratchet_state` cloning on CLI Block `463`, threading
`RustCliAllocBudget M` (`A.pool`) and `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
open CryptoVerification (LibsignalPlacement lsmpl lsRustNoAllocShimSym lsRustAllocSym)
open CryptoVerification.RustHeap (allocHookStack vecU8At vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (
  RecordDecryptGhost sessionShimSpec sessionMemcpyRegionSpec
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false eq_nil_or_length_pos
  segClone_pure_eq_emp vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos
  vecU8At_eq_of_nil vecU8At_eq_of_pos vecU8Buf_nil_eq vecU8Buf_pos_eq
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps (SepWPpCl sepWPpCl_pure_2nd)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved AllocCallPreserved
  RustLayoutOk FitsEvents rustAllocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (vecCloneEvents)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  SegCloneHooks SepWPpCl_of_sepWP_vm SepWPpCl_transport_budgetPool
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget (sepWP_cut_here)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Allocator events emitted by cloning `pq_ratchet_state` (`Vec<u8>::clone`). -/
def pqRatchetCloneEvents (pq : List (BitVec 8)) : List AllocEvent :=
  if pq.length = 0 then [] else rustAllocEvents pq.length 1

theorem segClone_aliceBaseKey_444_pos_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {F : SepProp}
    (hfits : FitsEvents M lim st (rustAllocEvents x.G.alice.bytes.length 1))
    (halice : 0 < x.G.alice.bytes.length)
    (hlen_le : x.G.alice.bytes.length ≤ x.G.alice.cap.toNat)
    (hcap_lt : x.G.alice.cap.toNat < 2 ^ 63)
    (hptr : x.G.alice.ptr ≠ 0)
    (hpc : s.pc = (blkPl_463).base + 1092#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.G.alice.bytes.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (blkPl_463).base + 1132#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (rustAllocEvents x.G.alice.bytes.length 1) st) s1 ∗
          vecGhostAt A.repAlloc x.G.alice (s.sp + 0x198#64) ∗
          vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
          stackAt s.sp allocHookStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        (s.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗
        (s.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
        (s.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗
        (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
        A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
        memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
          (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have hshim := hA.shim_ok
  have halloc := hA.allocNoOom_ok
  have hmemcpy := hA.memcpy_ok
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
  have h1a0 : s.sp + 0x198#64 + 8#64 = s.sp + 0x1a0#64 := by bv_arith
  have h1a8 : s.sp + 0x198#64 + 16#64 = s.sp + 0x1a8#64 := by bv_arith
  have halice_lt : x.G.alice.bytes.length < 2 ^ 63 := by omega
  have halice_le63 : x.G.alice.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have halice_le64 : x.G.alice.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk x.G.alice.bytes.length 1 := ⟨⟨halice, hpow2, halice_le63⟩, by decide⟩
  have htoNat : (BitVec.ofNat 64 x.G.alice.bytes.length).toNat = x.G.alice.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1_le : 1 ≤ x.G.alice.bytes.length := Nat.succ_le_of_lt halice
  have hfits_ev : FitsEvents M lim st [.alloc x.G.alice.bytes.length] := by
    simpa [rustAllocEvents, h1_le] using hfits
  obtain ⟨⟨hwmax, henf, hram, hva⟩, _⟩ := hfits_ev
  apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1132))
  apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
  by_vm_open (
    wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    wp_call hshim ()
    clear hshim
    refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
    have htr_sf : sf.trace = s0.trace :=
      (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr.1])
    have hsp_sf : sf.sp = s.sp := (‹sf.sp = _›).trans (by segCloneAssemble_close)
    rw [show stackAt s.sp allocHookStack = stackAt sf.sp allocHookStack from
      congrArg (stackAt · allocHookStack) hsp_sf.symm]
    apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
    by_vm_open (
      wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2
      refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      wp_call halloc (x.G.alice.bytes.length, 1, st)
      clear halloc
      have hacp : AllocCallPreserved sf sf_1 := by assumption
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 .x0 ≠ 0#64›
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom64
      have htr_sf1 : sf_1.trace = s0.trace :=
        hacp.2.1.trans (by simp only [wp_norm, arm64_norm, htr_sf])
      try dsimp only [Bool.false_eq_true, ↓reduceIte]
      apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
      by_vm_open (
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm3
        wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.ptr, x.G.alice.bytes)
        clear hmemcpy
        refine SepWP.transport_budgetPool (hvm3.trans (by assumption)) (hnext := ?_); clear hvm3
        have htr_sf2 : sf_2.trace = s0.trace :=
          (‹sf_2.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr_sf1])
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
        refine SepWPpCl.weaken_pre ?_
          (hnext sf_2 ⟨BitVec.ofNat 64 x.G.alice.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.bytes⟩
            (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close)
            ⟨htr_sf2, by segCloneAssemble_close⟩
            rfl rfl)
        have h_pure_emp :
            (⌜x.G.alice.bytes.length ≤ x.G.alice.cap.toNat ∧
                x.G.alice.cap.toNat < 2 ^ 63 ∧ x.G.alice.ptr ≠ 0⌝ : SepProp) = emp :=
          segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
        rw [vecGhostAt_eq_of_pos A.repAlloc x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
            vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) x.G.alice.bytes halice halice_lt hoom64,
            h_pure_emp]
        dsimp only [RustCliAllocBudget.repAlloc]
        simp only [sepConj_assoc, hsp_sf, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
      )
    )
  )

/-- Sub-segment 8 (`+1388 / +6432 / +1072 → +1412 / +1132`): clones `alice_base_key`
    into `x25 = alice'.cap` and `x27 = alice'.ptr`, loads `w21, w23` from `[sp + 0x288, 0x28c]`,
    and stores `x26` at `[sp + 0x30]`, threading `A.pool` across `vecCloneEvents x.G.alice`. -/
theorem segClone_aliceBaseKey_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {v30 : BitVec 64} {w288 w28c : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (vecCloneEvents x.G.alice))
    (hpc : s.pc = (blkPl_463).base + 1388#64 ∨
           s.pc = (blkPl_463).base + 6432#64 ∨
           s.pc = (blkPl_463).base + 1072#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (if x.G.alice.bytes = [] then
                 (blkPl_463).base + 1412#64
               else
                 (blkPl_463).base + 1132#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = w28c.setWidth 64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (vecCloneEvents x.G.alice) st) s1 ∗
          vecGhostAt A.repAlloc x.G.alice (s.sp + 0x198#64) ∗
          vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗
          ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          ((s.sp + 0x30#64) ↦₆₄ s.readReg64 .x26) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        vecGhostAt A.repAlloc x.G.alice (s.sp + 0x198#64) ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗
        ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have h1a0 : s.sp + 0x198#64 + 8#64 = s.sp + 0x1a0#64 := by bv_arith
  have h1a8 : s.sp + 0x198#64 + 16#64 = s.sp + 0x1a8#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.alice.bytes with halice | halice
  · have hevs : vecCloneEvents x.G.alice = [] := by simp [vecCloneEvents, halice]
    simp only [halice, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_nil A.repAlloc x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8]
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have h_pure_emp :
        (⌜x.G.alice.cap.toNat < 2 ^ 63 ∧ x.G.alice.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    rcases hpc with hpc | hpc | hpc
    · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1412))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end ⟨0#64, 1#64, []⟩
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close)
            rfl (by simp))
        rw [hevs, M.stepEvents_nil, hpool,
            vecGhostAt_eq_of_nil A.repAlloc x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
            vecU8Buf_nil_eq A.repAlloc, h_pure_emp]
        dsimp only [Reg.x26]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
    · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1412))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end ⟨0#64, 1#64, []⟩
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close)
            rfl (by simp))
        rw [hevs, M.stepEvents_nil, hpool,
            vecGhostAt_eq_of_nil A.repAlloc x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
            vecU8Buf_nil_eq A.repAlloc, h_pure_emp]
        dsimp only [Reg.x26]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
    · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1412))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end ⟨0#64, 1#64, []⟩
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close)
            rfl (by simp))
        rw [hevs, M.stepEvents_nil, hpool,
            vecGhostAt_eq_of_nil A.repAlloc x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
            vecU8Buf_nil_eq A.repAlloc, h_pure_emp]
        dsimp only [Reg.x26]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
  · have halice_ne_nil : x.G.alice.bytes ≠ [] := List.ne_nil_of_length_pos halice
    have hevs : vecCloneEvents x.G.alice = rustAllocEvents x.G.alice.bytes.length 1 := by
      simp [vecCloneEvents, Nat.ne_of_gt halice]
    have hfit_alloc : FitsEvents M lim st (rustAllocEvents x.G.alice.bytes.length 1) :=
      hevs ▸ hfits
    simp only [halice_ne_nil, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_pos A.repAlloc x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
        RustCliAllocBudget.repAlloc_live]
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have halice_ne : BitVec.ofNat 64 x.G.alice.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos halice (by omega)
    have halice_beq : (BitVec.ofNat 64 x.G.alice.bytes.length == 0#64) = false :=
      beq_ofNat_zero_eq_false halice (by omega)
    suffices h_at_444 : ∀ s_444 : State,
        VmPreserved s s_444 →
        s_444.pc = (blkPl_463).base + bv% (1092) →
        s_444.status = .Running →
        s_444.sp = s.sp →
        s_444.spAligned = true →
        s_444.readReg64 .x19 = s.readReg64 .x19 →
        s_444.readReg64 .x21 = w288.setWidth 64 →
        s_444.readReg64 .x22 = s.readReg64 .x22 →
        s_444.readReg64 .x23 = w28c.setWidth 64 →
        s_444.readReg64 .x24 = s.readReg64 .x24 →
        s_444.readReg64 .x25 = BitVec.ofNat 64 x.G.alice.bytes.length →
        s_444.readReg64 .x26 = s.readReg64 .x26 →
        s_444.readReg64 .x28 = s.readReg64 .x28 →
        s_444.readReg64 .x29 = s.readReg64 .x29 →
        (s_444.trace = s0.trace ∧ calleeSavedVRegs s_444 = calleeSavedVRegs s0) →
        SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s_444
          (A.pool lim st s ∗
            (s_444.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗
            (s_444.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
            (s_444.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗
            (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
            A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
            memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
              (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
            (s_444.sp + 0x288#64) ↦₃₂ w288 ∗
            (s_444.sp + 0x28c#64) ↦₃₂ w28c ∗
            (s_444.sp + 0x30#64) ↦₆₄ s.readReg64 .x26 ∗
            stackAt s_444.sp allocHookStack ∗ F)
          Q Qp by
      rcases hpc with hpc | hpc | hpc
      · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1092))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          dsimp only [Reg.x26] at h_at_444
          exact h_at_444 _ hvm (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close)
      · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1092))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          dsimp only [Reg.x26] at h_at_444
          exact h_at_444 _ hvm (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close)
      · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1092))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          dsimp only [Reg.x26] at h_at_444
          exact h_at_444 _ hvm (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close)
    intro s_444 hvm444 hpc444 hrun444 hsp444 hspA444 hx19_444 hx21_444 hx22_444 hx23_444 hx24_444 hx25_444 hx26_444 hx28_444 hx29_444 htr444
    refine SepWPpCl_transport_budgetPool hvm444 ?_
    refine SepWPpCl.weaken_pre
      (P' := A.pool lim st s_444 ∗
              (s_444.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗
              (s_444.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
              (s_444.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗
              (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
              A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
              memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
                (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
              stackAt s_444.sp allocHookStack ∗
              (((s_444.sp + 0x288#64) ↦₃₂ w288) ∗
                ((s_444.sp + 0x28c#64) ↦₃₂ w28c) ∗
                ((s_444.sp + 0x30#64) ↦₆₄ s.readReg64 .x26) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine segClone_aliceBaseKey_444_pos_placed hA hfit_alloc halice hlen_le hcap_lt hptr
      hpc444 hrun444 hspA444 hx25_444 htr444
      fun s1 alice' hpc1 hrun1 hsp1 hspA1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hbytes' hcap' => ?_
    rw [hsp444, ← hevs]
    refine SepWPpCl.weaken_pre ?_
      (hnext s1 alice' hpc1 hrun1 (by reg_chain) hspA1
        (by reg_chain) (by reg_chain) (by reg_chain)
        (by reg_chain) (by reg_chain) hx25_1 (by reg_chain)
        hx27_1 (by reg_chain) (by reg_chain) htr1 hbytes' hcap')
    exact Entails.of_eq (by sep_ac_rfl)

theorem segClone_pqRatchet_478_pos_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {F : SepProp}
    (hfits : FitsEvents M lim st (rustAllocEvents x.st.pqRatchetState.length 1))
    (hpq : 0 < x.st.pqRatchetState.length)
    (hlen_le : x.st.pqRatchetState.length ≤ x.G.pq.cap.toNat)
    (hcap_lt : x.G.pq.cap.toNat < 2 ^ 63)
    (hptr : x.G.pq.ptr ≠ 0)
    (hpc : s.pc = (blkPl_463).base + 1144#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.st.pqRatchetState.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (blkPl_463).base + 1428#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (rustAllocEvents x.st.pqRatchetState.length 1) st) s1 ∗
          vecU8At A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          vecU8Buf A.repAlloc pqCap' pqPtr' x.st.pqRatchetState ∗
          stackAt s.sp allocHookStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        (s.sp + 0x1b0#64) ↦₆₄ x.G.pq.cap ∗
        (s.sp + 0x1b8#64) ↦₆₄ x.G.pq.ptr ∗
        (s.sp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length ∗
        (x.G.pq.ptr ↦ₛ x.st.pqRatchetState) ∗
        A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
        memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.st.pqRatchetState.length)
          (x.G.pq.cap.toNat - x.st.pqRatchetState.length) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have hshim := hA.shim_ok
  have halloc := hA.allocNoOom_ok
  have hmemcpy := hA.memcpy_ok
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
  have h1b8 : s.sp + 0x1b0#64 + 8#64 = s.sp + 0x1b8#64 := by bv_arith
  have h1c0 : s.sp + 0x1b0#64 + 16#64 = s.sp + 0x1c0#64 := by bv_arith
  have hpq_lt : x.st.pqRatchetState.length < 2 ^ 63 := by omega
  have hpq_le63 : x.st.pqRatchetState.length + 1 ≤ 2 ^ 63 := by omega
  have hpq_le64 : x.st.pqRatchetState.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk x.st.pqRatchetState.length 1 := ⟨⟨hpq, hpow2, hpq_le63⟩, by decide⟩
  have htoNat : (BitVec.ofNat 64 x.st.pqRatchetState.length).toNat = x.st.pqRatchetState.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1_le : 1 ≤ x.st.pqRatchetState.length := Nat.succ_le_of_lt hpq
  have hfits_ev : FitsEvents M lim st [.alloc x.st.pqRatchetState.length] := by
    simpa [rustAllocEvents, h1_le] using hfits
  obtain ⟨⟨hwmax, henf, hram, hva⟩, _⟩ := hfits_ev
  apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1428))
  apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
  by_vm_open (
    wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    wp_call hshim ()
    clear hshim
    refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
    have htr_sf : sf.trace = s0.trace :=
      (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr.1])
    have hsp_sf : sf.sp = s.sp := (‹sf.sp = _›).trans (by segCloneAssemble_close)
    rw [show stackAt s.sp allocHookStack = stackAt sf.sp allocHookStack from
      congrArg (stackAt · allocHookStack) hsp_sf.symm]
    apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
    by_vm_open (
      wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2
      refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      wp_call halloc (x.st.pqRatchetState.length, 1, st)
      clear halloc
      have hacp : AllocCallPreserved sf sf_1 := by assumption
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 .x0 ≠ 0#64›
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom64
      have htr_sf1 : sf_1.trace = s0.trace :=
        hacp.2.1.trans (by simp only [wp_norm, arm64_norm, htr_sf])
      try dsimp only [Bool.false_eq_true, ↓reduceIte]
      apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
      by_vm_open (
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm3
        wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.pq.ptr, x.st.pqRatchetState)
        clear hmemcpy
        refine SepWP.transport_budgetPool (hvm3.trans (by assumption)) (hnext := ?_); clear hvm3
        have htr_sf2 : sf_2.trace = s0.trace :=
          (‹sf_2.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr_sf1])
        by_vm_open (
          wp_steps
          refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
            ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm4
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm4
          have hpool4 := A.pool_transport lim
            (M.stepEvents (rustAllocEvents x.st.pqRatchetState.length 1) st) sf_2 s_end hvm4
          refine SepWPpCl.weaken_pre ?_
            (hnext s_end (BitVec.ofNat 64 x.st.pqRatchetState.length) (sf_1.readReg64 (Reg.gpr 0#5))
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              (by dsimp only [s_end]; segCloneAssemble_close)
              ⟨by simp only [s_end, wp_norm, arm64_norm, htr_sf2],
               by dsimp only [s_end]; segCloneAssemble_close⟩
              rfl)
          have h_pure_emp :
              (⌜x.st.pqRatchetState.length ≤ x.G.pq.cap.toNat ∧
                  x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0⌝ : SepProp) = emp :=
            segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
          rw [hpool4,
              vecU8At_eq_of_pos A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState hpq,
              h1b8, h1c0,
              vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) x.st.pqRatchetState hpq hpq_lt hoom64,
              h_pure_emp]
          dsimp only [RustCliAllocBudget.repAlloc]
          simp only [sepConj_assoc, hsp_sf, emp_sepConj, sepConj_emp]
          exact Entails.of_eq (by sep_ac_rfl)
        )
      )
    )
  )

/-- Sub-segment 9 (`+1412 / +1132 → +1428`): clones `pq_ratchet_state`
    into `x20 = pqCap'` and `x22 = pqPtr'`, moves `x22` (`pendCap'`) to `x26`,
    and restores `x24 = sp + 0xca0`, threading `A.pool` across `pqRatchetCloneEvents x.st.pqRatchetState`. -/
theorem segClone_pqRatchet_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {F : SepProp}
    (hfits : FitsEvents M lim st (pqRatchetCloneEvents x.st.pqRatchetState))
    (hpc : s.pc = (if x.G.alice.bytes = [] then
                     (blkPl_463).base + 1412#64
                   else
                     (blkPl_463).base + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (blkPl_463).base + 1428#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (pqRatchetCloneEvents x.st.pqRatchetState) st) s1 ∗
          vecU8At A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          vecU8Buf A.repAlloc pqCap' pqPtr' x.st.pqRatchetState ∗
          stackAt s.sp allocHookStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        vecU8At A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have h1b8 : s.sp + 0x1b0#64 + 8#64 = s.sp + 0x1b8#64 := by bv_arith
  have h1c0 : s.sp + 0x1b0#64 + 16#64 = s.sp + 0x1c0#64 := by bv_arith
  have hpcs : s.pc = (blkPl_463).base + 1412#64 ∨
              s.pc = (blkPl_463).base + 1132#64 := by
    by_cases h : x.G.alice.bytes = [] <;> simp only [h, ↓reduceIte] at hpc <;>
      [exact Or.inl hpc; exact Or.inr hpc]
  clear hpc
  rcases eq_nil_or_length_pos x.st.pqRatchetState with hpq | hpq
  · have hevs : pqRatchetCloneEvents x.st.pqRatchetState = [] := by
      simp [pqRatchetCloneEvents, hpq]
    rw [hpq, vecU8At_eq_of_nil A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr, h1b8, h1c0]
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have h_pure_emp :
        (⌜x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    rcases hpcs with hpc | hpc
    · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1428))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end 0#64 1#64
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by simp [hpq]))
        rw [hevs, M.stepEvents_nil, hpool,
            hpq, vecU8At_eq_of_nil A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr, h1b8, h1c0,
            vecU8Buf_nil_eq A.repAlloc, h_pure_emp]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
    · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1428))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end 0#64 1#64
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by dsimp only [s_end]; segCloneAssemble_close) (by dsimp only [s_end]; segCloneAssemble_close)
            (by simp [hpq]))
        rw [hevs, M.stepEvents_nil, hpool,
            hpq, vecU8At_eq_of_nil A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr, h1b8, h1c0,
            vecU8Buf_nil_eq A.repAlloc, h_pure_emp]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
  · have hevs : pqRatchetCloneEvents x.st.pqRatchetState =
        rustAllocEvents x.st.pqRatchetState.length 1 := by
      simp [pqRatchetCloneEvents, Nat.ne_of_gt hpq]
    have hfit_alloc : FitsEvents M lim st (rustAllocEvents x.st.pqRatchetState.length 1) :=
      hevs ▸ hfits
    rw [vecU8At_eq_of_pos A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState hpq,
        h1b8, h1c0, RustCliAllocBudget.repAlloc_live]
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hpq_ne : BitVec.ofNat 64 x.st.pqRatchetState.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpq (by omega)
    have hpq_beq : (BitVec.ofNat 64 x.st.pqRatchetState.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpq (by omega)
    suffices h_at_478 : ∀ s_478 : State,
        VmPreserved s s_478 →
        s_478.pc = (blkPl_463).base + bv% (1144) →
        s_478.status = .Running →
        s_478.sp = s.sp →
        s_478.spAligned = true →
        s_478.readReg64 .x19 = s.readReg64 .x19 →
        s_478.readReg64 .x20 = BitVec.ofNat 64 x.st.pqRatchetState.length →
        s_478.readReg64 .x21 = s.readReg64 .x21 →
        s_478.readReg64 .x23 = s.readReg64 .x23 →
        s_478.readReg64 .x25 = s.readReg64 .x25 →
        s_478.readReg64 .x26 = s.readReg64 .x22 →
        s_478.readReg64 .x27 = s.readReg64 .x27 →
        s_478.readReg64 .x28 = s.readReg64 .x28 →
        s_478.readReg64 .x29 = s.readReg64 .x29 →
        (s_478.trace = s0.trace ∧ calleeSavedVRegs s_478 = calleeSavedVRegs s0) →
        SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s_478
          (A.pool lim st s ∗
            (s_478.sp + 0x1b0#64) ↦₆₄ x.G.pq.cap ∗
            (s_478.sp + 0x1b8#64) ↦₆₄ x.G.pq.ptr ∗
            (s_478.sp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length ∗
            (x.G.pq.ptr ↦ₛ x.st.pqRatchetState) ∗
            A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
            memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.st.pqRatchetState.length)
              (x.G.pq.cap.toNat - x.st.pqRatchetState.length) ∗
            stackAt s_478.sp allocHookStack ∗ F)
          Q Qp by
      rcases hpcs with hpc | hpc
      · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1144))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          exact h_at_478 _ hvm (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close)
      · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1144))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          exact h_at_478 _ hvm (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
            (by segCloneAssemble_close)
    intro s_478 hvm478 hpc478 hrun478 hsp478 hspA478 hx19_478 hx20_478 hx21_478 hx23_478 hx25_478 hx26_478 hx27_478 hx28_478 hx29_478 htr478
    refine SepWPpCl_transport_budgetPool hvm478 ?_
    refine segClone_pqRatchet_478_pos_placed hA hfit_alloc hpq hlen_le hcap_lt hptr
      hpc478 hrun478 hspA478 hx20_478 htr478
      fun s1 pqCap' pqPtr' hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hcap' => ?_
    rw [hsp478] at hx24_1 ⊢
    rw [← hevs]
    exact hnext s1 pqCap' pqPtr' hpc1 hrun1 (by reg_chain) hspA1
      (by reg_chain) hx20_1 (by reg_chain) hx22_1
      (by reg_chain) hx24_1 (by reg_chain) (by reg_chain)
      (by reg_chain) (by reg_chain) (by reg_chain) htr1 hcap'

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlacedBudgetAux
