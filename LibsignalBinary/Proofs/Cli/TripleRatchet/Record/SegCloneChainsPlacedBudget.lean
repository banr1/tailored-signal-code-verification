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
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlaced
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneChains -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegClone` Sub-Segments 6–7 (`pending_pre_key`, `pending_kyber_pre_key`)

Re-exports `receiver_chains` cloning from `SegCloneChainsPlacedBudgetAux` and threads
`RustCliAllocBudget M` across `pending_pre_key` and `pending_kyber_pre_key` cloning on CLI
Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
open CryptoVerification (LibsignalPlacement lsmpl lsRustNoAllocShimSym lsRustAllocSym)
open CryptoVerification.RustHeap (allocHookStack vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost noneCap optTailVecAt)
open CryptoVerification.LibsignalTripleRatchet (
  RecordDecryptGhost sessionShimSpec sessionMemcpyRegionSpec
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  OptPendClone OptKybClone
  cap_add_one_ne_zero cap_add_one_beq_zero_eq_false
  ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false eq_nil_or_length_pos
  segClone_pure_eq_emp vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos
  vecU8Buf_nil_eq vecU8Buf_pos_eq exists_tail24_decomp exists_unpack32_pair_of_length_8
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps (SepWPpCl sepWPpCl_pure_2nd)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved AllocCallPreserved
  RustLayoutOk FitsEvents rustAllocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (vecCloneEvents optTailCloneEvents)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  SegCloneHooks SepWPpCl_of_sepWP_vm SepWPpCl_transport_budgetPool
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget (sepWP_cut_here)

export LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudgetAux (
  receiverChainsCloneEvents segClone_receiverChains_copy_placed
  segClone_receiverChains_iter_placed segClone_receiverChains_loop_placed
  segClone_receiverChains_placed
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem segClone_pendingPreKey_39c_pos_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {s0 s : State} {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 : BitVec 64}
    {v08 v18 : BitVec 64} {v24 v28 v2c : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (rustAllocEvents gp.vec.bytes.length 1))
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((s.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((s.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s.sp + 0x24c#64) ↦₃₂ tw1) ∗
        ((s.sp + 0x250#64) ↦₆₄ td2) ∗ ((s.sp + 0x258#64) ↦₃₂ tw3) ∗
        ((s.sp + 0x25c#64) ↦₃₂ tw4)))
    (hpos : 0 < gp.vec.bytes.length)
    (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63)
    (hptr : gp.vec.ptr ≠ 0)
    (hpc : s.pc = (blkPl_463).base + 0x39c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32),
      (s1.pc = (blkPl_463).base + 0x558#64 ∨
       s1.pc = (blkPl_463).base + 0x1904#64 ∨
       s1.pc = (blkPl_463).base + 0x3e8#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (rustAllocEvents gp.vec.bytes.length 1) st) s1 ∗
          (⌜gp.tail.length = 48 - 24⌝ ∗
            vecGhostAt A.repAlloc gp.vec (s.sp + 0x230#64) ∗
            ((s.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length⌝ ∗
            vecU8Buf A.repAlloc pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        ((s.sp + 0x230#64) ↦₆₄ gp.vec.cap) ∗
        ((s.sp + 0x238#64) ↦₆₄ gp.vec.ptr) ∗
        ((s.sp + 0x240#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
        (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
          (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((s.sp + 0x248#64) ↦₃₂ tw0) ∗
        ((s.sp + 0x24c#64) ↦₃₂ tw1) ∗
        ((s.sp + 0x250#64) ↦₆₄ td2) ∗
        ((s.sp + 0x258#64) ↦₃₂ tw3) ∗
        ((s.sp + 0x25c#64) ↦₃₂ tw4) ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have hshim := hA.shim_ok
  have halloc := hA.allocNoOom_ok
  have hmemcpy := hA.memcpy_ok
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
  have h238 : s.sp + 0x230#64 + 8#64 = s.sp + 0x238#64 := by bv_arith
  have h240 : s.sp + 0x230#64 + 16#64 = s.sp + 0x240#64 := by bv_arith
  have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gp.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos (by omega)
  have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpos (by omega)
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk gp.vec.bytes.length 1 := ⟨⟨hpos, hpow2, hlen_le63⟩, by decide⟩
  have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1_le : 1 ≤ gp.vec.bytes.length := Nat.succ_le_of_lt hpos
  have hfits_ev : FitsEvents M lim st [.alloc gp.vec.bytes.length] := by
    simpa [rustAllocEvents, h1_le] using hfits
  obtain ⟨⟨hwmax, henf, hram, hva⟩, _⟩ := hfits_ev
  apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1000))
  apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
  by_vm_open (
    wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    wp_call hshim ()
    clear hshim
    refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
    have htr_sf : sf.trace = s0.trace :=
      (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr.1])
    have hsp_sf : sf.sp = s.sp := (‹sf.sp = _›).trans (by segCloneChains_close)
    rw [show stackAt s.sp allocHookStack = stackAt sf.sp allocHookStack from
      congrArg (stackAt · allocHookStack) hsp_sf.symm]
    apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
    by_vm_open (
      wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2
      refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      wp_call halloc (gp.vec.bytes.length, 1, st)
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
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm3
        wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gp.vec.ptr, gp.vec.bytes)
        clear hmemcpy
        refine SepWP.transport_budgetPool (hvm3.trans (by assumption)) (hnext := ?_); clear hvm3
        have htr_sf2 : sf_2.trace = s0.trace :=
          (‹sf_2.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr_sf1])
        by_vm_open (
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
            ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm4
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm4
          have hpool4 := A.pool_transport lim
            (M.stepEvents (rustAllocEvents gp.vec.bytes.length 1) st) sf_2 s_end hvm4
          refine SepWPpCl.weaken_pre ?_
            (hnext s_end (BitVec.ofNat 64 gp.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) td2 tw3 tw0 tw1
              (Or.inr (Or.inr (by dsimp only [s_end]; segCloneChains_close)))
              (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              ⟨by simp only [s_end, wp_norm, arm64_norm, htr_sf2], by dsimp only [s_end]; segCloneChains_close⟩)
          have h_rfl : (⌜BitVec.ofNat 64 gp.vec.bytes.length = BitVec.ofNat 64 gp.vec.bytes.length⌝ : SepProp) = emp :=
            segClone_pure_eq_emp rfl
          have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
            segClone_pure_eq_emp htail
          have h_pure2 : (⌜gp.vec.bytes.length ≤ gp.vec.cap.toNat ∧ gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
            segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
          rw [hpool4,
              vecGhostAt_eq_of_pos A.repAlloc gp.vec (s.sp + 0x230#64) hpos, h238, h240,
              htail_eq,
              vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) gp.vec.bytes hpos hlen_lt hoom64,
              h_rfl, h_pure1, h_pure2]
          dsimp only [RustCliAllocBudget.repAlloc]
          simp only [sepConj_assoc, hsp_sf, emp_sepConj, sepConj_emp]
          exact Entails.of_eq (by sep_ac_rfl)
        )
      )
    )
  )

/-- Sub-segment 6 (`+0x548 / +0x390 → +0x558 / +0x1904 / +0x3e8`): clones `pending_pre_key`
    into `x22 = pendCap'` and `[sp + 0x18] = pendPtr'`, plus spill slots
    `[sp + 0x08, 0x24, 0x28, 0x2c]`, threading `A.pool` across `optTailCloneEvents x.G.pending`. -/
theorem segClone_pendingPreKey_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {v08 v18 : BitVec 64} {v24 v28 v2c : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (optTailCloneEvents x.G.pending))
    (hpc : s.pc = (if x.st.receiverChains = [] then
                     (blkPl_463).base + 0x548#64
                   else
                     (blkPl_463).base + 0x390#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32),
      (s1.pc = (blkPl_463).base + 0x558#64 ∨
       s1.pc = (blkPl_463).base + 0x1904#64 ∨
       s1.pc = (blkPl_463).base + 0x3e8#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (optTailCloneEvents x.G.pending) st) s1 ∗
          optTailVecAt A.repAlloc 48 (s.sp + 0x230#64) x.G.pending ∗
          OptPendClone A.repAlloc x.G.pending pendCap' pendPtr' ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        optTailVecAt A.repAlloc 48 (s.sp + 0x230#64) x.G.pending ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗
        F)
      Q Qp := by
  cases hpend : x.G.pending with
  | none =>
    rw [hpend] at hnext
    dsimp only [optTailCloneEvents, AllocCostModel.stepEvents, List.foldl,
      optTailVecAt, OptPendClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    by_cases hrc : x.st.receiverChains = []
    · simp only [hrc, ↓reduceIte] at hpc
      apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1368))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end 0xffffffffffffffff#64 v18 v08 v24 v28 v2c
            (Or.inl (by dsimp only [s_end]; segCloneChains_close)) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close))
        rw [hpool, h_rfl]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
    · simp only [hrc, ↓reduceIte] at hpc
      apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1368))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end 0xffffffffffffffff#64 v18 v08 v24 v28 v2c
            (Or.inl (by dsimp only [s_end]; segCloneChains_close)) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close))
        rw [hpool, h_rfl]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
  | some gp =>
    rw [hpend] at hfits hnext
    dsimp only [optTailCloneEvents, optTailVecAt, OptPendClone] at hfits hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, _, htail_pts⟩ := exists_tail24_decomp htail
    have h238 : s.sp + 0x230#64 + 8#64 = s.sp + 0x238#64 := by bv_arith
    have h240 : s.sp + 0x230#64 + 16#64 = s.sp + 0x240#64 := by bv_arith
    have h248 : s.sp + 0x230#64 + BitVec.ofNat 64 24 = s.sp + 0x248#64 := by bv_arith
    have h24c : s.sp + 0x248#64 + 4#64 = s.sp + 0x24c#64 := by bv_arith
    have h250 : s.sp + 0x248#64 + 8#64 = s.sp + 0x250#64 := by bv_arith
    have h258 : s.sp + 0x248#64 + 16#64 = s.sp + 0x258#64 := by bv_arith
    have h25c : s.sp + 0x248#64 + 20#64 = s.sp + 0x25c#64 := by bv_arith
    rw [h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c]
    rcases eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · have hevs : vecCloneEvents gp.vec = [] := by simp [vecCloneEvents, hnil]
      rw [vecGhostAt_eq_of_nil A.repAlloc gp.vec (s.sp + 0x230#64) hnil, h238, h240]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      by_cases hrc : x.st.receiverChains = []
      · simp only [hrc, ↓reduceIte] at hpc
        apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (6404))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
          have hpool := A.pool_transport lim st s s_end hvm
          refine SepWPpCl.weaken_pre ?_
            (hnext s_end 0#64 1#64 td2 tw3 tw0 tw1
              (Or.inr (Or.inl (by dsimp only [s_end]; segCloneChains_close)))
              (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close))
          rw [hevs, M.stepEvents_nil, hpool,
              vecGhostAt_eq_of_nil A.repAlloc gp.vec (s.sp + 0x230#64) hnil, h238, h240,
              h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c, hnil, vecU8Buf_nil_eq A.repAlloc,
              h_rfl, h_pure1, h_pure2]
          simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
          exact Entails.of_eq (by sep_ac_rfl)
      · simp only [hrc, ↓reduceIte] at hpc
        apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (6404))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
          have hpool := A.pool_transport lim st s s_end hvm
          refine SepWPpCl.weaken_pre ?_
            (hnext s_end 0#64 1#64 td2 tw3 tw0 tw1
              (Or.inr (Or.inl (by dsimp only [s_end]; segCloneChains_close)))
              (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close))
          rw [hevs, M.stepEvents_nil, hpool,
              vecGhostAt_eq_of_nil A.repAlloc gp.vec (s.sp + 0x230#64) hnil, h238, h240,
              h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c, hnil, vecU8Buf_nil_eq A.repAlloc,
              h_rfl, h_pure1, h_pure2]
          simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
          exact Entails.of_eq (by sep_ac_rfl)
    · have hevs : vecCloneEvents gp.vec = rustAllocEvents gp.vec.bytes.length 1 := by
        simp [vecCloneEvents, Nat.ne_of_gt hpos]
      have hfit_alloc : FitsEvents M lim st (rustAllocEvents gp.vec.bytes.length 1) :=
        hevs ▸ hfits
      rw [vecGhostAt_eq_of_pos A.repAlloc gp.vec (s.sp + 0x230#64) hpos, h238, h240,
          RustCliAllocBudget.repAlloc_live]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hsub := fun (s_39c : State) (htail_eq_39c : ((s_39c.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
          (((s_39c.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s_39c.sp + 0x24c#64) ↦₃₂ tw1) ∗
            ((s_39c.sp + 0x250#64) ↦₆₄ td2) ∗ ((s_39c.sp + 0x258#64) ↦₃₂ tw3) ∗
            ((s_39c.sp + 0x25c#64) ↦₃₂ tw4))) =>
        segClone_pendingPreKey_39c_pos_placed (A := A) (lim := lim) (st := st) (H := H) hA
          (s0 := s0) (s := s_39c) (ret := ret) (Q := Q) (Qp := Qp)
          (gp := gp) (tw0 := tw0) (tw1 := tw1) (tw3 := tw3) (tw4 := tw4) (td2 := td2)
          (v08 := v08) (v18 := v18) (v24 := v24) (v28 := v28) (v2c := v2c) (F := F)
          hfit_alloc htail htail_eq_39c hpos hlen_le hcap_lt hptr
      suffices h_at_39c : ∀ s_39c : State,
          VmPreserved s s_39c →
          s_39c.pc = (blkPl_463).base + bv% (924) →
          s_39c.status = .Running →
          s_39c.sp = s.sp →
          s_39c.spAligned = true →
          s_39c.readReg64 .x24 = s.readReg64 .x24 →
          s_39c.readReg64 .x25 = s.readReg64 .x25 →
          s_39c.readReg64 .x26 = s.readReg64 .x26 →
          s_39c.readReg64 .x28 = s.readReg64 .x28 →
          s_39c.readReg64 .x29 = s.readReg64 .x29 →
          (s_39c.trace = s0.trace ∧ calleeSavedVRegs s_39c = calleeSavedVRegs s0) →
          SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s_39c
            (A.pool lim st s ∗
              (s_39c.sp + 0x230#64) ↦₆₄ gp.vec.cap ∗
              (s_39c.sp + 0x238#64) ↦₆₄ gp.vec.ptr ∗
              (s_39c.sp + 0x240#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length ∗
              (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
              A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
              memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
                (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
              (s_39c.sp + 0x248#64) ↦₃₂ tw0 ∗
              (s_39c.sp + 0x24c#64) ↦₃₂ tw1 ∗
              (s_39c.sp + 0x250#64) ↦₆₄ td2 ∗
              (s_39c.sp + 0x258#64) ↦₃₂ tw3 ∗
              (s_39c.sp + 0x25c#64) ↦₃₂ tw4 ∗
              (s_39c.sp + 0x08#64) ↦₆₄ v08 ∗
              (s_39c.sp + 0x18#64) ↦₆₄ v18 ∗
              (s_39c.sp + 0x24#64) ↦₃₂ v24 ∗
              (s_39c.sp + 0x28#64) ↦₃₂ v28 ∗
              (s_39c.sp + 0x2c#64) ↦₃₂ v2c ∗
              stackAt s_39c.sp allocHookStack ∗ F)
            Q Qp by
        clear hsub
        by_cases hrc : x.st.receiverChains = []
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (924))
          by_vm_steps
            wp_steps
            refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
              ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
            exact h_at_39c _ hvm (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (924))
          by_vm_steps
            wp_steps
            refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
              ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
            exact h_at_39c _ hvm (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
      intro s_39c hvm39c hpc39c hrun39c hsp39c hspA39c hx24_39c hx25_39c hx26_39c hx28_39c hx29_39c htr39c
      refine SepWPpCl_transport_budgetPool hvm39c ?_
      have htail_eq_39c : ((s_39c.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
          (((s_39c.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s_39c.sp + 0x24c#64) ↦₃₂ tw1) ∗
            ((s_39c.sp + 0x250#64) ↦₆₄ td2) ∗ ((s_39c.sp + 0x258#64) ↦₃₂ tw3) ∗
            ((s_39c.sp + 0x25c#64) ↦₃₂ tw4)) := by
        rw [hsp39c, h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c]
      refine hsub s_39c htail_eq_39c hpc39c hrun39c hspA39c htr39c
        fun s1 pendCap' pendPtr' v08' v24' v28' v2c' hpc1 hrun1 hsp1 hspA1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      clear hsub
      rw [hsp39c, ← hevs]
      exact hnext s1 pendCap' pendPtr' v08' v24' v28' v2c'
        hpc1 hrun1 (by reg_chain) hspA1
        hx22_1 (by reg_chain) (by reg_chain)
        (by reg_chain) (by reg_chain) (by reg_chain) htr1

theorem segClone_pendingKyber_3f8_pos_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {s0 s : State} {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {gk : TailVecGhost} {kw0 kw1 : BitVec 32}
    {v00 : BitVec 64} {v14 : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (rustAllocEvents gk.vec.bytes.length 1))
    (htail : gk.tail.length = 32 - 24)
    (htail_pts : ∀ a : BitVec 64,
      (a ↦ₛ gk.tail) = ((a ↦₃₂ kw0) ∗ ((a + 4#64) ↦₃₂ kw1)))
    (hpos : 0 < gk.vec.bytes.length)
    (hlen_le : gk.vec.bytes.length ≤ gk.vec.cap.toNat)
    (hcap_lt : gk.vec.cap.toNat < 2 ^ 63)
    (hptr : gk.vec.ptr ≠ 0)
    (hpc : s.pc = (blkPl_463).base + 0x3f8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32),
      (s1.pc = (blkPl_463).base + 0x56c#64 ∨
       s1.pc = (blkPl_463).base + 0x1920#64 ∨
       s1.pc = (blkPl_463).base + 0x430#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (rustAllocEvents gk.vec.bytes.length 1) st) s1 ∗
          (⌜gk.tail.length = 32 - 24⌝ ∗
            vecGhostAt A.repAlloc gk.vec (s.sp + 0x260#64) ∗
            ((s.sp + 0x260#64 + BitVec.ofNat 64 24) ↦ₛ gk.tail)) ∗
          (⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length⌝ ∗
            vecU8Buf A.repAlloc kybCap' kybPtr' gk.vec.bytes) ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        ((s.sp + 0x260#64) ↦₆₄ gk.vec.cap) ∗
        ((s.sp + 0x268#64) ↦₆₄ gk.vec.ptr) ∗
        ((s.sp + 0x270#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length) ∗
        (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
        A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
        memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length)
          (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
        ((s.sp + 0x278#64) ↦₃₂ kw0) ∗
        ((s.sp + 0x27c#64) ↦₃₂ kw1) ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q Qp := by
  have hshim := hA.shim_ok
  have halloc := hA.allocNoOom_ok
  have hmemcpy := hA.memcpy_ok
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
  have h268 : s.sp + 0x260#64 + 8#64 = s.sp + 0x268#64 := by bv_arith
  have h270 : s.sp + 0x260#64 + 16#64 = s.sp + 0x270#64 := by bv_arith
  have h278 : s.sp + 0x260#64 + BitVec.ofNat 64 24 = s.sp + 0x278#64 := by bv_arith
  have h27c : s.sp + 0x278#64 + 4#64 = s.sp + 0x27c#64 := by bv_arith
  have hlen_lt : gk.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gk.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gk.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hlen_ne : BitVec.ofNat 64 gk.vec.bytes.length ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos (by omega)
  have hlen_beq : (BitVec.ofNat 64 gk.vec.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpos (by omega)
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk gk.vec.bytes.length 1 := ⟨⟨hpos, hpow2, hlen_le63⟩, by decide⟩
  have htoNat : (BitVec.ofNat 64 gk.vec.bytes.length).toNat = gk.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1_le : 1 ≤ gk.vec.bytes.length := Nat.succ_le_of_lt hpos
  have hfits_ev : FitsEvents M lim st [.alloc gk.vec.bytes.length] := by
    simpa [rustAllocEvents, h1_le] using hfits
  obtain ⟨⟨hwmax, henf, hram, hva⟩, _⟩ := hfits_ev
  apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1072))
  apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
  by_vm_open (
    wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    wp_call hshim ()
    clear hshim
    refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
    have htr_sf : sf.trace = s0.trace :=
      (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr.1])
    have hsp_sf : sf.sp = s.sp := (‹sf.sp = _›).trans (by segCloneChains_close)
    rw [show stackAt s.sp allocHookStack = stackAt sf.sp allocHookStack from
      congrArg (stackAt · allocHookStack) hsp_sf.symm]
    apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
    by_vm_open (
      wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2
      refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      wp_call halloc (gk.vec.bytes.length, 1, st)
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
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm3
        wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gk.vec.ptr, gk.vec.bytes)
        clear hmemcpy
        refine SepWP.transport_budgetPool (hvm3.trans (by assumption)) (hnext := ?_); clear hvm3
        have htr_sf2 : sf_2.trace = s0.trace :=
          (‹sf_2.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr_sf1])
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        refine SepWPpCl.weaken_pre ?_
          (hnext sf_2 (BitVec.ofNat 64 gk.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) kw0
            (Or.inr (Or.inr (by segCloneChains_close))) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) ⟨htr_sf2, by segCloneChains_close⟩)
        have h_rfl : (⌜BitVec.ofNat 64 gk.vec.bytes.length = BitVec.ofNat 64 gk.vec.bytes.length⌝ : SepProp) = emp :=
          segClone_pure_eq_emp rfl
        have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp :=
          segClone_pure_eq_emp htail
        have h_pure2 : (⌜gk.vec.bytes.length ≤ gk.vec.cap.toNat ∧ gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
          segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
        rw [vecGhostAt_eq_of_pos A.repAlloc gk.vec (s.sp + 0x260#64) hpos, h268, h270,
            h278, htail_pts (s.sp + 0x278#64), h27c,
            vecU8Buf_pos_eq A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) gk.vec.bytes hpos hlen_lt hoom64,
            h_rfl, h_pure1, h_pure2]
        dsimp only [RustCliAllocBudget.repAlloc, Reg.x25]
        simp only [sepConj_assoc, hsp_sf, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
      )
    )
  )

/-- Sub-segment 7 (`+0x558 / +0x1904 / +0x3e8 → +0x56c / +0x1920 / +0x430`):
    stores `[sp + 0x3c] = w25` (`session_version`) and clones `pending_kyber_pre_key`
    into `x19 = kybCap'`, `[sp + 0x00] = kybPtr'`, and `[sp + 0x14] = v14'`,
    threading `A.pool` across `optTailCloneEvents x.G.kyber`. -/
theorem segClone_pendingKyber_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {v00 : BitVec 64} {v14 v3c : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (optTailCloneEvents x.G.kyber))
    (hpc : s.pc = (blkPl_463).base + 0x558#64 ∨
           s.pc = (blkPl_463).base + 0x1904#64 ∨
           s.pc = (blkPl_463).base + 0x3e8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32),
      (s1.pc = (blkPl_463).base + 0x56c#64 ∨
       s1.pc = (blkPl_463).base + 0x1920#64 ∨
       s1.pc = (blkPl_463).base + 0x430#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (optTailCloneEvents x.G.kyber) st) s1 ∗
          optTailVecAt A.repAlloc 32 (s.sp + 0x260#64) x.G.kyber ∗
          OptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        optTailVecAt A.repAlloc 32 (s.sp + 0x260#64) x.G.kyber ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        stackAt s.sp allocHookStack ∗
        F)
      Q Qp := by
  cases hkyb : x.G.kyber with
  | none =>
    rw [hkyb] at hnext
    dsimp only [optTailCloneEvents, AllocCostModel.stepEvents, List.foldl,
      optTailVecAt, OptKybClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    rcases hpc with hpc | hpc | hpc
    · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1388))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end 0xffffffffffffffff#64 v00 v14
            (Or.inl (by dsimp only [s_end]; segCloneChains_close)) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close))
        rw [hpool, h_rfl]; dsimp only [Reg.x25]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
    · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1388))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end 0xffffffffffffffff#64 v00 v14
            (Or.inl (by dsimp only [s_end]; segCloneChains_close)) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close))
        rw [hpool, h_rfl]; dsimp only [Reg.x25]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
    · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1388))
      by_vm_steps
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
        have hpool := A.pool_transport lim st s s_end hvm
        refine SepWPpCl.weaken_pre ?_
          (hnext s_end 0xffffffffffffffff#64 v00 v14
            (Or.inl (by dsimp only [s_end]; segCloneChains_close)) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
            (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close))
        rw [hpool, h_rfl]; dsimp only [Reg.x25]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by sep_ac_rfl)
  | some gk =>
    rw [hkyb] at hfits hnext
    dsimp only [optTailCloneEvents, optTailVecAt, OptKybClone] at hfits hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun htail => ?_
    obtain ⟨kw0, kw1, _, htail_pts⟩ := exists_unpack32_pair_of_length_8 htail
    have h268 : s.sp + 0x260#64 + 8#64 = s.sp + 0x268#64 := by bv_arith
    have h270 : s.sp + 0x260#64 + 16#64 = s.sp + 0x270#64 := by bv_arith
    have h278 : s.sp + 0x260#64 + BitVec.ofNat 64 24 = s.sp + 0x278#64 := by bv_arith
    have h27c : s.sp + 0x278#64 + 4#64 = s.sp + 0x27c#64 := by bv_arith
    rw [h278, htail_pts (s.sp + 0x278#64), h27c]
    rcases eq_nil_or_length_pos gk.vec.bytes with hnil | hpos
    · have hevs : vecCloneEvents gk.vec = [] := by simp [vecCloneEvents, hnil]
      rw [vecGhostAt_eq_of_nil A.repAlloc gk.vec (s.sp + 0x260#64) hnil, h268, h270]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      rcases hpc with hpc | hpc | hpc
      · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (6432))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
          have hpool := A.pool_transport lim st s s_end hvm
          refine SepWPpCl.weaken_pre ?_
            (hnext s_end 0#64 1#64 kw0
              (Or.inr (Or.inl (by dsimp only [s_end]; segCloneChains_close)))
              (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close))
          rw [hevs, M.stepEvents_nil, hpool,
              vecGhostAt_eq_of_nil A.repAlloc gk.vec (s.sp + 0x260#64) hnil, h268, h270,
              h278, htail_pts (s.sp + 0x278#64), h27c, hnil, vecU8Buf_nil_eq A.repAlloc,
              h_rfl, h_pure1, h_pure2]
          dsimp only [Reg.x25]
          simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
          exact Entails.of_eq (by sep_ac_rfl)
      · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (6432))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
          have hpool := A.pool_transport lim st s s_end hvm
          refine SepWPpCl.weaken_pre ?_
            (hnext s_end 0#64 1#64 kw0
              (Or.inr (Or.inl (by dsimp only [s_end]; segCloneChains_close)))
              (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close))
          rw [hevs, M.stepEvents_nil, hpool,
              vecGhostAt_eq_of_nil A.repAlloc gk.vec (s.sp + 0x260#64) hnil, h268, h270,
              h278, htail_pts (s.sp + 0x278#64), h27c, hnil, vecU8Buf_nil_eq A.repAlloc,
              h_rfl, h_pure1, h_pure2]
          dsimp only [Reg.x25]
          simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
          exact Entails.of_eq (by sep_ac_rfl)
      · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (6432))
        by_vm_steps
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
            ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
          have hpool := A.pool_transport lim st s s_end hvm
          refine SepWPpCl.weaken_pre ?_
            (hnext s_end 0#64 1#64 kw0
              (Or.inr (Or.inl (by dsimp only [s_end]; segCloneChains_close)))
              (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
              (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close))
          rw [hevs, M.stepEvents_nil, hpool,
              vecGhostAt_eq_of_nil A.repAlloc gk.vec (s.sp + 0x260#64) hnil, h268, h270,
              h278, htail_pts (s.sp + 0x278#64), h27c, hnil, vecU8Buf_nil_eq A.repAlloc,
              h_rfl, h_pure1, h_pure2]
          dsimp only [Reg.x25]
          simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
          exact Entails.of_eq (by sep_ac_rfl)
    · have hevs : vecCloneEvents gk.vec = rustAllocEvents gk.vec.bytes.length 1 := by
        simp [vecCloneEvents, Nat.ne_of_gt hpos]
      have hfit_alloc : FitsEvents M lim st (rustAllocEvents gk.vec.bytes.length 1) :=
        hevs ▸ hfits
      rw [vecGhostAt_eq_of_pos A.repAlloc gk.vec (s.sp + 0x260#64) hpos, h268, h270,
          RustCliAllocBudget.repAlloc_live]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hsub : ∀ (s_3f8 : State), _ := fun s_3f8 =>
        segClone_pendingKyber_3f8_pos_placed (A := A) (lim := lim) (st := st) (H := H) hA
          (s0 := s0) (s := s_3f8) (ret := ret) (Q := Q) (Qp := Qp)
          (gk := gk) (kw0 := kw0) (kw1 := kw1) (v00 := v00) (v14 := v14) (F := F)
          hfit_alloc htail htail_pts hpos hlen_le hcap_lt hptr
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      suffices h_at_3f8 : ∀ s_3f8 : State,
          VmPreserved s s_3f8 →
          s_3f8.pc = (blkPl_463).base + bv% (1016) →
          s_3f8.status = .Running →
          s_3f8.sp = s.sp →
          s_3f8.spAligned = true →
          s_3f8.readReg64 .x22 = s.readReg64 .x22 →
          s_3f8.readReg64 .x24 = s.readReg64 .x24 →
          s_3f8.readReg64 .x25 = s.readReg64 .x25 →
          s_3f8.readReg64 .x26 = s.readReg64 .x26 →
          s_3f8.readReg64 .x28 = s.readReg64 .x28 →
          s_3f8.readReg64 .x29 = s.readReg64 .x29 →
          (s_3f8.trace = s0.trace ∧ calleeSavedVRegs s_3f8 = calleeSavedVRegs s0) →
          SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s_3f8
            (A.pool lim st s ∗
              (s_3f8.sp + 0x260#64) ↦₆₄ gk.vec.cap ∗
              (s_3f8.sp + 0x268#64) ↦₆₄ gk.vec.ptr ∗
              (s_3f8.sp + 0x270#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length ∗
              (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
              A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
              memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length)
                (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
              (s_3f8.sp + 0x278#64) ↦₃₂ kw0 ∗
              (s_3f8.sp + 0x27c#64) ↦₃₂ kw1 ∗
              (s_3f8.sp ↦₆₄ v00) ∗
              (s_3f8.sp + 0x14#64) ↦₃₂ v14 ∗
              (s_3f8.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32 ∗
              stackAt s_3f8.sp allocHookStack ∗ F)
            Q Qp by
        clear hsub
        rcases hpc with hpc | hpc | hpc
        · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1016))
          by_vm_steps
            wp_steps
            refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
              ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
            dsimp only [Reg.x25] at h_at_3f8
            exact h_at_3f8 _ hvm (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close)
        · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1016))
          by_vm_steps
            wp_steps
            refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
              ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
            dsimp only [Reg.x25] at h_at_3f8
            exact h_at_3f8 _ hvm (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close)
        · apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1016))
          by_vm_steps
            wp_steps
            refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
              ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
            dsimp only [Reg.x25] at h_at_3f8
            exact h_at_3f8 _ hvm (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
              (by segCloneChains_close)
      intro s_3f8 hvm3f8 hpc3f8 hrun3f8 hsp3f8 hspA3f8 hx22_3f8 hx24_3f8 hx25_3f8 hx26_3f8 hx28_3f8 hx29_3f8 htr3f8
      refine SepWPpCl_transport_budgetPool hvm3f8 ?_
      rw [← hx25_3f8]
      refine hsub s_3f8 hpc3f8 hrun3f8 hspA3f8 htr3f8
        fun s1 kybCap' kybPtr' v14' hpc1 hrun1 hsp1 hspA1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      clear hsub
      rw [hsp3f8, hx25_3f8, ← hevs]
      exact hnext s1 kybCap' kybPtr' v14'
        hpc1 hrun1 (by reg_chain) hspA1
        hx19_1 (by reg_chain) (by reg_chain) (by reg_chain)
        (by reg_chain) (by reg_chain) (by reg_chain) htr1

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudget
