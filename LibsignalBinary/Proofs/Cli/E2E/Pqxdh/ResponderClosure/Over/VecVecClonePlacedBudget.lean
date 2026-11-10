/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecCloneBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClonePlaced
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.PlacedCallSym
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Placed `<Vec<Vec<u8>> as Clone>::clone` on 1 Element

Proves `VecVecClone1PlacedOkStmt M A lim H` (`vecVecClone1_placed_okX_of_ser`) at `lsmpl.base 117`
from `SerContractsXPlaced M A lim H` under `FitsEnv M lim st (VecVecClone1Env x)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClonePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCl sepWP_mono_lscl
  lsρ lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
)
open CryptoVerification.RustHeap (arrayAt vecHeader vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.E2E.Record.Placed (blkPC_117 blkPl_117)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  prevElem prevVecAt vvc1Cells vvc1Saved vvc1_stack_split vvc1_saved_cells vvc1_mem24_cells
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.VvcStateSimp (
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  SepWPpLsCl subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  VecVecClone1Env VecVecClone1Ghost vecVecClone1Events vecVecClone1SpecX vecVecClone1StackX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlacedBudget (
  VecVecClone1PlacedOkStmt vecVecClone1_placed_ok_cl
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecCloneBudget (
  vvc1Q vvc1Qp
  fitsEvents_outer24_of_fitsEnv fitsEvents_inner_of_fitsEnv
  vecVecClone1Env_nil stepEvents_vecVecClone1_nil stepEvents_vecVecClone1_pos
  vvc1_src_eq vvc1_src_fold vvc1_post_entails vvc1_elem_nil vvc1_elem_cons
)

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓] sp_setPC_pre
  sp_setMem_setPC_pre readReg64_setPC_pre
  readReg64_setMem_setPC_pre readReg32_setPC_pre
  readReg32_setMem_setPC_pre
attribute [local wp_norm] calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32 calleeSavedVRegs_writeReg
  calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite calleeSavedVRegs_writeVReg32_ite
  isCalleeSavedVReg updateCalleeSavedVRegs

@[local arm64_norm ↓, local wp_norm ↓]
private theorem vvc1_readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem vvc1_readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

/-! ## Epilogue (`+0xc8`) -/

private theorem sepWPp_of_sepWP_lscl {prog : Program} {pl : Obj.MultiPlacement}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
theorem vvc1_finish_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : VecVecClone1Ghost) (st : M.σ) (evs : List AllocEvent) (s0 s : State) (R : SepProp)
    (q : BitVec 64) (henv : VecVecClone1Env x evs) (hq : q ≠ 0#64)
    (hpc : s.pc = (blkPl_117).base + bv% (200)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst) (hx23 : s.readReg64 (Reg.gpr 23#5) = q)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) extHookStack ∗
        arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗
        A.pool lim (M.stepEvents evs st) s ∗ A.repAlloc.live q 24 8 ∗ vecU8 A.repAlloc q x.enc)
      (vvc1Q A lim x st s0 R) (vvc1Qp A lim x st s0 R) := by
  intro _
  change s.pc = (blkPl_117).base + 200#64 at hpc
  rw [vvc1_mem24_cells x.dst]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 => ?_
  unfold vvc1Saved; simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  refine ⟨?_, by simp_all, ?_⟩
  · intro hm
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_
      (sepConj_mono_left (vvc1_post_entails A lim x st evs s0 _ q
        (by simp_all [ProofLib.NonSyscallPreserved, wp_norm, arm64_norm]) henv hq))
    rw [vvc1_stack_split s0.sp]
    refine Entails.trans (Entails.of_eq (show _ =
      ((vecHeader x.dst 1#64 q 1#64 ∗
        (arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗
          A.pool lim (M.stepEvents evs st) _ ∗ A.repAlloc.live q 24 8 ∗ vecU8 A.repAlloc q x.enc)) ∗
        (stackAt (s0.sp - 96#64) extHookStack ∗ vvc1Saved s0)) ∗ R by
        unfold vecHeader vvc1Saved; sep_ac_rfl)) ?_
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (vvc1_saved_cells s0)))
  · constructor <;> simp_all

/-! ## Post-Outer-Allocation Branches (`+0x44`) -/

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
/-- Placed empty-element branch (`L = 0`): writes `{0, 1, 0}` at `q`. -/
theorem vvc1_nil_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : VecVecClone1Ghost) (st : M.σ) (s0 s : State) (R : SepProp)
    (q cap ptr : BitVec 64) (SRC : SepProp)
    (henc : x.enc = []) (hq : q ≠ 0#64) (hs0_align : s0.spAligned = true)
    (hsrc : vecHeader x.src cap ptr 0#64 ∗ SRC ⊢ arrayAt (prevElem A.repAlloc) 24 x.src [x.enc])
    (hpc : s.pc = (blkPl_117).base + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecHeader x.src cap ptr 0#64 ∗ SRC ∗ memRegion x.dst 24 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 24 8) st) s ∗
        stackAt (s0.sp - 96#64) extHookStack ∗ vvc1Saved s0 ∗
        A.repAlloc.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A lim x st s0 R) (vvc1Qp A lim x st s0 R) := by
  intro hcl
  have hfin := fun s' => vvc1_finish_placed (M := M) (A := A) (lim := lim) (H := H)
    x st (rustAllocEvents 24 8) s0 s' R q (vecVecClone1Env_nil henc) hq
  change s.pc = (blkPl_117).base + 68#64 at hpc
  have hq_beq : (q == 0#64) = false := beq_eq_false_iff_ne.mpr hq
  have hsp_sub_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96 hs0_align (by decide)
  rw [vvc1_mem24_cells q]; unfold vecHeader
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 => ?_
  apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_117).base + bv% (200))
  wp_steps_sync_pool ((blkPl_117).base + bv% (200))
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_ep
  refine SepWPp.weaken_pre ?_ (hfin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_ep)
  · have hel : (q ↦₆₄ 0#64) ∗ ((q + 8#64) ↦₆₄ 1#64) ∗ ((q + 16#64) ↦₆₄ 0#64) ⊢
        vecU8 A.repAlloc q x.enc := by
      rw [henc]; exact vvc1_elem_nil A q
    have hsrc' : (x.src ↦₆₄ cap) ∗ ((x.src + 8#64) ↦₆₄ ptr) ∗ ((x.src + 16#64) ↦₆₄ 0#64) ∗ SRC ⊢
        arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] := by
      refine Entails.trans ?_ hsrc; unfold vecHeader; exact Entails.of_eq (by simp only [sepConj_assoc])
    refine Entails.trans (Entails.of_eq (show _ =
      (((x.src ↦₆₄ cap) ∗ ((x.src + 8#64) ↦₆₄ ptr) ∗ ((x.src + 16#64) ↦₆₄ 0#64) ∗ SRC) ∗
        ((q ↦₆₄ 0#64) ∗ ((q + 8#64) ↦₆₄ 1#64) ∗ ((q + 16#64) ↦₆₄ 0#64)) ∗
        (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) extHookStack ∗
          A.pool lim (M.stepEvents (rustAllocEvents 24 8) st) _ ∗
          A.repAlloc.live q 24 8)) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hsrc' (sepConj_mono_left hel)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  all_goals simp only [State.spAligned, wp_norm, arm64_norm, *]
  all_goals exact hs0_align

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
/-- Placed non-empty element branch (`L > 0`): allocates `p'` via `allocNoOom(L, 1)`, copies `ptr`
into `p'`, and writes `{L, p', L}` at `q`. -/
theorem vvc1_cons_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) (x : VecVecClone1Ghost) (st : M.σ)
    (s0 s : State) (R : SepProp) (q cap ptr : BitVec 64) (SRCM : SepProp)
    (hpos : 0 < x.enc.length) (hlt : x.enc.length < 2 ^ 63) (hq : q ≠ 0#64)
    (hs0_align : s0.spAligned = true)
    (hfit_in : FitsEvents M lim (M.stepEvents (rustAllocEvents 24 8) st)
      (rustAllocEvents x.enc.length 1))
    (hsrc : vecHeader x.src cap ptr (BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM ⊢
      arrayAt (prevElem A.repAlloc) 24 x.src [x.enc])
    (hpc : s.pc = (blkPl_117).base + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecHeader x.src cap ptr (BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM ∗
        memRegion x.dst 24 ∗ A.pool lim (M.stepEvents (rustAllocEvents 24 8) st) s ∗
        stackAt (s0.sp - 96#64) extHookStack ∗ vvc1Saved s0 ∗
        A.repAlloc.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A lim x st s0 R) (vvc1Qp A lim x st s0 R) := by
  intro hcl
  have hfin := fun s' => vvc1_finish_placed (M := M) (A := A) (lim := lim) (H := H)
    x st (vecVecClone1Events x.enc) s0 s' R q rfl hq
  change s.pc = (blkPl_117).base + 68#64 at hpc
  have hq_beq : (q == 0#64) = false := beq_eq_false_iff_ne.mpr hq
  have hsp_sub_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96 hs0_align (by decide)
  have hL : (BitVec.ofNat 64 x.enc.length).toNat = x.enc.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hLne : BitVec.ofNat 64 x.enc.length ≠ 0#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    rw [hL, h0] at h2; omega
  have hLbeq : (BitVec.ofNat 64 x.enc.length == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; exact hLne
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsumL : x.enc.length + 1 ≤ 2 ^ 63 := by omega
  have hmax1 : 1 ≤ 2 ^ 31 := by decide
  have hlayL : RustLayoutOk x.enc.length 1 := ⟨⟨hpos, hpow1, hsumL⟩, hmax1⟩
  rw [vvc1_mem24_cells q]; unfold vecHeader
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 => ?_
  apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_shim
  have hshim_call := lscall_of_withLsCl
    (hC.alloc.shim (callerProg := (blkPC_117).rebase (blkPl_117).base H)) hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := lsρ lsRustAllocSym)
  wp_call hshim_call ()
  have htr_shim : sf.trace = s0.trace := by simpa only [wp_norm, arm64_norm, *] using ‹sf.trace = _›
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_alloc
  have halloc_call := hC.alloc.allocNoOom_call
    (callerProg := (blkPC_117).rebase (blkPl_117).base H) hcl_alloc
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := lsρ lsMemcpySym)
  wp_call halloc_call (x.enc.length, 1, M.stepEvents (rustAllocEvents 24 8) st)
  have htr_alloc : sf_1.trace = s0.trace :=
    ‹AllocCallPreserved _ sf_1›.2.1.trans (by simp only [wp_norm, arm64_norm, *])
  have hp_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 .x0 ≠ 0#64›
  have hp_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hp_ne
  wp_steps_sync_pool (lsρ lsMemcpySym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_memcpy
  have hmemcpy_call := lscall_of_withLsCl
    (hC.memcpy (callerProg := (blkPC_117).rebase (blkPl_117).base H)) hcl_memcpy
  apply sepWPp_of_sepWP_lscl hcl_memcpy (mid := (blkPl_117).base + bv% (200))
  wp_call hmemcpy_call (sf_1.readReg64 (Reg.gpr 0#5), ptr, x.enc)
  have htr_memcpy : sf_2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, *] using ‹sf_2.trace = _›
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool ((blkPl_117).base + bv% (200))
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_ep
  refine SepWPp.weaken_pre ?_ (hfin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_ep)
  · rw [stepEvents_vecVecClone1_pos st hpos]
    have hel := vvc1_elem_cons A q (sf_1.readReg64 (Reg.gpr 0#5)) x.enc hp_ne hpos hlt
    have hsrc' : (x.src ↦₆₄ cap) ∗ ((x.src + 8#64) ↦₆₄ ptr) ∗
        ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM ⊢
        arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] := by
      refine Entails.trans ?_ hsrc; unfold vecHeader; exact Entails.of_eq (by simp only [sepConj_assoc])
    have hlive_eq : A.live (sf_1.readReg64 .x0) x.enc.length 1 =
        A.repAlloc.live (sf_1.readReg64 (Reg.gpr 0#5)) x.enc.length 1 := rfl
    rw [hlive_eq]
    refine Entails.trans (Entails.of_eq (show _ =
      (((x.src ↦₆₄ cap) ∗ ((x.src + 8#64) ↦₆₄ ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM) ∗
        ((q ↦₆₄ BitVec.ofNat 64 x.enc.length) ∗ ((q + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
          ((q + 16#64) ↦₆₄ BitVec.ofNat 64 x.enc.length) ∗
          A.repAlloc.live (sf_1.readReg64 (Reg.gpr 0#5)) x.enc.length 1 ∗
          (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ x.enc)) ∗
        (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) extHookStack ∗
          A.pool lim (M.stepEvents (vecVecClone1Events x.enc) st) _ ∗
          A.repAlloc.live q 24 8)) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hsrc' (sepConj_mono_left hel)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  all_goals simp only [State.spAligned, wp_norm, arm64_norm, *]
  all_goals exact hs0_align

set_option maxRecDepth 500000 in
theorem vvc1_after_alloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) (x : VecVecClone1Ghost) (st : M.σ)
    (s0 s : State) (R : SepProp) (q : BitVec 64)
    (hs0_align : s0.spAligned = true) (hq : q ≠ 0#64)
    (hfit : FitsEnv M lim st (VecVecClone1Env x))
    (hpc : s.pc = (blkPl_117).base + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 24 8) st) s ∗
        stackAt (s0.sp - 96#64) extHookStack ∗ vvc1Saved s0 ∗
        A.repAlloc.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A lim x st s0 R) (vvc1Qp A lim x st s0 R) := by
  intro hcl
  rw [vvc1_src_eq]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.pure_elim fun ⟨hlen, hcap63, hptr⟩ => ?_
  by_cases henc : x.enc = []
  · have hL : BitVec.ofNat 64 x.enc.length = 0#64 := by rw [henc]; rfl
    rw [hL]
    refine vvc1_nil_placed x st s0 s R q cap ptr _ henc hq hs0_align ?_
      hpc hrun hsp hx0 hx19 hx20 hx21 hx22 htrace hvregs hcl
    have h := vvc1_src_fold A x.src cap ptr x.enc ⟨hlen, hcap63, hptr⟩
    rw [hL] at h; exact h
  · have hpos : 0 < x.enc.length := List.length_pos_iff.mpr henc
    have hcap : ¬ (cap = 0) := by
      intro h; subst h
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0] at hlen; omega
    have hfold := vvc1_src_fold A x.src cap ptr x.enc ⟨hlen, hcap63, hptr⟩
    simp only [hcap, ↓reduceIte] at hfold
    simp only [hcap, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (vvc1_cons_placed hC x st s0 s R q cap ptr
        (A.repAlloc.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 x.enc.length) (cap.toNat - x.enc.length))
        hpos (by omega) hq hs0_align (fitsEvents_inner_of_fitsEnv hpos hfit)
        (Entails.trans (Entails.of_eq (by sep_ac_rfl)) hfold)
        hpc hrun hsp hx0 hx19 hx20 hx21 hx22 htrace hvregs hcl)

/-! ## Entry and Top-Level Contract (`lsmpl.base 117`) -/

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
theorem vvc1_entry_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) (x : VecVecClone1Ghost) (st : M.σ)
    (s0 : State) (R : SepProp)
    (hpc : s0.pc = lsmpl.base 117) (hrun : s0.status = .Running)
    (hs0_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src)
    (hx2 : s0.readReg64 .x2 = 1#64) (hfit : FitsEnv M lim st (VecVecClone1Env x)) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 Reg.lr) s0
      (arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗
        A.pool lim st s0 ∗ stackAt s0.sp vecVecClone1StackX)
      (vvc1Q A lim x st s0 R) (vvc1Qp A lim x st s0 R) := by
  intro hcl
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hx2' : s0.readReg64 (Reg.gpr 2#5) = 1#64 := hx2
  have hafter := fun s' q => vvc1_after_alloc_placed (M := M) (A := A) (lim := lim) (H := H)
    hC x st s0 s' R q hs0_align
  change s0.pc = (blkPl_117).base at hpc
  have hsp_sub_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96 hs0_align (by decide)
  have hpos24 : 0 < 24 := by decide
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hsum24 : 24 + 8 ≤ 2 ^ 63 := by decide
  have hmax8 : 8 ≤ 2 ^ 31 := by decide
  have hlay24 : RustLayoutOk 24 8 := ⟨⟨hpos24, hpow8, hsum24⟩, hmax8⟩
  have hfit24 : FitsEvents M lim st (rustAllocEvents 24 8) := fitsEvents_outer24_of_fitsEnv hfit
  rw [vvc1_stack_split s0.sp]; unfold vvc1Cells
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 =>
    SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 =>
    SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
    SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => ?_
  apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_shim
  have hshim_call := lscall_of_withLsCl
    (hC.alloc.shim (callerProg := (blkPC_117).rebase (blkPl_117).base H)) hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := lsρ lsRustAllocSym)
  wp_call hshim_call ()
  have htr_shim : sf.trace = s0.trace := by simpa only [wp_norm, arm64_norm, *] using ‹sf.trace = _›
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_alloc
  have halloc_call := hC.alloc.allocNoOom_call
    (callerProg := (blkPC_117).rebase (blkPl_117).base H) hcl_alloc
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_117).base + bv% (68))
  wp_call halloc_call (24, 8, st)
  have htr_alloc : sf_1.trace = s0.trace :=
    ‹AllocCallPreserved _ sf_1›.2.1.trans (by simp only [wp_norm, arm64_norm, *])
  have hq_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 .x0 ≠ 0#64›
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_post_alloc
  have hlive24 : A.live (sf_1.readReg64 .x0) 24 8 =
      A.repAlloc.live (sf_1.readReg64 (Reg.gpr 0#5)) 24 8 := rfl
  refine SepWPp.weaken_pre (Entails.of_eq (by
      rw [show sf.sp = s0.sp - 96#64 by simp only [wp_norm, arm64_norm, *], hlive24]
      unfold vvc1Saved; sep_ac_rfl))
    (hafter sf_1 (sf_1.readReg64 (Reg.gpr 0#5)) hq_ne hfit
      ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ hcl_post_alloc)
  all_goals simp only [wp_norm, arm64_norm, *]

/-- Budget-threaded `<Vec<Vec<u8>> as Clone>::clone` on `len = 1` satisfies
`withLsCodeLoaded lsmpl (vecVecClone1SpecX M A lim)` at `lsmpl.base 117`. -/
theorem vecVecClone1_placed_okX_of_ser [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    VecVecClone1PlacedOkStmt M A lim H := by
  unfold VecVecClone1PlacedOkStmt
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  intro ⟨x, st⟩ R s0 hpc hrun hpre hs0_align
  simp only [vecVecClone1SpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hfit⟩, hm⟩ := hpre
  exact ⟨_, R, by simpa only [sepConj_assoc] using hm,
    vvc1_entry_placed hC x st s0 R hpc hrun hs0_align hx0 hx1 hx2 hfit⟩

theorem vecVecClone1_placed_ok_cl_of_ser [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (blkPl_117).base (withLsCl lsmpl (vecVecClone1SpecX M A lim)) :=
  vecVecClone1_placed_ok_cl (callerProg := callerProg) (vecVecClone1_placed_okX_of_ser hC)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClonePlacedBudget
