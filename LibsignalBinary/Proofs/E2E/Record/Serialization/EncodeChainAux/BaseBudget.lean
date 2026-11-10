/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Base
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-threaded callee stepping helpers for `encode::<Chain, Vec<u8>>`

Relocatable `[LibsignalPlacement]` helpers for block `12` (`lsProg_12 H`), threading
`LibsignalCodeLoaded`, `VmPreserved`, and `A.pool lim st` across `encode_varint`,
`do_reserve_and_handle`, and `memcpy` calls.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open CryptoVerification (
  LibsignalPlacement lsmpl LibsignalCodeLoaded withLsCodeLoaded sepWP_mono_lscl
  ls_subroutine_ok_of_block subroutine_ok_withLsCodeLoaded_of_plain
  lsMemcpySym lsρ ls_hook_ok_of_mem blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.RustHeap (
  vecHeader vecU8At
)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (
  reserveCap doReserveStack DoReserveCall
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  encodeVarintStack EncodeVarintGhost vecU8Buf vecU8At_eq_header_sep_buf reserveCap_bounds
)
open CryptoVerification.E2E.Record.Placed (lsProg_12)
open CryptoVerification.E2E.Record.Serialization (
  encChainSubStack sp_sub_96_aligned stackAt_sub_to_encodeVarint stackAt_sub_to_doReserve
  vecSliceRest vecU8Buf_eq_open_slice vecU8Buf_append_slice_eq
  reserveCap_slice_bounds trVRegs_of_call
)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents doReserveSpec doReserveSpecWithStack framelessMemcpyBudgetSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Lifts a `SepWP` basic block into `SepWPp` while threading `LibsignalCodeLoaded` and `VmPreserved`. -/
theorem sepWPp_of_sepWP_lscl_vm {prog : Program} {pl : MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧
        (LibsignalCodeLoaded pl sm.mem → VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm ⟨hvm, hnext⟩ => hnext hclm hvm)

/-- Steps a total-correctness `withLsCodeLoaded` call inside `SepWPp` for arbitrary panic postcondition `Qp`. -/
theorem sepWPp_call_lscl_noPanic {α : Type} {prog : Program} {pl : MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → LibsignalCodeLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre' : s.mem ⊨ (withLsCodeLoaded pl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm (hcl.of_keepsFrozen hsteps.keepsFrozen)
        hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hpanic sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hexit code sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hoom sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Bridges `HookSat H "memcpy" allocMemcpyVmSpec` to `HookSat H lsMemcpySym framelessMemcpyBudgetSpec`. -/
theorem hookSat_framelessMemcpyBudget_of_allocMemcpyVm
    {H : String → Option (State → State)}
    (hmc : HookSat H "memcpy" allocMemcpyVmSpec) :
    HookSat H lsMemcpySym framelessMemcpyBudgetSpec := by
  change HookSat H "memcpy" framelessMemcpyBudgetSpec
  refine HookSat.mono hmc fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  dsimp only [framelessMemcpyBudgetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat⟩, hrest⟩
  have hlt64 : bs.length < 2 ^ 64 := hx2_nat ▸ (s0.readReg64 .x2).isLt
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [allocMemcpyVmSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlt64⟩, ?_⟩
    simpa only [sepConj_assoc] using hrest
  · dsimp only [allocMemcpyVmSpec] at hpost
    dsimp only [framelessMemcpyBudgetSpec]
    rw [sepConj_assoc] at hpost
    rw [sepConj_assoc, sepConj_assoc]
    rw [satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hret, hacp, hvm⟩, hmem⟩
    refine ⟨⟨hret, hacp.2.1, hvm⟩, ?_⟩
    simpa only [sepConj_assoc] using hmem

theorem step_encChain_encodeVarint_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (val v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs →
      curCap.toNat ≤ cap'.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat → cap' = curCap ∧ ptr' = curPtr) →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  have hEV' : subroutine_ok (lsProg_12 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hEV
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPp_call_lscl_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, st))
    (F := memRegion (sp0 - 96#64 - 8544#64) 4288 ∗ F)
    hEV' hpc hrun hsp_aligned hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint (sp0 - 96#64)] at hm
    simp only [encodeVarintSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr (by omega), hfit⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun cap' =>
      SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.pure_elim fun ⟨hcap_le, hspare⟩ => ?_
    have hPullEvs :
        (vecU8At A.repAlloc v cap' ptr' (curBs ++ encodeVarint val) ∗
          ⌜EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 96#64) encodeVarintStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4288 ∗ F) =
        (⌜EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs⌝ ∗
          ((vecU8At A.repAlloc v cap' ptr' (curBs ++ encodeVarint val) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (sp0 - 96#64) encChainSubStack) ∗ F)) := by
      rw [stackAt_sub_to_encodeVarint (sp0 - 96#64)]
      sep_ac_rfl
    rw [hPullEvs]
    refine SepWPp.pure_elim fun hevs => ?_
    exact hnext sm cap' ptr' evs hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm
      hevs hcap_le hspare

theorem step_encChain_reserve1_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (st : M.σ)
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs 1)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length < newCap.toNat →
      newCap = BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1) →
      SepWPp (lsProg_12 H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) sm ∗
          stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  have hDR' : subroutine_ok (lsProg_12 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hDR
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_gt, _⟩ := reserveCap_bounds (len := curBs.length) (by omega)
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine sepWPp_call_lscl_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs 1, st))
    (F := memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F)
    hDR' hpc hrun hsp_aligned hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve (sp0 - 96#64)] at hm
    simp only [doReserveSpec, doReserveSpecWithStack,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_, hfit⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpec, doReserveSpecWithStack,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)) p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) sm ∗
          stackAt (sp0 - 96#64) doReserveStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F) =
        (((v ↦₆₄ BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) sm ∗
          stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [hcap_eq, stackAt_sub_to_doReserve (sp0 - 96#64)]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_gt rfl

theorem step_encChain_reserveSlice_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (st : M.σ)
    (hle : curBs.length ≤ curCap.toNat)
    (hrem : curCap.toNat - curBs.length < add)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hadd_lt : add < 2 ^ 32)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs add)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length + add ≤ newCap.toNat →
      ((newCap - BitVec.ofNat 64 curBs.length).ult (BitVec.ofNat 64 add)) = false →
      newCap = BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add) →
      SepWPp (lsProg_12 H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc newCap p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)) st) sm ∗
          stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  have hDR' : subroutine_ok (lsProg_12 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hDR
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_ge, hult_false⟩ := reserveCap_slice_bounds hle hrem hlen_lt hadd_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = add := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_call_lscl_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs add, st))
    (F := memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F)
    hDR' hpc hrun hsp_aligned hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve (sp0 - 96#64)] at hm
    simp only [doReserveSpec, doReserveSpecWithStack,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, hres_bound, hfit⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpec, doReserveSpecWithStack,
      vecU8At_eq_header_sep_buf, vecHeader, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)) st) sm ∗
          stackAt (sp0 - 96#64) doReserveStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F) =
        (((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)) st) sm ∗
          stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [stackAt_sub_to_doReserve (sp0 - 96#64)]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p'
      hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_ge hult_false rfl

theorem step_encChain_memcpy_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (curCap curPtr srcPtr sp0 ret_pc : BitVec 64) (curBs sliceBs : List (BitVec 8))
    (st : M.σ)
    (hpos : 0 < sliceBs.length)
    (hle : curBs.length + sliceBs.length ≤ curCap.toNat)
    (hslice_lt : sliceBs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = curPtr + BitVec.ofNat 64 curBs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 sliceBs.length)
    (hP : P = (vecU8Buf A.repAlloc curCap curPtr curBs ∗
      (srcPtr ↦ₛ sliceBs) ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State),
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8Buf A.repAlloc curCap curPtr (curBs ++ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗ A.pool lim st sm) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  have hmc' : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl framelessMemcpyBudgetSpec) :=
    subroutine_ok_withLsCodeLoaded_of_plain (ls_hook_ok_of_mem (prog := lsProg_12 H) hmc)
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hx2_toNat : (s.readReg64 .x2).toNat = sliceBs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_call_lscl_noPanic (x := (curPtr + BitVec.ofNat 64 curBs.length, srcPtr, sliceBs))
    (F := vecSliceRest A.repAlloc curCap curPtr curBs sliceBs.length ∗ A.pool lim st s ∗ F)
    hmc' hpc hrun hsp_aligned hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_open_slice A.repAlloc curCap curPtr curBs sliceBs.length hpos hle] at hm
    simp only [framelessMemcpyBudgetSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_toNat⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [framelessMemcpyBudgetSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm, hvm⟩ => ?_
    have hGoalEq :
        (((curPtr + BitVec.ofNat 64 curBs.length) ↦ₛ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗
          vecSliceRest A.repAlloc curCap curPtr curBs sliceBs.length ∗
          A.pool lim st s ∗ F) =
        ((vecU8Buf A.repAlloc curCap curPtr (curBs ++ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗ A.pool lim st sm) ∗ F) := by
      rw [← vecU8Buf_append_slice_eq A.repAlloc curCap curPtr curBs sliceBs hpos hle,
          A.pool_of_vmPreserved hvm]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm hvm hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm

end LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget
