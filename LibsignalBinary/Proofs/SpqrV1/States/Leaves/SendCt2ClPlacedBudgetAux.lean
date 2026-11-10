/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275 -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: `LibsignalCodeLoaded` Auxiliary Segments (Block `347`)

`LibsignalCodeLoaded`-preserving `SepWPp` call combinators and budget-threaded relocatable
Segments 2–4 (`+136 → +676` plus slow path `+1036..+1060`) for
`<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_347 blkPl_347
  libsignalSessionCode lsLogFilterAddr lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall doReserveStack extHookStack reserveCap
)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem flipEndiannessOfEncapsulationStateBytes issue1275NeedsFlip
  mlkemEncaps2Spec spqrAuthApi
)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym
)
open CryptoVerification.SpqrV1.Auth (toBEBytes_8_length)
open CryptoVerification.SpqrV1.States.Leaves (UnchunkedSendCt2Ghost)
open CryptoVerification.SpqrV1.Unchunked (
  cap_ne_zero_of_add_128_le ctLabel_length es_scan_split es_swap_join es_swap_split
  exists_unpack64_of_length_128 fold_vecU8At_sp_304 le_of_not_ule_sub_len
  memRegion_128_cells reserveCap_bound_of_ule_sub_len reserveCap_ge_add_128
  reserveCap_ne_zero_len sendCt2EsAfterWorkAt sendCt2EsWorkAt sendCt2EsWorkAt_entails
  spqrMlkemEncaps2Sym spqrRustDeallocSym stackAt_extHook_eq_allocHook
  stackAt_extHook_eq_doReserve vecU8At_expose_sp_304_cells_heap
  vecU8At_expose_sp_304_of_ne_zero vecU8HeapAt vecU8HeapAt_expose_of_ne_zero
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveSpec)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget (of_sepWP_lscl)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget (
  sepWPp_call_frozen_noPanic
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (sepWPp_pure_left_focus)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  SendCt2Reserve128Env UnchunkedSendCt2PreEnv doReserveEvents_128_eq
  fitsEnv_doReserve128_of_fitsEvents fitsEvents_alloc128_of_seg23
  fitsEvents_flipAlloc_of_preEnv fitsEvents_reserve128_of_preEnv
  fitsEvents_seg23_of_preEnv scan_loop_false_placed_pool_ok
  scan_loop_true_placed_pool_ok sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
  sendCt2Reserve128Events sendCt2Seg23Events sepWPp_exists_left_eq
  sepWPp_fold_eq sepWPp_intro_state sepWPp_pure_left_eq sepWPp_rw_pre_eq
  sepWPp_weaken_pre swap_loop_placed_pool_ok
)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  toBEBytes_8_length ctLabel_length

local macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

/-! ## 1. `LibsignalCodeLoaded`-Preserving `SepWPp` Call Combinators -/

/-- `SepWPp` subroutine call rule for a plain non-panicking `spec` that preserves
    `LibsignalCodeLoaded lsmpl` via `Memory.KeepsFrozen`. -/
theorem sepWPp_call_lscl_noPanic [LibsignalPlacement] {α : Type}
    {prog : Program} {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (x : α) (F : SepProp)
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom :=
  sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf)
    hcl hcall (x := x) (F := F) hexit_eq hpan_eq hoom_eq hpc hrun hsp hlr hpre hnext

/-- `SepWPp` subroutine call rule for a `withLsCodeLoaded lsmpl spec` callee that supplies
    `LibsignalCodeLoaded lsmpl s.mem` in the precondition and preserves it to `sf.mem`. -/
theorem sepWPp_call_withLscl_noPanic [LibsignalPlacement] {α : Type}
    {prog : Program} {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (x : α) (F : SepProp)
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf)
    hcl hcall (x := x) (F := F) hexit_eq hpan_eq hoom_eq hpc hrun hsp hlr ?_ hnext
  intro R hm
  have hm' := hpre R hm
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hm'⟩

/-- Framed `SepWPp` call rule for `withVmPreserved (mlkemEncaps2Spec K)` preserving
    `LibsignalCodeLoaded lsmpl` and syncing `A.pool lim stCost`. -/
theorem call_mlkemEncaps2_vm_lscl_wpp [LibsignalPlacement] {K : MlKem} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    {s0 s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog fnAddr (withVmPreserved (mlkemEncaps2Spec K)))
    (ret esA ekA : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (stCost : M.σ)
    {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = ret)
    (hx0 : s.readReg64 Reg.x0 = esA) (hx1 : s.readReg64 Reg.x1 = ekA)
    (hsplit : P = ((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
      memRegion ret 128 ∗ stackAt sp_call extHookStack ∗
      A.pool lim stCost s) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf
        (((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
          (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack ∗
          A.pool lim stCost sf) ∗ Frame) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_lscl_noPanic hcl hcall ⟨ret, esA, esVec, ekA, ekVec⟩
    (A.pool lim stCost s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withVmPreserved, mlkemEncaps2Spec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1⟩,
      Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm⟩
  · dsimp only [withVmPreserved, mlkemEncaps2Spec]
    rw [hsp, htrace]
    refine sepWPp_pure_left_eq (φ := VmPreserved s sf)
      (⌜sf.trace = s0.trace⌝ ∗
        (esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
        (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack ∗
        A.pool lim stCost s ∗ Frame)
      (by sep_ac_rfl) ?_
    intro hvm
    refine sepWPp_pure_left_eq (φ := sf.trace = s0.trace)
      ((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
        (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack ∗
        A.pool lim stCost s ∗ Frame)
      (by sep_ac_rfl) ?_
    intro htr_sf
    rw [← A.pool_of_vmPreserved hvm]
    exact sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) htr_sf hcs_sf hcl_sf)

/-- Framed `SepWPp` call rule for `rustCliAllocNoOomSpec M A lim false` preserving
    `LibsignalCodeLoaded lsmpl` and `CalleeSavedPreserved s sf`. -/
theorem call_rustAllocNoOom_cs_lscl_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog fnAddr (rustCliAllocNoOomSpec M A lim false))
    (size align : Nat) (stCost : M.σ)
    (hlay : RustLayoutOk size align)
    (hFit : FitsEvents M lim stCost (rustAllocEvents size align))
    {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool lim stCost s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → AllocCallPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.readReg64 .x0 ≠ 0#64 → (sf.readReg64 .x0).toNat % align = 0 →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_lscl_noPanic hcl hcall (size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliAllocNoOomSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hFit, hlr ▸ hlr_ls⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp]
    refine sepWPp_pure_left_eq
      (φ := AllocCallPreserved s sf ∧ (sf.readReg64 .x0).toNat % align = 0 ∧
        sf.readReg64 .x0 ≠ 0#64)
      ((A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack ∗
        A.live (sf.readReg64 .x0) size align ∗
        memRegion (sf.readReg64 .x0) size) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, hmod, hne⟩
    exact sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hacp hcl_sf hne hmod)

/-- Framed `SepWPp` call rule for `rustCliDeallocBudgetSpec M A lim` preserving
    `LibsignalCodeLoaded lsmpl`. -/
theorem call_rustDealloc_cs_lscl_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    {s0 s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog fnAddr (rustCliDeallocBudgetSpec M A lim))
    (ptr : BitVec 64) (size align : Nat) (stCost : M.σ)
    {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = ptr)
    (hx1 : (s.readReg64 Reg.x1).toNat = size) (hx2 : (s.readReg64 Reg.x2).toNat = align)
    (hsplit : P = (A.pool lim stCost s ∗ A.live ptr size align ∗ memRegion ptr size ∗
      stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf
        ((A.pool lim (M.stepEvents (rustDeallocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_lscl_noPanic hcl hcall (ptr, size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliDeallocBudgetSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlr ▸ hlr_ls⟩,
      Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm⟩
  · dsimp only [rustCliDeallocBudgetSpec]
    rw [hsp]
    refine sepWPp_pure_left_eq
      (φ := AllocCallPreserved s sf ∧
        M.liveBytes (M.stepEvents (rustDeallocEvents size align) stCost) ≤ M.liveBytes stCost)
      ((A.pool lim (M.stepEvents (rustDeallocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, _⟩
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hacp.2.1.trans htrace) hcs_sf hcl_sf

/-! ## 2. Segment 2 (`+136 → +552`, including `+472 → +516`): Scan + Optional Issue-1275 Flip -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded 2080-byte workspace allocation and `memcpy`
    (`+472 → +516`) preserving `LibsignalCodeLoaded lsmpl`. -/
theorem send_ct2_5d8_to_604_cl_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hFit : FitsEvents M lim stCost (rustAllocEvents 2080 1))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 472#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      esWorkPtr ≠ 0#64 →
      st'.pc = (blkPl_347).base + 516#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x8 = 0#64 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = 2080#64 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ x.st.es) ∗
          A.live esWorkPtr 2080 1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp := by
  have hallocNoOom := subroutine_ok_allocNoOom_of_budget halloc
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19
  refine of_sepWP_lscl hcl (mid := lsρ spqrRustNoAllocShimSym) ?_
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_shim0 => ?_
  refine sepWPp_intro_state fun s_shim hs_shim => ?_
  have hcl_s_shim : LibsignalCodeLoaded lsmpl s_shim.mem := by rw [hs_shim]; exact hcl_shim0
  rw [← hs_shim]
  have hsp_shim : s_shim.sp = s0.sp - 336#64 := by
    simp only [hs_shim, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_lscl_noPanic hcl_s_shim hshim ()
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_shim ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by rw [hs_shim]; wp_norm_goal)
    (by simp only [hs_shim, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_shim]; exact hfsp_align)
    (ret_pc := (blkPl_347).base + 476#64)
    (by simp only [hs_shim, Reg.lr, wp_norm, arm64_norm, *])
    (fun R' hm => by
      dsimp only [rustAllocShimVmSpec]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by simp only [emp_sepConj]; sep_ac_rfl)) hm)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_shim hpc_shim hrun_shim hsp_shim_rel hcs_shim hcl_sf_shim => ?_)
  dsimp only [rustAllocShimVmSpec]
  refine sepWPp_pure_left_eq (φ := AllocCallPreserved s_shim sf_shim ∧ VmPreserved s_shim sf_shim)
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_shim ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by sep_ac_rfl) ?_
  rintro ⟨hacp_shim, hvm_shim⟩
  rw [← A.pool_of_vmPreserved hvm_shim]
  rcases hcs_shim with ⟨hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s,
    hx27_s, hx28_s, hfp_s, hvregs_s⟩
  simp only [hs_shim, wp_norm, arm64_norm] at hx19_s hx20_s hx21_s hx22_s hx23_s hx24_s
  simp only [hs_shim, wp_norm, arm64_norm] at hx25_s hx26_s hx27_s hx28_s hfp_s hvregs_s
  have htr_shim : sf_shim.trace = s0.trace := by
    have ht := hacp_shim.2.1
    simpa only [hs_shim, wp_norm, arm64_norm, htr] using ht
  have hsp_sf_shim : sf_shim.sp = s0.sp - 336#64 := hsp_shim_rel.trans hsp_shim
  have hsp_sf_shim_norm : sf_shim.readReg64 .sp = s0.sp - 336#64 := hsp_sf_shim
  simp only [wp_norm, arm64_norm] at hsp_sf_shim_norm
  refine of_sepWP_lscl hcl_sf_shim (mid := lsρ spqrRustAllocSym) ?_
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_alloc0 => ?_
  refine sepWPp_intro_state fun s_alloc hs_alloc => ?_
  have hcl_s_alloc : LibsignalCodeLoaded lsmpl s_alloc.mem := by rw [hs_alloc]; exact hcl_alloc0
  rw [← hs_alloc]
  have hstack_alloc :
      stackAt (s0.sp - 336#64) extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine sepWPp_fold_eq
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_alloc ∗ F_frame)
    hstack_alloc (by sep_ac_rfl) ?_
  have hlay_2080 : RustLayoutOk 2080 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  refine call_rustAllocNoOom_cs_lscl_wpp hcl_s_alloc hallocNoOom 2080 1 stCost hlay_2080 hFit
    (memRegion (s0.sp - 16720#64) 12288 ∗ (esPtr ↦ₛ x.st.es) ∗ F_frame)
    (ret_pc := (blkPl_347).base + 488#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_alloc]; wp_norm_goal)
    (by simp only [hs_alloc, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_alloc, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x1, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 hacp1 hcl1 hne1 _ => ?_)
  have htr1 : sf1.trace = s_alloc.trace := hacp1.2.1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
    hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [hs_alloc, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [hs_alloc, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1 htr1
  have htr1' : sf1.trace = s0.trace := htr1.trans htr_shim
  have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hne1
  have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
  simp only [wp_norm, arm64_norm] at hsp1_norm
  have hstack_back :
      memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
        stackAt (s0.sp - 336#64) extHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
  refine sepWPp_fold_eq
    (A.live (sf1.readReg64 .x0) 2080 1 ∗
      memRegion (sf1.readReg64 .x0) 2080 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) sf1 ∗
      (esPtr ↦ₛ x.st.es) ∗ F_frame)
    hstack_back (by sep_ac_rfl) ?_
  have hmr_es :
      memRegion (sf1.readReg64 .x0) 2080 ⊢
        memRegion (sf1.readReg64 .x0) x.st.es.length := by
    rw [hes_len]; exact Entails.refl _
  refine sepWPp_fold_eq
    (stackAt (s0.sp - 336#64) extHookStack ∗
      A.live (sf1.readReg64 .x0) 2080 1 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) sf1 ∗
      (esPtr ↦ₛ x.st.es) ∗ F_frame)
    hmr_es (by sep_ac_rfl) ?_
  refine of_sepWP_lscl hcl1 (mid := lsρ spqrMemcpySym) ?_
  wp_steps_sync_pool (lsρ spqrMemcpySym)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_mc0 => ?_
  refine sepWPp_intro_state fun s_mc hs_mc => ?_
  have hcl_s_mc : LibsignalCodeLoaded lsmpl s_mc.mem := by rw [hs_mc]; exact hcl_mc0
  rw [← hs_mc]
  have hsp_mc : s_mc.sp = s0.sp - 336#64 := by
    simp only [hs_mc, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_lscl_noPanic hcl_s_mc hmemcpy
    (sf1.readReg64 .x0, esPtr, x.st.es)
    (stackAt (s0.sp - 336#64) extHookStack ∗
      A.live (sf1.readReg64 .x0) 2080 1 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s_mc ∗ F_frame)
    (by rw [hs_mc]; wp_norm_goal)
    (by simp only [hs_mc, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_mc]; exact hfsp_align)
    (ret_pc := (blkPl_347).base + 512#64)
    (by simp only [hs_mc, Reg.lr, wp_norm, arm64_norm, *])
    ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_mc hpc_mc hrun_mc hsp_mc_rel hcs_mc hcl_sf_mc => ?_)
  · intro R' hm
    dsimp only [framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [hs_mc, Reg.x0, wp_norm, arm64_norm, *]
    · simp only [hs_mc, Reg.x1, wp_norm, arm64_norm, *]
    · simp only [hs_mc, Reg.x2, hes_len, wp_norm, arm64_norm, *]
    · exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
  · dsimp only [framelessMemcpyAcpSpec]
    refine sepWPp_pure_left_eq
      (φ := sf_mc.readReg64 .x0 = sf1.readReg64 .x0 ∧ AllocCallPreserved s_mc sf_mc ∧ VmPreserved s_mc sf_mc)
      (((sf1.readReg64 .x0) ↦ₛ x.st.es) ∗ (esPtr ↦ₛ x.st.es) ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        A.live (sf1.readReg64 .x0) 2080 1 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s_mc ∗ F_frame)
      (by sep_ac_rfl) ?_
    rintro ⟨_, hacp_mc, hvm_mc⟩
    rw [← A.pool_of_vmPreserved hvm_mc]
    rcases hcs_mc with ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m,
      hx27_m, hx28_m, hfp_m, hvregs_m⟩
    simp only [hs_mc, wp_norm, arm64_norm] at hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
    simp only [hs_mc, wp_norm, arm64_norm] at hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    have htr_mc : sf_mc.trace = s0.trace := by
      have ht := hacp_mc.2.1
      simpa only [hs_mc, wp_norm, arm64_norm, htr1'] using ht
    have hsp_sf_mc : sf_mc.sp = s0.sp - 336#64 := hsp_mc_rel.trans hsp_mc
    have hsp_sf_mc_norm : sf_mc.readReg64 .sp = s0.sp - 336#64 := hsp_sf_mc
    simp only [wp_norm, arm64_norm] at hsp_sf_mc_norm
    refine of_sepWP_lscl hcl_sf_mc (mid := (blkPl_347).base + 516#64) ?_
    wp_steps_sync_pool ((blkPl_347).base + 516#64)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_end => ?_
    refine sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hcont _ (sf1.readReg64 .x0) hcl_end hne1
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hvregs_m, hvregs_1, hvregs_s, hvregs])
        (by simp only [Reg.x8, wp_norm, arm64_norm, *])
        (by simp only [Reg.x19, wp_norm, arm64_norm, *])
        (by simp only [Reg.x20, wp_norm, arm64_norm, *])
        (by simp only [Reg.x22, Reg.x0, wp_norm, arm64_norm, *])
        (by simp only [Reg.x23, wp_norm, arm64_norm, *])
        (by simp only [Reg.x24, wp_norm, arm64_norm, *])
        (by simp only [Reg.x25, wp_norm, arm64_norm, *])
        (by simp only [Reg.x26, wp_norm, arm64_norm, *])
        (by simp only [Reg.x27, wp_norm, arm64_norm, *])
        (by simp only [Reg.x28, wp_norm, arm64_norm, *])
        (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded Segment 2 (`+136 → +552`) preserving
    `LibsignalCodeLoaded lsmpl`. -/
theorem send_ct2_scan_to_628_cl_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hFit : FitsEvents M lim stCost (sendCt2FlipAllocEvents x.st.es))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      st'.pc = (blkPl_347).base + 552#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp := by
  have hlen512 : ((x.st.es.drop 1536).take 512).length = 512 := by
    rw [List.length_take, List.length_drop, hes_len]; rfl
  have hbs_ne : (x.st.es.drop 1536).take 512 ≠ [] := by
    intro hnil; rw [hnil] at hlen512; contradiction
  have hbs_mod : ((x.st.es.drop 1536).take 512).length % 2 = 0 := by rw [hlen512]
  have hbs_le : ((x.st.es.drop 1536).take 512).length ≤ 512 := by omega
  have hrem_eq : (512#64 : BitVec 64) = BitVec.ofNat 64 ((x.st.es.drop 1536).take 512).length := by
    rw [hlen512]
  have hpre_split : ∀ (P_pool : SepProp),
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        P_pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) =
      (((esPtr + 1536#64) ↦ₛ ((x.st.es.drop 1536).take 512)) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        P_pool ∗
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
    intro P_pool
    rw [es_scan_split esPtr x.st.es hes_len]
    sep_ac_rfl
  by_cases hflip : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = false
  · refine of_sepWP_lscl hcl (mid := (blkPl_347).base + 552#64) ?_
    rw [hpre_split (A.pool lim stCost st)]
    refine SepWP.mono
      (scan_loop_false_placed_pool_ok A lim stCost
        (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hbs_ne hbs_mod hbs_le hrem_eq hflip hpc hrun hx8 hx9 hx10 hx11 hx13 hx28) ?_
    rintro sf Pf hpc_sf hrun_sf ⟨hPf, hx21_sf, hx22_sf, hx28_sf, hsaved, _⟩ hcl_sf
    have hwork : (esPtr ↦ₛ x.st.es) ⊢ sendCt2EsWorkAt A.repAlloc esPtr esPtr x.st.es := by
      unfold sendCt2EsWorkAt
      simp only [hflip, Bool.false_eq_true, ↓reduceIte]
      exact Entails.pure_right trivial (Entails.refl _)
    have hevs_nil : sendCt2FlipAllocEvents x.st.es = [] := by
      unfold sendCt2FlipAllocEvents
      simp only [hflip, Bool.false_eq_true, ↓reduceIte]
    have hPf_back : Pf ⊢
        sendCt2EsWorkAt A.repAlloc esPtr esPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) sf ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf, ← hpre_split (A.pool lim stCost sf), hevs_nil, M.stepEvents_nil]
      exact sepConj_mono_left hwork
    refine sepWPp_weaken_pre hPf_back ?_
    exact hcont sf esPtr hcl_sf hpc_sf hrun_sf
      (hsaved.sp.trans hsp) (hsaved.trace.trans htr) (hsaved.vregs.trans hvregs)
      (hsaved.x19.trans hx19) hsaved.x20
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx21_sf])
      (hx22_sf.trans hx19)
      hsaved.x23 hsaved.x24 hsaved.x25 hsaved.x26 hsaved.x27
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx28_sf])
      hsaved.x29
  · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
      Bool.eq_true_of_not_eq_false hflip
    have hevs_alloc : sendCt2FlipAllocEvents x.st.es = rustAllocEvents 2080 1 := by
      unfold sendCt2FlipAllocEvents
      simp only [hflip_t, ↓reduceIte]
    have hFit2080 : FitsEvents M lim stCost (rustAllocEvents 2080 1) := by
      rwa [← hevs_alloc]
    refine of_sepWP_lscl hcl (mid := (blkPl_347).base + 472#64) ?_
    rw [hpre_split (A.pool lim stCost st)]
    refine SepWP.mono
      (scan_loop_true_placed_pool_ok A lim stCost
        (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hbs_ne hbs_mod hbs_le hrem_eq hflip_t hpc hrun hx8 hx9 hx10 hx11 hx13) ?_
    rintro s5d8 P5d8 hpc_5d8 hrun_5d8 ⟨hP5d8, hsaved1, _⟩ hcl_5d8
    have hP5d8_eq : P5d8 =
        (esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s5d8 ∗ stackAt (s0.sp - 336#64) extHookStack ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) := by
      rw [hP5d8, ← hpre_split (A.pool lim stCost s5d8)]
      sep_ac_rfl
    rw [hP5d8_eq]
    refine send_ct2_5d8_to_604_cl_placed_wpp hshim halloc hmemcpy
      x stCost esPtr s0 s5d8 ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame)
      hcl_5d8 hFit2080 hes_len hpc_5d8 hrun_5d8
      (hsaved1.sp.trans hsp) hsp_s0 (hsaved1.trace.trans htr)
      (hsaved1.vregs.trans hvregs) (hsaved1.x19.trans hx19) ?_
    intro s604 esWorkPtr hcl604 hwork_ne hpc604 hrun604 hsp604 htr604 hvregs604
      hx8_604 hx19_604 hx20_604 hx22_604 hx23_604 hx24_604 hx25_604 hx26_604
      hx27_604 hx28_604 hx29_604
    refine of_sepWP_lscl hcl604 (mid := (blkPl_347).base + 552#64) ?_
    have h2048_len : (x.st.es.take 2048).length = 2048 := by
      rw [List.length_take, hes_len]; rfl
    have h2048_ne : x.st.es.take 2048 ≠ [] := by
      intro hnil; rw [hnil] at h2048_len; contradiction
    have h2048_mod : (x.st.es.take 2048).length % 2 = 0 := by rw [h2048_len]
    have h2048_sum : (0#64 : BitVec 64).toNat + (x.st.es.take 2048).length = 2048 := by
      rw [h2048_len]; rfl
    have hsplit_swap :
        (esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s604 ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) =
        (((esWorkPtr + 0#64) ↦ₛ (x.st.es.take 2048)) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s604 ∗
          (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
            (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
      rw [es_swap_split esWorkPtr x.st.es hes_len]
      sep_ac_rfl
    rw [hsplit_swap]
    refine SepWP.mono
      (swap_loop_placed_pool_ok A lim (M.stepEvents (rustAllocEvents 2080 1) stCost)
        esWorkPtr (x.st.es.take 2048) 0#64 s604
        (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
          (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        h2048_ne h2048_mod h2048_sum hpc604 hrun604 hx22_604 hx8_604) ?_
    rintro st' Pf2 hpc' hrun' ⟨hPf2, hx21', hsaved2, _⟩ hcl'
    have hwork :
        (esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1 ⊢
          sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es := by
      unfold sendCt2EsWorkAt
      simp only [hflip_t, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      exact Entails.pure_right hwork_ne (Entails.of_eq (by sep_ac_rfl))
    have hPf2_reord :
        ((esWorkPtr + 0#64) ↦ₛ CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs (x.st.es.take 2048)) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
            (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) =
        (((esWorkPtr + 0#64) ↦ₛ CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs (x.st.es.take 2048)) ∗
          ((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      sep_ac_rfl
    have hpost_ent : Pf2 ⊢
        sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf2, hPf2_reord, es_swap_join esWorkPtr x.st.es hes_len, hevs_alloc]
      refine Entails.trans (Entails.of_eq (show _ =
        ((esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1) ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hwork
    refine sepWPp_weaken_pre hpost_ent ?_
    exact hcont st' esWorkPtr hcl' hpc' hrun'
      (hsaved2.sp.trans hsp604) (hsaved2.trace.trans htr604) (hsaved2.vregs.trans hvregs604)
      (hsaved2.x19.trans hx19_604)
      ((hsaved2.x20.trans hx20_604).trans hsaved1.x20)
      (by simp only [hflip_t, ↓reduceIte, hx21'])
      (hsaved2.x22.trans hx22_604)
      ((hsaved2.x23.trans hx23_604).trans hsaved1.x23)
      ((hsaved2.x24.trans hx24_604).trans hsaved1.x24)
      ((hsaved2.x25.trans hx25_604).trans hsaved1.x25)
      ((hsaved2.x26.trans hx26_604).trans hsaved1.x26)
      ((hsaved2.x27.trans hx27_604).trans hsaved1.x27)
      (by simp only [hflip_t, ↓reduceIte, hsaved2.x28.trans hx28_604])
      ((hsaved2.x29.trans hx29_604).trans hsaved1.x29)

/-- Specialization of `send_ct2_scan_to_628_cl_placed_wpp` under
    `FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x)`. -/
theorem send_ct2_scan_to_628_cl_placed_preEnv_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      st'.pc = (blkPl_347).base + 552#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim st0 st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp :=
  send_ct2_scan_to_628_cl_placed_wpp hshim halloc hmemcpy x st0 esPtr s0 st F_frame
    hcl (fitsEvents_flipAlloc_of_preEnv hPre) hes_len hpc hrun hsp hsp_s0 htr hvregs
    hx8 hx9 hx10 hx11 hx13 hx19 hx28 hcont

/-! ## 3. Segment 3 (`+552 → +656`): `encapsulate2`, `ct2` Alloc & Copy, Conditional Dealloc -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded Segment 3 (`+552 → +656`) preserving
    `LibsignalCodeLoaded lsmpl`. -/
theorem send_ct2_628_to_690_cl_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ)
    (esPtr ekPtr esWorkPtr : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hFit128 : FitsEvents M lim stCost (rustAllocEvents 128 1))
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hpc : st.pc = (blkPl_347).base + 552#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx21 : st.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64))
    (hx22 : st.readReg64 .x22 = esWorkPtr)
    (hx27 : st.readReg64 .x27 = 1152#64)
    (hx28 : st.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)))
    (hcont : ∀ (st' : State) (ptr_ct2 : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      ptr_ct2 ≠ 0#64 →
      st'.pc = (blkPl_347).base + 656#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = ekPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        A.pool lim stCost st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  have hallocNoOom := subroutine_ok_allocNoOom_of_budget halloc
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hek_beq : (ekPtr == 0#64) = false := beq_false_of_ne hekPtr_ne
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx27 hx28
  refine sepWPp_fold_eq
    ((ekPtr ↦ₛ x.st.ek) ∗ memRegion (s0.sp - 272#64) 128 ∗
      A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (sendCt2EsWorkAt_entails A.repAlloc esPtr esWorkPtr x.st.es hesVec)
    (by sep_ac_rfl) ?_
  refine sepWPp_rw_pre_eq (by rw [← hekVec]) ?_
  refine of_sepWP_lscl hcl (mid := lsρ spqrMlkemEncaps2Sym) ?_
  wp_steps_sync_pool (lsρ spqrMlkemEncaps2Sym)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_enc0 => ?_
  refine sepWPp_intro_state fun s_enc hs_enc => ?_
  have hcl_s_enc : LibsignalCodeLoaded lsmpl s_enc.mem := by rw [hs_enc]; exact hcl_enc0
  rw [← hs_enc]
  refine call_mlkemEncaps2_vm_lscl_wpp hcl_s_enc henc
    (s0.sp - 272#64) esWorkPtr ekPtr esVec ekVec stCost
    (sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame)
    (s0 := s0) (ret_pc := (blkPl_347).base + 580#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_enc]; wp_norm_goal)
    (by simp only [hs_enc, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_enc, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, Reg.x8, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, Reg.x1, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 hcl1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
    hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [hs_enc, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [hs_enc, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
  simp only [wp_norm, arm64_norm] at hsp1_norm
  refine of_sepWP_lscl hcl1 (mid := lsρ spqrRustNoAllocShimSym) ?_
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_shim0 => ?_
  refine sepWPp_intro_state fun s_shim hs_shim => ?_
  have hcl_s_shim : LibsignalCodeLoaded lsmpl s_shim.mem := by rw [hs_shim]; exact hcl_shim0
  rw [← hs_shim]
  have hsp_shim : s_shim.sp = s0.sp - 336#64 := by
    simp only [hs_shim, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_lscl_noPanic hcl_s_shim hshim ()
    (((esWorkPtr ↦ₛ esVec.toList) ∗ (ekPtr ↦ₛ ekVec.toList) ∗
      ((s0.sp - 272#64) ↦ₛ (K.encaps2 esVec ekVec).toList) ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ A.pool lim stCost s_shim) ∗
      (sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame))
    (by rw [hs_shim]; wp_norm_goal)
    (by simp only [hs_shim, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_shim]; exact hfsp_align)
    rfl
    (fun R' hm => by
      dsimp only [rustAllocShimVmSpec]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by simp only [emp_sepConj]; sep_ac_rfl)) hm)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_shim hpc_shim hrun_shim hsp_shim_rel hcs_shim hcl_sf_shim => ?_)
  simp only [hs_shim, Reg.lr, wp_norm, arm64_norm] at hpc_shim
  dsimp only [rustAllocShimVmSpec]
  refine sepWPp_pure_left_eq (φ := AllocCallPreserved s_shim sf_shim ∧ VmPreserved s_shim sf_shim)
    (((esWorkPtr ↦ₛ esVec.toList) ∗ (ekPtr ↦ₛ ekVec.toList) ∗
      ((s0.sp - 272#64) ↦ₛ (K.encaps2 esVec ekVec).toList) ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ A.pool lim stCost s_shim) ∗
      (sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame))
    (by sep_ac_rfl) ?_
  rintro ⟨hacp_shim, hvm_shim⟩
  rw [← A.pool_of_vmPreserved hvm_shim]
  rcases hcs_shim with ⟨hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s,
    hx27_s, hx28_s, hfp_s, hvregs_s⟩
  simp only [hs_shim, wp_norm, arm64_norm] at hx19_s hx20_s hx21_s hx22_s hx23_s hx24_s
  simp only [hs_shim, wp_norm, arm64_norm] at hx25_s hx26_s hx27_s hx28_s hfp_s hvregs_s
  have htr_shim : sf_shim.trace = s0.trace := by
    have ht := hacp_shim.2.1
    simpa only [hs_shim, wp_norm, arm64_norm, htr1] using ht
  have hsp_sf_shim : sf_shim.sp = s0.sp - 336#64 := hsp_shim_rel.trans hsp_shim
  have hsp_sf_shim_norm : sf_shim.readReg64 .sp = s0.sp - 336#64 := hsp_sf_shim
  simp only [wp_norm, arm64_norm] at hsp_sf_shim_norm
  refine of_sepWP_lscl hcl_sf_shim (mid := lsρ spqrRustAllocSym) ?_
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_alloc0 => ?_
  refine sepWPp_intro_state fun s_alloc hs_alloc => ?_
  have hcl_s_alloc : LibsignalCodeLoaded lsmpl s_alloc.mem := by rw [hs_alloc]; exact hcl_alloc0
  rw [← hs_alloc]
  have hstack_alloc :
      stackAt (s0.sp - 336#64) extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine sepWPp_fold_eq
    ((esWorkPtr ↦ₛ esVec.toList) ∗ (ekPtr ↦ₛ ekVec.toList) ∗
      ((s0.sp - 272#64) ↦ₛ (K.encaps2 esVec ekVec).toList) ∗
      A.pool lim stCost s_alloc ∗
      sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame)
    hstack_alloc (by sep_ac_rfl) ?_
  have hlay_128 : RustLayoutOk 128 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  refine call_rustAllocNoOom_cs_lscl_wpp hcl_s_alloc hallocNoOom 128 1 stCost hlay_128 hFit128
    (memRegion (s0.sp - 16720#64) 12288 ∗
      (esWorkPtr ↦ₛ esVec.toList) ∗ (ekPtr ↦ₛ ekVec.toList) ∗
      ((s0.sp - 272#64) ↦ₛ (K.encaps2 esVec ekVec).toList) ∗
      sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame)
    (ret_pc := (blkPl_347).base + 596#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_alloc]; wp_norm_goal)
    (by simp only [hs_alloc, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_alloc, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x1, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 hacp2 hcl2 hne2 _ => ?_)
  have htr2_raw : sf2.trace = s_alloc.trace := hacp2.2.1
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2,
    hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [hs_alloc, wp_norm, arm64_norm] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
  simp only [hs_alloc, wp_norm, arm64_norm] at hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2 htr2_raw
  have htr2 : sf2.trace = s0.trace := htr2_raw.trans htr_shim
  have hoom_false : (sf2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hne2
  have hsp2_norm : sf2.readReg64 .sp = s0.sp - 336#64 := hsp2
  simp only [wp_norm, arm64_norm] at hsp2_norm
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, hct2_cells⟩ :=
    exists_unpack64_of_length_128 hct2_len
  refine sepWPp_rw_pre_eq (by
    rw [← hct2_eq, hekVec,
      hct2_cells (s0.sp - 272#64),
      memRegion_128_cells (sf2.readReg64 .x0)]) ?_
  sep_elim_exists
  have hsp_cells_back :
      ((s0.sp - 272#64) ↦₆₄ w0) ∗ ((s0.sp - 272#64 + 8#64) ↦₆₄ w1) ∗
        ((s0.sp - 272#64 + 16#64) ↦₆₄ w2) ∗ ((s0.sp - 272#64 + 24#64) ↦₆₄ w3) ∗
        ((s0.sp - 272#64 + 32#64) ↦₆₄ w4) ∗ ((s0.sp - 272#64 + 40#64) ↦₆₄ w5) ∗
        ((s0.sp - 272#64 + 48#64) ↦₆₄ w6) ∗ ((s0.sp - 272#64 + 56#64) ↦₆₄ w7) ∗
        ((s0.sp - 272#64 + 64#64) ↦₆₄ w8) ∗ ((s0.sp - 272#64 + 72#64) ↦₆₄ w9) ∗
        ((s0.sp - 272#64 + 80#64) ↦₆₄ w10) ∗ ((s0.sp - 272#64 + 88#64) ↦₆₄ w11) ∗
        ((s0.sp - 272#64 + 96#64) ↦₆₄ w12) ∗ ((s0.sp - 272#64 + 104#64) ↦₆₄ w13) ∗
        ((s0.sp - 272#64 + 112#64) ↦₆₄ w14) ∗ ((s0.sp - 272#64 + 120#64) ↦₆₄ w15) ⊢
        memRegion (s0.sp - 272#64) 128 := by
    rw [← hct2_cells (s0.sp - 272#64)]
    exact hct2_len ▸ pointsToBytes_entails_memRegion (s0.sp - 272#64) x.ct2
  have hstack_back :
      memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
        stackAt (s0.sp - 336#64) extHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
  by_cases hflip : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = false
  · refine sepWPp_rw_pre_eq (by
      unfold sendCt2EsAfterWorkAt
      simp only [hflip, Bool.false_eq_true, ↓reduceIte] at hesVec ⊢
      rw [hesVec]) ?_
    refine sepWPp_pure_left_focus (esWorkPtr = esPtr) (by sep_focus) fun hwork_eq => ?_
    subst hwork_eq
    refine of_sepWP_lscl hcl2 (mid := (blkPl_347).base + 656#64) ?_
    wp_steps_sync_pool ((blkPl_347).base + 656#64)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_end0 => ?_
    refine sepWPp_intro_state fun s_end hs_end => ?_
    have hcl_s_end : LibsignalCodeLoaded lsmpl s_end.mem := by rw [hs_end]; exact hcl_end0
    rw [← hs_end]
    refine SepWPp.fold (Entails.of_eq (hct2_cells (sf2.readReg64 .x0)).symm) (by sep_focus) ?_
    refine SepWPp.fold hsp_cells_back (by sep_focus) ?_
    refine SepWPp.fold hstack_back (by sep_focus) ?_
    have hevs_f :
        rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es = rustAllocEvents 128 1 := by
      simp only [sendCt2FlipDeallocEvents, hflip, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    refine sepWPp_rw_pre_eq (by rw [hevs_f]; sep_ac_rfl)
      (hcont s_end (sf2.readReg64 .x0) hcl_s_end hne2
        (by rw [hs_end]; wp_norm_goal) (by rw [hs_end]; wp_norm_goal)
        (by simp only [hs_end, State.sp, wp_norm, arm64_norm, *])
        (by simp only [hs_end, wp_norm, arm64_norm, *])
        (by simp only [hs_end, wp_norm, arm64_norm, hvregs_2, hvregs_s, hvregs_1, hvregs])
        (by simp only [hs_end, Reg.x19, wp_norm, arm64_norm, *])
        (by simp only [hs_end, Reg.x20, wp_norm, arm64_norm, *])
        (by simp only [hs_end, Reg.x23, wp_norm, arm64_norm, *])
        (by simp only [hs_end, Reg.x24, wp_norm, arm64_norm, *])
        (by simp only [hs_end, Reg.x25, wp_norm, arm64_norm, *])
        (by simp only [hs_end, Reg.x26, wp_norm, arm64_norm, *])
        (by simp only [hs_end, Reg.x27, Reg.x0, wp_norm, arm64_norm, *])
        (by simp only [hs_end, Reg.x29, wp_norm, arm64_norm, *]))
  · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
      Bool.eq_true_of_not_eq_false hflip
    refine sepWPp_rw_pre_eq (by
      unfold sendCt2EsAfterWorkAt
      simp only [hflip_t, ↓reduceIte, RustCliAllocBudget.repAlloc_live]; rfl) ?_
    refine sepWPp_pure_left_focus (esWorkPtr ≠ 0#64) (by sep_focus) fun hwork_ne => ?_
    have hwork_beq : (esWorkPtr == 0#64) = false := beq_false_of_ne hwork_ne
    refine of_sepWP_lscl hcl2 (mid := lsρ spqrRustDeallocSym) ?_
    wp_steps_sync_pool (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_dl0 => ?_
    refine sepWPp_intro_state fun s_dl hs_dl => ?_
    have hcl_s_dl : LibsignalCodeLoaded lsmpl s_dl.mem := by rw [hs_dl]; exact hcl_dl0
    rw [← hs_dl]
    refine SepWPp.fold (Entails.of_eq (hct2_cells (sf2.readReg64 .x0)).symm) (by sep_focus) ?_
    refine SepWPp.fold hsp_cells_back (by sep_focus) ?_
    have hwork_mr : (esWorkPtr ↦ₛ esVec.toList) ⊢ memRegion esWorkPtr 2080 := by
      simpa only [esVec.toList_length] using pointsToBytes_entails_memRegion esWorkPtr esVec.toList
    refine SepWPp.fold hwork_mr (by sep_focus) ?_
    refine call_rustDealloc_cs_lscl_wpp hcl_s_dl hdealloc esWorkPtr 2080 1
      (M.stepEvents (rustAllocEvents 128 1) stCost)
      (memRegion (s0.sp - 16720#64) 12288 ∗
        (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        ((sf2.readReg64 .x0) ↦ₛ x.ct2) ∗ A.live (sf2.readReg64 .x0) 128 1 ∗
        memRegion (s0.sp - 272#64) 128 ∗ F_frame)
      (s0 := s0) (ret_pc := (blkPl_347).base + 656#64) (sp_call := s0.sp - 336#64)
      (by rw [hs_dl]; wp_norm_goal)
      (by simp only [hs_dl, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, State.sp, wp_norm, arm64_norm, *]) hfsp_align
      (by simp only [hs_dl, Reg.lr, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, Reg.x0, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, Reg.x1, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, Reg.x2, wp_norm, arm64_norm, *])
      (by sep_ac_rfl)
      (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 hcl3 => ?_)
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3,
      hx27_3, hx28_3, hfp_3, hvregs_3⟩
    simp only [hs_dl, wp_norm, arm64_norm] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    simp only [hs_dl, wp_norm, arm64_norm] at hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
    refine SepWPp.fold hstack_back (by sep_focus) ?_
    have hevs_t :
        M.stepEvents (rustDeallocEvents 2080 1) (M.stepEvents (rustAllocEvents 128 1) stCost) =
          M.stepEvents (rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es) stCost := by
      rw [← M.stepEvents_append]
      simp only [sendCt2FlipDeallocEvents, hflip_t, ↓reduceIte]
    refine sepWPp_rw_pre_eq (by rw [hevs_t]; sep_ac_rfl)
      (hcont sf3 (sf2.readReg64 .x0) hcl3 hne2
        hpc3 hrun3 hsp3 htr3
        (by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_s, hvregs_1, hvregs])
        (by simp only [Reg.x19, wp_norm, arm64_norm, *])
        (by simp only [Reg.x20, wp_norm, arm64_norm, *])
        (by simp only [Reg.x23, wp_norm, arm64_norm, *])
        (by simp only [Reg.x24, wp_norm, arm64_norm, *])
        (by simp only [Reg.x25, wp_norm, arm64_norm, *])
        (by simp only [Reg.x26, wp_norm, arm64_norm, *])
        (by simp only [Reg.x27, Reg.x0, wp_norm, arm64_norm, *])
        (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

/-- Specialization of `send_ct2_628_to_690_cl_placed_wpp` at
    `stCost := M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0` under
    `FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x)`. -/
theorem send_ct2_628_to_690_cl_placed_preEnv_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (esPtr ekPtr esWorkPtr : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hpc : st.pc = (blkPl_347).base + 552#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx21 : st.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64))
    (hx22 : st.readReg64 .x22 = esWorkPtr)
    (hx27 : st.readReg64 .x27 = 1152#64)
    (hx28 : st.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)))
    (hcont : ∀ (st' : State) (ptr_ct2 : BitVec 64),
      LibsignalCodeLoaded lsmpl st'.mem →
      ptr_ct2 ≠ 0#64 →
      st'.pc = (blkPl_347).base + 656#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = ekPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine send_ct2_628_to_690_cl_placed_wpp henc hshim halloc hdealloc x
    (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0)
    esPtr ekPtr esWorkPtr esVec ekVec s0 st F_frame hcl
    (fitsEvents_alloc128_of_seg23 (fitsEvents_seg23_of_preEnv hPre))
    hesVec hekVec hct2_eq hekPtr_ne hpc hrun hsp hsp_s0 htr hvregs
    hx19 hx20 hx21 hx22 hx27 hx28 ?_
  intro st' ptr_ct2 hcl'
  have hseg23 :
      M.stepEvents (rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es)
        (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) =
      M.stepEvents (sendCt2Seg23Events x.st.es) st0 := by
    rw [← M.stepEvents_append]
    unfold sendCt2Seg23Events
    rw [List.append_assoc]
  rw [hseg23]
  exact hcont st' ptr_ct2 hcl'

/-! ## 4. Segment 4 (`+656 → +676` + Slow Path `+1036..+1060`): `ct1.reserve(128)` -/

private theorem ule_127_add_le {cap : BitVec 64} {len : Nat}
    (hle : len ≤ cap.toNat) (hlen : len < 2 ^ 32)
    (h : (cap - BitVec.ofNat 64 len).ule 127#64 = true) :
    cap.toNat ≤ len + 127 := by
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le] at h
  · rw [hlen_bv] at h
    change cap.toNat - len ≤ 127 at h
    omega
  · rw [BitVec.le_def, hlen_bv]
    exact hle

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded `ct1.reserve(128)` (`+656 → +676`) calling
    Block `320` under `withLsCodeLoaded lsmpl (doReserveSpec M A lim)` and preserving
    `LibsignalCodeLoaded lsmpl`. -/
theorem send_ct2_reserve_ct1_cl_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hFit : ∀ cap : BitVec 64, x.st.ct1.length ≤ cap.toNat → cap.toNat ≤ x.st.ct1.length + 127 →
      FitsEvents M lim stCost (sendCt2Reserve128Events cap x.st.ct1.length))
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_347).base + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64) (evsRes : List AllocEvent),
      LibsignalCodeLoaded lsmpl st'.mem →
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (blkPl_347).base + 676#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          A.pool lim (M.stepEvents evsRes stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim stCost st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm
  refine sepWPp_fold_eq
    (A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (vecU8At_expose_sp_304_cells_heap A.repAlloc s0.sp cap_ct1 ptr_ct1 x.st.ct1)
    (by sep_ac_rfl) ?_
  refine sepWPp_pure_left_eq
    (φ := x.st.ct1.length ≤ cap_ct1.toNat ∧ cap_ct1.toNat < 2 ^ 63 ∧ ptr_ct1 ≠ 0#64)
    (((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
      vecU8HeapAt A.repAlloc cap_ct1 ptr_ct1 x.st.ct1 ∗
      A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by sep_ac_rfl) ?_
  rintro ⟨hct1_le, hct1_lt, hptr_ct1_ne⟩
  by_cases hls : ¬ (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true
  · have hls_f : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = false :=
      Bool.eq_false_iff.mpr hls
    have hge128 : x.st.ct1.length + 128 ≤ cap_ct1.toNat :=
      le_of_not_ule_sub_len hct1_le hct1_lt hls
    have hcap_ct1_ne : cap_ct1 ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
    refine sepWPp_fold_eq
      (((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (vecU8HeapAt_expose_of_ne_zero A.repAlloc cap_ct1 ptr_ct1 x.st.ct1 hcap_ct1_ne)
      (by sep_ac_rfl) ?_
    refine sepWPp_pure_left_eq
      (φ := x.st.ct1.length ≤ cap_ct1.toNat ∧ cap_ct1.toNat < 2 ^ 63 ∧ ptr_ct1 ≠ 0#64)
      ((ptr_ct1 ↦ₛ x.st.ct1) ∗
        memRegion (ptr_ct1 + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1.toNat - x.st.ct1.length) ∗
        A.live ptr_ct1 cap_ct1.toNat 1 ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (by simp only [RustCliAllocBudget.repAlloc_live]; sep_ac_rfl) ?_
    intro _
    refine of_sepWP_lscl hcl (mid := (blkPl_347).base + 676#64) ?_
    wp_steps_sync_pool ((blkPl_347).base + 676#64)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl' => ?_
    refine sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hcont _ cap_ct1 ptr_ct1 [] hcl'
        (SendCt2Reserve128Env.nil x.st.ct1.length)
        hcap_ct1_ne hge128 hct1_lt hptr_ct1_ne
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hls_t : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true :=
      Classical.not_not.mp hls
    have hbound := reserveCap_bound_of_ule_sub_len hct1_le hct1_lt32 hls_t
    have hhi := ule_127_add_le hct1_le hct1_lt32 hls_t
    have hFitSlow := fitsEnv_doReserve128_of_fitsEvents
      (v := s0.sp - 304#64) (ptr := ptr_ct1) (hFit cap_ct1 hct1_le hhi)
    refine of_sepWP_lscl hcl (mid := lsmpl.base 320) ?_
    wp_steps_sync_pool (lsmpl.base 320)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_call0 => ?_
    refine sepWPp_intro_state fun s_call hs_call => ?_
    have hcl_s_call : LibsignalCodeLoaded lsmpl s_call.mem := by rw [hs_call]; exact hcl_call0
    rw [← hs_call]
    refine sepWPp_fold_eq
      (A.pool lim stCost s_call ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (fold_vecU8At_sp_304 A.repAlloc s0.sp cap_ct1 ptr_ct1 x.st.ct1)
      (by sep_ac_rfl) ?_
    have hstack_res :
        stackAt (s0.sp - 336#64) extHookStack ⊢
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack :=
      Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp)
    refine sepWPp_fold_eq
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim stCost s_call ∗ F_frame)
      hstack_res (by sep_ac_rfl) ?_
    have hsp_call : s_call.sp = s0.sp - 336#64 := by
      simp only [hs_call, State.sp, wp_norm, arm64_norm, *]
    refine sepWPp_call_withLscl_noPanic hcl_s_call h_res
      (⟨s0.sp - 304#64, cap_ct1, ptr_ct1, x.st.ct1, 128⟩, stCost)
      (memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
      (by rw [hs_call]; wp_norm_goal)
      (by simp only [hs_call, wp_norm, arm64_norm, *])
      (by rw [State.spAligned, hsp_call]; exact hfsp_align)
      (ret_pc := (blkPl_347).base + 1056#64)
      (by simp only [hs_call, Reg.lr, wp_norm, arm64_norm, *])
      ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hcl_sf1 => ?_)
    · intro R' hm
      dsimp only [doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack]
      rw [hsp_call, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, hbound, hFitSlow⟩, ?_⟩
      · simp only [hs_call, Reg.x0, wp_norm, arm64_norm, *]
      · simp only [hs_call, Reg.x1, wp_norm, arm64_norm, BitVec.toNat_ofNat, *]
        omega
      · simp only [hs_call, Reg.x2, wp_norm, arm64_norm, BitVec.toNat_ofNat, *]
      · simp only [hs_call, Reg.x3, wp_norm, arm64_norm, *]
      · simp only [hs_call, Reg.x4, wp_norm, arm64_norm, *]
      · dsimp only [doReserveStack] at hm
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
    · dsimp only [doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack]
      rw [hsp_call, doReserveEvents_128_eq]
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
        hx27_1, hx28_1, hfp_1, hvregs_1⟩
      simp only [hs_call, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      simp only [hs_call, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
      refine sepWPp_pure_left_eq (φ := sf1.trace = s_call.trace)
        ((∃∗ ptr_ct1' : BitVec 64,
            vecU8At A.repAlloc (s0.sp - 304#64)
              (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128))
              ptr_ct1' x.st.ct1) ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by dsimp only [doReserveStack]; sep_ac_rfl) ?_
      intro htr1
      have htr1' : sf1.trace = s0.trace := by
        simpa only [hs_call, wp_norm, arm64_norm, htr] using htr1
      refine sepWPp_exists_left_eq
        (A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by sep_ac_rfl) fun ptr_ct1' => ?_
      have hcap_ct1'_ne : BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128) ≠ 0#64 :=
        reserveCap_ne_zero_len hbound
      refine sepWPp_fold_eq
        (A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (vecU8At_expose_sp_304_of_ne_zero A.repAlloc s0.sp
          (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128))
          ptr_ct1' x.st.ct1 hcap_ct1'_ne)
        (by sep_ac_rfl) ?_
      refine sepWPp_pure_left_eq
        (φ := x.st.ct1.length ≤ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat ∧
          (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat < 2 ^ 63 ∧ ptr_ct1' ≠ 0#64)
        (((s0.sp - 304#64) ↦₆₄ BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)
            ((BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by simp only [RustCliAllocBudget.repAlloc_live]; sep_ac_rfl) ?_
      rintro ⟨_, hmax_ct1', hptr_ct1'_ne⟩
      have hge128' :
          x.st.ct1.length + 128 ≤
            (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat :=
        reserveCap_ge_add_128 hbound
      have hsp1' : sf1.sp = s0.sp - 336#64 := hsp1.trans hsp_call
      have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1'
      simp only [wp_norm, arm64_norm] at hsp1_norm
      refine of_sepWP_lscl hcl_sf1 (mid := (blkPl_347).base + 676#64) ?_
      wp_steps_sync_pool ((blkPl_347).base + 676#64)
      simp only [State.setMem_setMem]
      refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_sf2_0 => ?_
      refine sepWPp_intro_state fun sf2 hsf2 => ?_
      have hcl_sf2 : LibsignalCodeLoaded lsmpl sf2.mem := by rw [hsf2]; exact hcl_sf2_0
      rw [← hsf2]
      have hstack_back :
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack ⊢
            stackAt (s0.sp - 336#64) extHookStack :=
        Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp).symm
      refine sepWPp_fold_eq
        (((s0.sp - 304#64) ↦₆₄ BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)
            ((BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf2 ∗
          F_frame)
        hstack_back (by sep_ac_rfl) ?_
      refine sepWPp_rw_pre_eq (by sep_ac_rfl)
        (hcont sf2 (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ptr_ct1'
          (sendCt2Reserve128Events cap_ct1 x.st.ct1.length)
          hcl_sf2
          (SendCt2Reserve128Env.slow hct1_le hhi)
          hcap_ct1'_ne hge128' hmax_ct1' hptr_ct1'_ne
          (by rw [hsf2]; wp_norm_goal) (by rw [hsf2]; wp_norm_goal)
          (by simp only [hsf2, State.sp, wp_norm, arm64_norm, *])
          (by simp only [hsf2, wp_norm, arm64_norm, *])
          (by simp only [hsf2, wp_norm, arm64_norm, hvregs_1, hvregs])
          (by simp only [hsf2, Reg.x1, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x19, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x20, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x23, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x24, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x25, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x26, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x27, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x29, wp_norm, arm64_norm, *]))

/-- Specialization of `send_ct2_reserve_ct1_cl_placed_wpp` at
    `stCost := M.stepEvents (sendCt2Seg23Events x.st.es) st0` under
    `FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x)`. -/
theorem send_ct2_reserve_ct1_cl_placed_preEnv_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_347).base + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64) (evsRes : List AllocEvent),
      LibsignalCodeLoaded lsmpl st'.mem →
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (blkPl_347).base + 676#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine send_ct2_reserve_ct1_cl_placed_wpp h_res x (M.stepEvents (sendCt2Seg23Events x.st.es) st0)
    cap_ct1 ptr_ct1 s0 st F_frame hcl
    (fun _ hle hhi => fitsEvents_reserve128_of_preEnv hPre hle hhi)
    hct1_lt32 hpc hrun hsp hsp_s0 htr hvregs ?_
  intro st' cap_ct1' ptr_ct1' evsRes hcl' hRes
  rw [← M.stepEvents_append]
  exact hcont st' cap_ct1' ptr_ct1' evsRes hcl' hRes

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudgetAux
