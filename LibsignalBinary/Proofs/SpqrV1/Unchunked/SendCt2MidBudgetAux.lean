/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Mid
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275 -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Call Wrappers and Segment 3

Defines Segment 5a deallocation events, framed `SepWPp` call combinators, and proves
`[LibsignalPlacement]` and fixed-base `RustCliAllocBudget`-threaded Segment 3 (`+552 → +656`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_347 blkPl_347 libsignalSessionCode lsρ
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionShimSpec tripleRatchetProgAtExt
)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator Bytes Epoch MlKem flipEndiannessOfEncapsulationStateBytes issue1275NeedsFlip
  libcruxHmacName mlkemEncaps2Name mlkemEncaps2Spec spqrAuthApi
)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Auth (toBEBytes_8_length vecU8At_expose_entails)
open CryptoVerification.SpqrV1.States.Leaves (
  UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name
)
open CryptoVerification.SpqrV1.Unchunked (
  ctLabel_length exists_unpack64_of_length_128 memRegion_128_cells
  sendCt2EsAfterWorkAt sendCt2EsWorkAt sendCt2EsWorkAt_entails
  spqrMlkemEncaps2Sym spqrRustDeallocSym stackAt_extHook_eq_allocHook
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliAllocNoOomSpecBase rustCliDeallocBudgetSpec
  rustCliDeallocBudgetSpecBase rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (
  libcruxHmacBudgetSpec libcruxHmacSha256Events withVmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  UnchunkedSendCt2PreEnv allocNoOom_ok_at_sendCt2 dealloc_ok_at_sendCt2
  fitsEvents_alloc128_of_seg23 fitsEvents_seg23_of_preEnv
  libcruxHmacSafeBudgetSpec libcrux_hmac_safe_budget_ok_at_ext mlkem_encaps2_vm_ok_at_ext
  sendCt2ConcatHmacEvents sendCt2FlipAllocEvents sendCt2FlipDeallocEvents sendCt2Seg23Events
  sepWPp_call_noPanic sepWPp_fold_eq sepWPp_intro_state sepWPp_pure_left_eq
  sepWPp_rw_pre_eq shim_ok_at_sendCt2
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

theorem sepWPp_pure_left_focus {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P P_rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = ⌜φ⌝ ∗ P_rest) (h : φ → SepWPp prog ret s P_rest Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hP]
  exact SepWPp.pure_elim h

/-! ## Segment 5a Deallocation Events and Fixed-Base Callee Helpers -/

/-- Deallocation event for the temporary `35 + 8 + (ct1Len + 128)`-byte MAC input buffer
    in Segment 5a. -/
def sendCt2MdDeallocEvents (ct1Len : Nat) : List AllocEvent :=
  rustDeallocEvents (35 + 8 + (ct1Len + 128)) 1

/-- Full allocator event list of Segment 5a (`slice_concat_3`, `libcrux_hmac::hmac`, and
    temporary MAC buffer deallocation). -/
def sendCt2Seg5aEvents (ct1Len : Nat) : List AllocEvent :=
  sendCt2ConcatHmacEvents ct1Len ++ sendCt2MdDeallocEvents ct1Len

theorem freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

theorem freeOnlyEvs_sendCt2MdDeallocEvents (ct1Len : Nat) :
    FreeOnlyEvs (sendCt2MdDeallocEvents ct1Len) :=
  freeOnlyEvs_rustDeallocEvents _ _

theorem freeOnlyEvs_sendCt2FlipDeallocEvents (es : Bytes) :
    FreeOnlyEvs (sendCt2FlipDeallocEvents es) := by
  unfold sendCt2FlipDeallocEvents
  by_cases h : issue1275NeedsFlip ((es.drop 1536).take 512) = true
  · simp only [h, ↓reduceIte]
    exact freeOnlyEvs_rustDeallocEvents 2080 1
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact FreeOnlyEvs.nil

theorem fitsEvents_hmac_of_concatHmac {M : AllocCostModel} {lim : BudgetLimits}
    {stCost : M.σ} {ct1Len : Nat}
    (hFit : FitsEvents M lim stCost (sendCt2ConcatHmacEvents ct1Len)) :
    FitsEvents M lim
      (M.stepEvents (rustAllocEvents (35 + 8 + (ct1Len + 128)) 1) stCost)
      libcruxHmacSha256Events := by
  unfold sendCt2ConcatHmacEvents at hFit
  rw [fitsEvents_append] at hFit
  exact hFit.2

theorem encaps2_vm_ok_at_sendCt2 (b : BitVec 64) {K : MlKem}
    {ext : String → Option (State → State)}
    (hencaps2 : HookSat ext mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "libcrux_ml_kem::mlkem768::incremental::encapsulate2" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (withVmPreserved (mlkemEncaps2Spec K)) :=
  mlkem_encaps2_vm_ok_at_ext b K ext hencaps2
    unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "libcrux_ml_kem::mlkem768::incremental::encapsulate2" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))

theorem hmac_safe_budget_ok_at_sendCt2 (b : BitVec 64) {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "libcrux_hmac::hmac" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (libcruxHmacSafeBudgetSpec F M A lim) :=
  libcrux_hmac_safe_budget_ok_at_ext b F A lim ext hhmac
    unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "libcrux_hmac::hmac" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))

/-! ## Framed `SepWPp` Call Rules -/

/-- Framed `SepWPp` call rule for `withVmPreserved (mlkemEncaps2Spec K)`, syncing
    `A.pool lim stCost` across the call via `A.pool_of_vmPreserved`. -/
theorem call_mlkemEncaps2_vm_wpp {K : MlKem} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (withVmPreserved (mlkemEncaps2Spec K)))
    (ret esA ekA : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (stCost : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
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
      SepWPp prog target_pc sf
        (((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
          (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack ∗
          A.pool lim stCost sf) ∗ Frame) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall ⟨ret, esA, esVec, ekA, ekVec⟩
    (A.pool lim stCost s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
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
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) htr_sf hcs_sf)

theorem call_rustAllocNoOom_cs_wppBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (rustCliAllocNoOomSpecBase M A lim false))
    (size align : Nat) (stCost : M.σ)
    (hlay : RustLayoutOk size align)
    (hFit : FitsEvents M lim stCost (rustAllocEvents size align))
    {s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool lim stCost s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → AllocCallPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → (sf.readReg64 .x0).toNat % align = 0 →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall (size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliAllocNoOomSpecBase]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hFit⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustCliAllocNoOomSpecBase]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp]
    refine sepWPp_pure_left_eq
      ((A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack ∗
        A.live (sf.readReg64 .x0) size align ∗
        memRegion (sf.readReg64 .x0) size) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, hmod, hne⟩
    exact sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hacp hne hmod)

theorem call_rustAllocNoOom_cs_wpp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (rustCliAllocNoOomSpec M A lim false))
    (size align : Nat) (stCost : M.σ)
    (hlay : RustLayoutOk size align)
    (hFit : FitsEvents M lim stCost (rustAllocEvents size align))
    {s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool lim stCost s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → AllocCallPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → (sf.readReg64 .x0).toNat % align = 0 →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall (size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliAllocNoOomSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hFit, hlr.symm ▸ hlr_ls⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp]
    refine sepWPp_pure_left_eq
      ((A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack ∗
        A.live (sf.readReg64 .x0) size align ∗
        memRegion (sf.readReg64 .x0) size) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, hmod, hne⟩
    exact sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hacp hne hmod)

theorem call_rustDealloc_cs_wppBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (rustCliDeallocBudgetSpecBase M A lim))
    (ptr : BitVec 64) (size align : Nat) (stCost : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
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
      SepWPp prog target_pc sf
        ((A.pool lim (M.stepEvents (rustDeallocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall (ptr, size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliDeallocBudgetSpecBase]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩,
      Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm⟩
  · dsimp only [rustCliDeallocBudgetSpecBase]
    rw [hsp]
    refine sepWPp_pure_left_eq
      (φ := AllocCallPreserved s sf ∧
        M.liveBytes (M.stepEvents (rustDeallocEvents size align) stCost) ≤ M.liveBytes stCost)
      ((A.pool lim (M.stepEvents (rustDeallocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, _⟩
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hacp.2.1.trans htrace) hcs_sf

theorem call_rustDealloc_cs_wpp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (rustCliDeallocBudgetSpec M A lim))
    (ptr : BitVec 64) (size align : Nat) (stCost : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
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
      SepWPp prog target_pc sf
        ((A.pool lim (M.stepEvents (rustDeallocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall (ptr, size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliDeallocBudgetSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlr.symm ▸ hlr_ls⟩,
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
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hacp.2.1.trans htrace) hcs_sf

/-- Unpack the exact-capacity `vecU8At` produced by `sliceConcat3Spec` at `sp - 144#64`. -/
theorem expose_concat3_md_sp_144 {A : RustAlloc} (sp ptr : BitVec 64)
    (ep : Epoch) (ct1 ct2 : Bytes)
    (hct2_len : ct2.length = 128)
    (hlen : 35 + 8 + (ct1.length + 128) < 2 ^ 63) :
    vecU8At A (sp - 144#64)
      (BitVec.ofNat 64
        (Authenticator.ctLabel.length + (toBEBytes 8 ep).length + (ct1 ++ ct2).length))
      ptr (Authenticator.ctLabel ++ toBEBytes 8 ep ++ (ct1 ++ ct2)) ⊢
      ⌜ptr ≠ 0#64⌝ ∗
        ((sp - 144#64) ↦₆₄ BitVec.ofNat 64 (35 + 8 + (ct1.length + 128))) ∗
        ((sp - 136#64) ↦₆₄ ptr) ∗
        ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 (35 + 8 + (ct1.length + 128))) ∗
        (ptr ↦ₛ (Authenticator.ctLabel ++ toBEBytes 8 ep ++ (ct1 ++ ct2))) ∗
        A.live ptr (35 + 8 + (ct1.length + 128)) 1 := by
  have h35 : Authenticator.ctLabel.length = 35 := ctLabel_length
  have h8 : (toBEBytes 8 ep).length = 8 := toBEBytes_8_length ep
  have hct12 : (ct1 ++ ct2).length = ct1.length + 128 := by rw [List.length_append, hct2_len]
  have hsum1 :
      Authenticator.ctLabel.length + (toBEBytes 8 ep).length + (ct1 ++ ct2).length =
        35 + 8 + (ct1.length + 128) := by omega
  have hsum2 :
      (Authenticator.ctLabel ++ toBEBytes 8 ep ++ (ct1 ++ ct2)).length =
        35 + 8 + (ct1.length + 128) := by
    simp only [List.length_append, h35, h8, hct2_len]
  have hcap_toNat :
      (BitVec.ofNat 64 (35 + 8 + (ct1.length + 128))).toNat = 35 + 8 + (ct1.length + 128) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 (35 + 8 + (ct1.length + 128)) ≠ 0 := by
    intro h0
    have h0' := congrArg BitVec.toNat h0
    rw [hcap_toNat] at h0'
    change 35 + 8 + (ct1.length + 128) = 0 at h0'
    omega
  have ha8 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have ha16 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  rw [hsum1]
  refine Entails.trans (vecU8At_expose_entails A (sp - 144#64)
    (BitVec.ofNat 64 (35 + 8 + (ct1.length + 128))) ptr
    (Authenticator.ctLabel ++ toBEBytes 8 ep ++ (ct1 ++ ct2))) ?_
  simp only [hsum2, hcap_ne, ↓reduceIte, hcap_toNat, Nat.sub_self, memRegion_zero,
    sepConj_emp, ha8, ha16]
  rw [show (((sp - 144#64) ↦₆₄ BitVec.ofNat 64 (35 + 8 + (ct1.length + 128))) ∗
      ((sp - 136#64) ↦₆₄ ptr) ∗
      ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 (35 + 8 + (ct1.length + 128))) ∗
      ⌜35 + 8 + (ct1.length + 128) ≤ 35 + 8 + (ct1.length + 128) ∧
        35 + 8 + (ct1.length + 128) < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (ptr ↦ₛ (Authenticator.ctLabel ++ toBEBytes 8 ep ++ (ct1 ++ ct2))) ∗
      A.live ptr (35 + 8 + (ct1.length + 128)) 1) =
    (⌜35 + 8 + (ct1.length + 128) ≤ 35 + 8 + (ct1.length + 128) ∧
        35 + 8 + (ct1.length + 128) < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((sp - 144#64) ↦₆₄ BitVec.ofNat 64 (35 + 8 + (ct1.length + 128))) ∗
      ((sp - 136#64) ↦₆₄ ptr) ∗
      ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 (35 + 8 + (ct1.length + 128))) ∗
      (ptr ↦ₛ (Authenticator.ctLabel ++ toBEBytes 8 ep ++ (ct1 ++ ct2))) ∗
      A.live ptr (35 + 8 + (ct1.length + 128)) 1) by sep_ac_rfl]
  refine Entails.pure_left fun ⟨_, _, hptr_ne⟩ => ?_
  exact Entails.pure_right hptr_ne (Entails.of_eq rfl)

/-! ## Segment 3 (`+552 → +656`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded Segment 3 (`+552 → +656`):
    calls `encapsulate2`, allocates and copies the 128-byte `ct2` buffer without OOM under
    `FitsEvents M lim stCost (rustAllocEvents 128 1)`, and conditionally frees `esWorkPtr`. -/
theorem send_ct2_628_to_690_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
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
  wp_steps_sync_pool (lsρ spqrMlkemEncaps2Sym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_enc hs_enc => ?_
  rw [← hs_enc]
  refine call_mlkemEncaps2_vm_wpp henc (s0.sp - 272#64) esWorkPtr ekPtr esVec ekVec stCost
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
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
    hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [hs_enc, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [hs_enc, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
  simp only [wp_norm, arm64_norm] at hsp1_norm
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_shim hs_shim => ?_
  rw [← hs_shim]
  have hsp_shim : s_shim.sp = s0.sp - 336#64 := by
    simp only [hs_shim, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_noPanic hshim ()
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
    (fun sf_shim hpc_shim hrun_shim hsp_shim_rel hcs_shim => ?_)
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
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_alloc hs_alloc => ?_
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
  refine call_rustAllocNoOom_cs_wpp hallocNoOom 128 1 stCost hlay_128 hFit128
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
    (fun sf2 hpc2 hrun2 hsp2 hcs2 hacp2 hne2 _ => ?_)
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
    wp_steps_sync_pool ((blkPl_347).base + 656#64)
    simp only [State.setMem_setMem]
    refine sepWPp_intro_state fun s_end hs_end => ?_
    rw [← hs_end]
    refine SepWPp.fold (Entails.of_eq (hct2_cells (sf2.readReg64 .x0)).symm) (by sep_focus) ?_
    refine SepWPp.fold hsp_cells_back (by sep_focus) ?_
    refine SepWPp.fold hstack_back (by sep_focus) ?_
    have hevs_f :
        rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es = rustAllocEvents 128 1 := by
      simp only [sendCt2FlipDeallocEvents, hflip, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    refine sepWPp_rw_pre_eq (by rw [hevs_f]; sep_ac_rfl)
      (hcont s_end (sf2.readReg64 .x0) hne2
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
    wp_steps_sync_pool (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    refine sepWPp_intro_state fun s_dl hs_dl => ?_
    rw [← hs_dl]
    refine SepWPp.fold (Entails.of_eq (hct2_cells (sf2.readReg64 .x0)).symm) (by sep_focus) ?_
    refine SepWPp.fold hsp_cells_back (by sep_focus) ?_
    have hwork_mr : (esWorkPtr ↦ₛ esVec.toList) ⊢ memRegion esWorkPtr 2080 := by
      simpa only [esVec.toList_length] using pointsToBytes_entails_memRegion esWorkPtr esVec.toList
    refine SepWPp.fold hwork_mr (by sep_focus) ?_
    refine call_rustDealloc_cs_wpp hdealloc esWorkPtr 2080 1
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
      (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 => ?_)
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
      (hcont sf3 (sf2.readReg64 .x0) hne2
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

theorem send_ct2_628_to_690_placed_preEnv_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
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
  refine send_ct2_628_to_690_placed_wpp henc hshim halloc hdealloc x
    (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0)
    esPtr ekPtr esWorkPtr esVec ekVec s0 st F_frame
    (fitsEvents_alloc128_of_seg23 (fitsEvents_seg23_of_preEnv hPre))
    hesVec hekVec hct2_eq hekPtr_ne hpc hrun hsp hsp_s0 htr hvregs
    hx19 hx20 hx21 hx22 hx27 hx28 ?_
  intro st' ptr_ct2
  have hseg23 :
      M.stepEvents (rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es)
        (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) =
      M.stepEvents (sendCt2Seg23Events x.st.es) st0 := by
    rw [← M.stepEvents_append]
    unfold sendCt2Seg23Events
    rw [List.append_assoc]
  rw [hseg23]
  exact hcont st' ptr_ct2

set_option maxHeartbeats 1200000 in
/-- Fixed-base budget-threaded Segment 3 (`+552 → +656`) on `tripleRatchetProgAtExt b ext`
    under `AllocContracts4K b A lim ext`. -/
theorem send_ct2_628_to_690_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (hencaps2 : HookSat ext mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K)))
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ)
    (esPtr ekPtr esWorkPtr : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hFit128 : FitsEvents M lim stCost (rustAllocEvents 128 1))
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 552#64)
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
      ptr_ct2 ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 656#64 →
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
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        A.pool lim stCost st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  have henc := encaps2_vm_ok_at_sendCt2 b hencaps2
  have hshim := shim_ok_at_sendCt2 hA
  have hallocNoOom := allocNoOom_ok_at_sendCt2 hA
  have hdealloc := dealloc_ok_at_sendCt2 hA
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hek_beq : (ekPtr == 0#64) = false := beq_false_of_ne hekPtr_ne
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx27 hx28
  clear hA hencaps2
  send_ct2_fetches_range b trapHooks 552 104
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at *
  simp +singlePass only [Program.fnAddr_rebase,
    SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, subroutine_ok, SepWPp]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine sepWPp_fold_eq
    ((ekPtr ↦ₛ x.st.ek) ∗ memRegion (s0.sp - 272#64) 128 ∗
      A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (sendCt2EsWorkAt_entails A.repAlloc esPtr esWorkPtr x.st.es hesVec)
    (by sep_ac_rfl) ?_
  refine sepWPp_rw_pre_eq (by rw [← hekVec]) ?_
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "libcrux_ml_kem::mlkem768::incremental::encapsulate2" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_enc hs_enc => ?_
  rw [← hs_enc]
  refine call_mlkemEncaps2_vm_wpp henc (s0.sp - 272#64) esWorkPtr ekPtr esVec ekVec stCost
    (sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame)
    (s0 := s0) (ret_pc := fnBase + 580#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_enc]; wp_norm_goal)
    (by simp only [hs_enc, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_enc, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, Reg.x8, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_enc, Reg.x1, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
    hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [hs_enc, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [hs_enc, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
  simp only [wp_norm, arm64_norm] at hsp1_norm
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_shim hs_shim => ?_
  rw [← hs_shim]
  have hsp_shim : s_shim.sp = s0.sp - 336#64 := by
    simp only [hs_shim, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_noPanic hshim ()
    (((esWorkPtr ↦ₛ esVec.toList) ∗ (ekPtr ↦ₛ ekVec.toList) ∗
      ((s0.sp - 272#64) ↦ₛ (K.encaps2 esVec ekVec).toList) ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ A.pool lim stCost s_shim) ∗
      (sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame))
    (by rw [hs_shim]; wp_norm_goal)
    (by simp only [hs_shim, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_shim]; exact hfsp_align)
    rfl
    (fun R' hm => by
      dsimp only [withVmPreserved, sessionShimSpec]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by simp only [emp_sepConj]; sep_ac_rfl)) hm)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_shim hpc_shim hrun_shim hsp_shim_rel hcs_shim => ?_)
  simp only [hs_shim, Reg.lr, wp_norm, arm64_norm] at hpc_shim
  dsimp only [withVmPreserved, sessionShimSpec]
  refine sepWPp_pure_left_eq (φ := VmPreserved s_shim sf_shim)
    (⌜sf_shim.trace = s_shim.trace⌝ ∗
      ((esWorkPtr ↦ₛ esVec.toList) ∗ (ekPtr ↦ₛ ekVec.toList) ∗
        ((s0.sp - 272#64) ↦ₛ (K.encaps2 esVec ekVec).toList) ∗
        stackAt (s0.sp - 336#64) extHookStack ∗ A.pool lim stCost s_shim) ∗
      (sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame))
    (by sep_ac_rfl) ?_
  intro hvm_shim
  refine sepWPp_pure_left_eq (φ := sf_shim.trace = s_shim.trace)
    (((esWorkPtr ↦ₛ esVec.toList) ∗ (ekPtr ↦ₛ ekVec.toList) ∗
      ((s0.sp - 272#64) ↦ₛ (K.encaps2 esVec ekVec).toList) ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ A.pool lim stCost s_shim) ∗
      (sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame))
    (by sep_ac_rfl) ?_
  intro htr_shim_raw
  rw [← A.pool_of_vmPreserved hvm_shim]
  rcases hcs_shim with ⟨hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s,
    hx27_s, hx28_s, hfp_s, hvregs_s⟩
  simp only [hs_shim, wp_norm, arm64_norm] at hx19_s hx20_s hx21_s hx22_s hx23_s hx24_s
  simp only [hs_shim, wp_norm, arm64_norm] at hx25_s hx26_s hx27_s hx28_s hfp_s hvregs_s
  have htr_shim : sf_shim.trace = s0.trace := by
    simpa only [hs_shim, wp_norm, arm64_norm, htr1] using htr_shim_raw
  have hsp_sf_shim : sf_shim.sp = s0.sp - 336#64 := hsp_shim_rel.trans hsp_shim
  have hsp_sf_shim_norm : sf_shim.readReg64 .sp = s0.sp - 336#64 := hsp_sf_shim
  simp only [wp_norm, arm64_norm] at hsp_sf_shim_norm
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_alloc hs_alloc => ?_
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
  refine call_rustAllocNoOom_cs_wppBase hallocNoOom 128 1 stCost hlay_128 hFit128
    (memRegion (s0.sp - 16720#64) 12288 ∗
      (esWorkPtr ↦ₛ esVec.toList) ∗ (ekPtr ↦ₛ ekVec.toList) ∗
      ((s0.sp - 272#64) ↦ₛ (K.encaps2 esVec ekVec).toList) ∗
      sendCt2EsAfterWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗ F_frame)
    (ret_pc := fnBase + 596#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_alloc]; wp_norm_goal)
    (by simp only [hs_alloc, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_alloc, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x1, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 hacp2 hne2 _ => ?_)
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
    wp_steps_rebase_pool (fnBase + 656#64)
    refine sepWPp_intro_state fun s_end hs_end => ?_
    rw [← hs_end]
    refine SepWPp.fold (Entails.of_eq (hct2_cells (sf2.readReg64 .x0)).symm) (by sep_focus) ?_
    refine SepWPp.fold hsp_cells_back (by sep_focus) ?_
    refine SepWPp.fold hstack_back (by sep_focus) ?_
    have hevs_f :
        rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es = rustAllocEvents 128 1 := by
      simp only [sendCt2FlipDeallocEvents, hflip, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    refine sepWPp_rw_pre_eq (by rw [hevs_f]; sep_ac_rfl)
      (hcont s_end (sf2.readReg64 .x0) hne2
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
    wp_steps_rebase_pool
      (fnBase + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
    refine sepWPp_intro_state fun s_dl hs_dl => ?_
    rw [← hs_dl]
    refine SepWPp.fold (Entails.of_eq (hct2_cells (sf2.readReg64 .x0)).symm) (by sep_focus) ?_
    refine SepWPp.fold hsp_cells_back (by sep_focus) ?_
    have hwork_mr : (esWorkPtr ↦ₛ esVec.toList) ⊢ memRegion esWorkPtr 2080 := by
      simpa only [esVec.toList_length] using pointsToBytes_entails_memRegion esWorkPtr esVec.toList
    refine SepWPp.fold hwork_mr (by sep_focus) ?_
    refine call_rustDealloc_cs_wppBase hdealloc esWorkPtr 2080 1
      (M.stepEvents (rustAllocEvents 128 1) stCost)
      (memRegion (s0.sp - 16720#64) 12288 ∗
        (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        ((sf2.readReg64 .x0) ↦ₛ x.ct2) ∗ A.live (sf2.readReg64 .x0) 128 1 ∗
        memRegion (s0.sp - 272#64) 128 ∗ F_frame)
      (s0 := s0) (ret_pc := fnBase + 656#64) (sp_call := s0.sp - 336#64)
      (by rw [hs_dl]; wp_norm_goal)
      (by simp only [hs_dl, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, State.sp, wp_norm, arm64_norm, *]) hfsp_align
      (by simp only [hs_dl, Reg.lr, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, Reg.x0, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, Reg.x1, wp_norm, arm64_norm, *])
      (by simp only [hs_dl, Reg.x2, wp_norm, arm64_norm, *])
      (by sep_ac_rfl)
      (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 => ?_)
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
      (hcont sf3 (sf2.readReg64 .x0) hne2
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

theorem send_ct2_628_to_690_preEnv_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (hencaps2 : HookSat ext mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K)))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (esPtr ekPtr esWorkPtr : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 552#64)
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
      ptr_ct2 ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 656#64 →
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
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine send_ct2_628_to_690_wpp hA hencaps2 x
    (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0)
    esPtr ekPtr esWorkPtr esVec ekVec s0 st F_frame
    (fitsEvents_alloc128_of_seg23 (fitsEvents_seg23_of_preEnv hPre))
    hesVec hekVec hct2_eq hekPtr_ne hpc hrun hsp hsp_s0 htr hvregs
    hx19 hx20 hx21 hx22 hx27 hx28 ?_
  intro st' ptr_ct2
  have hseg23 :
      M.stepEvents (rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents x.st.es)
        (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) =
      M.stepEvents (sendCt2Seg23Events x.st.es) st0 := by
    rw [← M.stepEvents_append]
    unfold sendCt2Seg23Events
    rw [List.append_assoc]
  rw [hseg23]
  exact hcont st' ptr_ct2

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux
