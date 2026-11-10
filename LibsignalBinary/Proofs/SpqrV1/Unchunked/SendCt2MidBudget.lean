/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Mid
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
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
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Middle Segments

Re-exports `SendCt2StepsBudget`, `SendCt2MidBudgetAux`, and `SendCt2MidPlacedBudget`, and
proves fixed-base `RustCliAllocBudget`-threaded Segment 5a (`+676 → +836`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator libcruxHmacName spqrAuthApi
)
open CryptoVerification.SpqrV1.Auth (
  pointsTo64_rev64_eq_toBEBytes toBEBytes_8_length
)
open CryptoVerification.SpqrV1.ChainProofs (
  SliceConcat3Ghost bytesAt_false bytesAt_true sliceConcatName
)
open CryptoVerification.SpqrV1.States.Leaves (
  UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name
  unchunkedCt1SentEkReceivedSendCt2_fnOff
)
open CryptoVerification.SpqrV1.Unchunked (
  adrp_ctLabel_sendCt2 adrp_ctLabel_sendCt2' bytes_rem_entails_memRegion_cap
  ctLabel_length exists_unpack64_of_length_128 fold_sp_144_24 fold_sp_272_24_24
  macCtUnchecked_eq_hmacWith memRegion_128_cells memRegion_ct1_split_128_len
  memRegion_sp_272_split_48_80 pointsToBytes_append_ct1_ct2 stackAt_extHook_eq_allocHook
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec libcruxHmacSha256Events)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  SliceConcat3Env sliceConcat3Events sliceConcat3Spec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  SendCt2Reserve128Env UnchunkedSendCt2PreEnv dealloc_ok_at_sendCt2
  fitsEnv_sliceConcat3_of_concatHmac fitsEvents_concatHmac_of_preEnv
  libcruxHmacSafeBudgetSpec sendCt2ConcatHmacEvents sendCt2Seg23Events
  sepWPp_call_noPanic sepWPp_exists_left_eq sepWPp_intro_state
  sepWPp_pure_left_eq sepWPp_rw_pre_eq sliceConcat3_ok_at_sendCt2
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (
  call_rustDealloc_cs_wpp call_rustDealloc_cs_wppBase expose_concat3_md_sp_144 fitsEvents_hmac_of_concatHmac
  hmac_safe_budget_ok_at_sendCt2 sendCt2Seg5aEvents sepWPp_pure_left_focus
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget (
  Ct1SentEkReceived
  sendCt2FlipAllocEvents
  sendCt2FlipDeallocEvents
  sendCt2Seg23Events
  sendCt2Reserve128Events
  SendCt2Reserve128Env
  sendCt2ConcatHmacEvents
  UnchunkedSendCt2PreEnv
  UnchunkedSendCt2PostEnv
  UnchunkedSendCt2Env
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpec
  UnchunkedCt1SentEkReceivedSendCt2PlacedOk
  sendCt2PlacedPostQOfPostEnv
  sendCt2PlacedPostQOfEnv
  sendCt2PlacedPostQ
  sendCt2PlacedPostQp
  unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv
  unchunkedCt1SentEkReceivedSendCt2SpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2Spec
  sendCt2PostQOfPostEnv
  sendCt2PostQOfEnv
  sendCt2PostQ
  sendCt2PostQp
  libcruxHmacSafeBudgetSpec
  subroutine_ok_libcruxHmacSafe_of_budget
  libcrux_hmac_safe_placed_ok
  mlkem_encaps2_vm_placed_ok
  mlkem_encaps2_vm_ok_at_ext
  libcrux_hmac_safe_budget_ok_at_ext
  shim_ok_at_sendCt2
  alloc_ok_at_sendCt2
  allocNoOom_ok_at_sendCt2
  dealloc_ok_at_sendCt2
  memcpy_ok_at_sendCt2
  doReserve7_ok_at_sendCt2
  sliceConcat3_ok_at_sendCt2
  swap_loop_placed_ok
  swap_loop_placed_pool_ok
  scan_loop_false_placed_ok
  scan_loop_false_placed_pool_ok
  scan_loop_true_placed_ok
  scan_loop_true_placed_pool_ok
  send_ct2_prologue_to_scan_placed
  send_ct2_prologue_to_scan_placed_pool
  send_ct2_prologue_to_scan_vm
  send_ct2_prologue_to_scan_pool
  send_ct2_5d8_to_604_placed_wpp
  send_ct2_5d8_to_604_wpp
  send_ct2_scan_to_628_placed_wpp
  send_ct2_scan_to_628_placed_preEnv_wpp
  send_ct2_reserve_ct1_placed_wpp
  send_ct2_reserve_ct1_placed_preEnv_wpp
  send_ct2_reserve_ct1_wpp
  send_ct2_reserve_ct1_preEnv_wpp
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (
  sepWPp_pure_left_focus
  sendCt2MdDeallocEvents
  sendCt2Seg5aEvents
  freeOnlyEvs_rustDeallocEvents
  freeOnlyEvs_sendCt2MdDeallocEvents
  freeOnlyEvs_sendCt2FlipDeallocEvents
  fitsEvents_hmac_of_concatHmac
  encaps2_vm_ok_at_sendCt2
  hmac_safe_budget_ok_at_sendCt2
  call_mlkemEncaps2_vm_wpp
  call_rustAllocNoOom_cs_wpp
  call_rustDealloc_cs_wpp
  expose_concat3_md_sp_144
  send_ct2_628_to_690_placed_wpp
  send_ct2_628_to_690_placed_preEnv_wpp
  send_ct2_628_to_690_wpp
  send_ct2_628_to_690_preEnv_wpp
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidPlacedBudget (
  send_ct2_append_hmac_placed_wpp
  send_ct2_append_hmac_placed_preEnv_wpp
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
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

local macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

/-! ## Fixed-Base Segment 5a (`+676 → +836`) -/

set_option maxHeartbeats 1600000 in
/-- Fixed-base budget-threaded Segment 5a (`+676 → +836`) on `tripleRatchetProgAtExt b ext`
    under `AllocContracts4K b A lim ext`. -/
theorem send_ct2_append_hmac_wpp {b : BitVec 64} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName) (sliceConcat3Spec M A lim))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim))
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ)
    (mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hb : b &&& 4095#64 = 0#64)
    (hFit : FitsEvents M lim stCost (sendCt2ConcatHmacEvents x.st.ct1.length))
    (hct2_len : x.ct2.length = 128)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 : (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 676#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State),
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 836#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = ptr_ct1' →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = mkPtr →
      st'.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
          A.pool lim (M.stepEvents (sendCt2Seg5aEvents x.st.ct1.length) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        (ptr_ct1' ↦ₛ x.st.ct1) ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
        A.pool lim stCost st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  have h_concat3 := sliceConcat3_ok_at_sendCt2 hconcat3
  have h_hmac := hmac_safe_budget_ok_at_sendCt2 b hhmac
  have h_dealloc := dealloc_ok_at_sendCt2 hA
  have hfnOff_bv :
      bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
        BitVec.ofNat 64
          (libsignalSessionCode.fnOff
            "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") := by
    change _ = BitVec.ofNat 64 (libsignalSessionCode.fnOff unchunkedCt1SentEkReceivedSendCt2Name)
    rw [unchunkedCt1SentEkReceivedSendCt2_fnOff]
  have hadrp_ct := adrp_ctLabel_sendCt2 hb
  have hadrp_ct' := adrp_ctLabel_sendCt2' hb
  rw [hfnOff_bv] at hadrp_ct hadrp_ct'
  clear hfnOff_bv
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx1 hx25 hx26 hx27 hx29
  have hmd_len_eq :
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length =
        35 + 8 + (x.st.ct1.length + 128) := by
    simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len]
  have hmd_lt63 : 35 + 8 + (x.st.ct1.length + 128) < 2 ^ 63 := by omega
  have hct1_full_len :
      BitVec.ofNat 64 x.st.ct1.length + 128#64 = BitVec.ofNat 64 (x.st.ct1 ++ x.ct2).length := by
    rw [List.length_append, hct2_len]; bv_omega
  clear hA hconcat3 hhmac hb
  send_ct2_fetches_range b trapHooks 676 160
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at *
  simp +singlePass only [Program.fnAddr_rebase,
    SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc hadrp_ct hadrp_ct'
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, subroutine_ok, SepWPp]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc hadrp_ct hadrp_ct'
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok, SepWPp]
  examples_hide_fetches
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hct2_cells⟩ :=
    exists_unpack64_of_length_128 hct2_len
  refine sepWPp_rw_pre_eq (by
    rw [memRegion_ct1_split_128_len ptr_ct1' hge128 hmax_ct1',
      memRegion_128_cells (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length),
      hct2_cells ptr_ct2,
      memRegion_sp_272_split_48_80 s0.sp]) ?_
  sep_elim_exists
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  try simp only [hadrp_ct, hadrp_ct']
  refine sepWPp_intro_state fun s_cc hs_cc => ?_
  rw [← hs_cc]
  refine SepWPp.fold (Entails.of_eq (hct2_cells ptr_ct2).symm) (by sep_focus) ?_
  refine SepWPp.fold
    (Entails.of_eq (hct2_cells (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)).symm)
    (by sep_focus) ?_
  refine SepWPp.fold
    (pointsToBytes_append_ct1_ct2 ptr_ct1' x.st.ct1 x.ct2)
    (by sep_focus) ?_
  refine SepWPp.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 120#64) x.st.epoch))
    (by sep_focus) ?_
  have hsp_cc : s_cc.sp = s0.sp - 336#64 := by
    simp only [hs_cc, State.sp, wp_norm, arm64_norm, *]
  let ctLabelAddr : BitVec 64 := b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")
  let g_cc : SliceConcat3Ghost :=
    ⟨s0.sp - 144#64, s0.sp - 272#64,
      true, ctLabelAddr, Authenticator.ctLabel,
      false, s0.sp - 120#64, toBEBytes 8 x.st.epoch,
      false, ptr_ct1', x.st.ct1 ++ x.ct2⟩
  have hg_sum :
      g_cc.bs0.length + g_cc.bs1.length + g_cc.bs2.length =
        35 + 8 + (x.st.ct1.length + 128) := by
    dsimp only [g_cc]
    simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len]
  have hFit_cc : FitsEnv M lim stCost (SliceConcat3Env g_cc) :=
    fitsEnv_sliceConcat3_of_concatHmac hg_sum (by omega) hFit
  have hs8 : (s0.sp - 272#64) + 8#64 = s0.sp - 264#64 := by bv_omega
  have hs16 : (s0.sp - 272#64) + 16#64 = s0.sp - 256#64 := by bv_omega
  have hs24 : (s0.sp - 272#64) + 24#64 = s0.sp - 248#64 := by bv_omega
  have hs32 : (s0.sp - 272#64) + 32#64 = s0.sp - 240#64 := by bv_omega
  have hs40 : (s0.sp - 272#64) + 40#64 = s0.sp - 232#64 := by bv_omega
  refine sepWPp_call_noPanic h_concat3 (g_cc, stCost)
    (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
      ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
      ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
      ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
      memRegion (ptr_ct1' + BitVec.ofNat 64 (x.st.ct1.length + 128))
        (cap_ct1'.toNat - (x.st.ct1.length + 128)) ∗
      A.live ptr_ct1' cap_ct1'.toNat 1 ∗
      (ptr_ct2 ↦ₛ x.ct2) ∗
      (mkPtr ↦ₛ x.st.auth.macKey) ∗
      memRegion (s0.sp - 224#64) 80 ∗
      F_frame)
    (by rw [hs_cc]; wp_norm_goal)
    (by simp only [hs_cc, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_cc]; exact hfsp_align)
    rfl
    ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_cc hpc_cc hrun_cc hsp_cc_rel hcs_cc => ?_)
  · intro R' hm
    dsimp only [sliceConcat3Spec, g_cc, ctLabelAddr]
    rw [hsp_cc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, ?_, ?_, ?_, hFit_cc⟩, ?_⟩
    · simp only [hs_cc, Reg.x0, wp_norm, arm64_norm, *]
    · simp only [hs_cc, Reg.x1, wp_norm, arm64_norm, *]
    · simp only [hs_cc, Reg.x2, wp_norm, arm64_norm, *]
    · simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len]; omega
    · simp only [bytesAt_true, bytesAt_false, ctLabel_length, toBEBytes_8_length,
        BitVec.ofNat_eq_ofNat, hs8, hs16, hs24, hs32, hs40, hadrp_ct, hadrp_ct'] at hm ⊢
      try rw [hct1_full_len] at hm
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
  · simp only [hs_cc, Reg.lr, wp_norm, arm64_norm] at hpc_cc
    dsimp only [sliceConcat3Spec, g_cc, ctLabelAddr]
    rw [hsp_cc]
    simp only [bytesAt_true, bytesAt_false, hs8, hs16, hs24, hs32, hs40]
    rcases hcs_cc with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c,
      hx27_c, hx28_c, hfp_c, hvregs_c⟩
    simp only [hs_cc, wp_norm, arm64_norm] at hx19_c hx20_c hx21_c hx22_c hx23_c hx24_c
    simp only [hs_cc, wp_norm, arm64_norm] at hx25_c hx26_c hx27_c hx28_c hfp_c hvregs_c
    try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro evs_cc
    apply SepWPp.exists_elim; intro ptr_md
    refine sepWPp_pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr_cc_raw, _, hEnv_cc⟩
    have hevs_cc : evs_cc = rustAllocEvents (35 + 8 + (x.st.ct1.length + 128)) 1 := by
      dsimp only [SliceConcat3Env, sliceConcat3Events,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events] at hEnv_cc
      simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len] at hEnv_cc
      have hne0 : 35 + 8 + (x.st.ct1.length + 128) ≠ 0 := by omega
      simpa only [hne0, ↓reduceIte] using hEnv_cc
    subst hevs_cc
    have htr_cc : sf_cc.trace = s0.trace := by
      simpa only [hs_cc, wp_norm, arm64_norm, htr] using htr_cc_raw
    have hsp_sf_cc : sf_cc.sp = s0.sp - 336#64 := hsp_cc_rel.trans hsp_cc
    have hsp_sf_cc_norm : sf_cc.readReg64 .sp = s0.sp - 336#64 := hsp_sf_cc
    simp only [wp_norm, arm64_norm] at hsp_sf_cc_norm
    refine SepWPp.fold
      (expose_concat3_md_sp_144 (A := A.repAlloc) s0.sp ptr_md x.st.epoch x.st.ct1 x.ct2
        hct2_len hmd_lt63)
      (by sep_focus) ?_
    refine sepWPp_pure_left_focus (ptr_md ≠ 0#64) (by sep_focus) fun hptr_md_ne => ?_
    simp only [RustCliAllocBudget.repAlloc_live]
    have hcap_md_toNat :
        (BitVec.ofNat 64 (35 + 8 + (x.st.ct1.length + 128))).toNat =
          35 + 8 + (x.st.ct1.length + 128) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hcap_md_ne : BitVec.ofNat 64 (35 + 8 + (x.st.ct1.length + 128)) ≠ 0#64 := by
      intro h0
      have h0' := congrArg BitVec.toNat h0
      rw [hcap_md_toNat] at h0'
      change 35 + 8 + (x.st.ct1.length + 128) = 0 at h0'
      omega
    have hcap_md_beq : (BitVec.ofNat 64 (35 + 8 + (x.st.ct1.length + 128)) == 0#64) = false :=
      beq_false_of_ne hcap_md_ne
    simp only [ctLabel_length, toBEBytes_8_length, BitVec.ofNat_eq_ofNat]
    refine SepWPp.fold
      (fold_sp_272_24_24 s0.sp
        (b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) 35#64
        (s0.sp - 120#64) 8#64 ptr_ct1'
        (BitVec.ofNat 64 (x.st.ct1 ++ x.ct2).length))
      (by sep_focus) ?_
    have hfold_ct1 :
        (ptr_ct1' ↦ₛ (x.st.ct1 ++ x.ct2)) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 (x.st.ct1.length + 128))
            (cap_ct1'.toNat - (x.st.ct1.length + 128)) ⊢
          memRegion ptr_ct1' cap_ct1'.toNat := by
      rw [← show (x.st.ct1 ++ x.ct2).length = x.st.ct1.length + 128 by
        rw [List.length_append, hct2_len]]
      exact bytes_rem_entails_memRegion_cap ptr_ct1' cap_ct1' (x.st.ct1 ++ x.ct2)
        (by rw [List.length_append, hct2_len]; omega) hmax_ct1'
    refine SepWPp.fold hfold_ct1 (by sep_focus) ?_
    wp_steps_rebase_pool
      (fnBase + bv% (ls_off% "libcrux_hmac::hmac" -
        ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
    refine sepWPp_intro_state fun s_hm hs_hm => ?_
    rw [← hs_hm]
    have hsp_hm : s_hm.sp = s0.sp - 336#64 := by
      simp only [hs_hm, State.sp, wp_norm, arm64_norm, *]
    have hmk_toNat : (BitVec.ofNat 64 x.st.auth.macKey.length).toNat = x.st.auth.macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hFit_hm := fitsEvents_hmac_of_concatHmac hFit
    refine sepWPp_call_noPanic h_hmac
      (⟨s0.sp - 272#64, mkPtr, x.st.auth.macKey,
        ptr_md, Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)⟩,
        M.stepEvents (rustAllocEvents (35 + 8 + (x.st.ct1.length + 128)) 1) stCost)
      (((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 (35 + 8 + (x.st.ct1.length + 128))) ∗
        ((s0.sp - 136#64) ↦₆₄ ptr_md) ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (35 + 8 + (x.st.ct1.length + 128))) ∗
        A.live ptr_md (35 + 8 + (x.st.ct1.length + 128)) 1 ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗ F_frame)
      (by rw [hs_hm]; wp_norm_goal)
      (by simp only [hs_hm, wp_norm, arm64_norm, *])
      (by rw [State.spAligned, hsp_hm]; exact hfsp_align)
      rfl
      ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (fun sf_hm hpc_hm hrun_hm hsp_hm_rel hcs_hm => ?_)
    · intro R' hm
      dsimp only [libcruxHmacSafeBudgetSpec]
      rw [hsp_hm, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmk_lt32, hdata_lt32, hFit_hm⟩, ?_⟩
      · simp only [hs_hm, Reg.x8, wp_norm, arm64_norm, *]
      · simp only [hs_hm, Reg.x0, wp_norm, arm64_norm, *]
      · simp only [hs_hm, Reg.x1, wp_norm, arm64_norm, *]
      · simp only [hs_hm, Reg.x2, wp_norm, arm64_norm, hmk_toNat, *]
      · simp only [hs_hm, Reg.x3, wp_norm, arm64_norm, *]
      · simp only [hs_hm, Reg.x4, wp_norm, arm64_norm, hcap_md_toNat, List.length_append,
          ctLabel_length, toBEBytes_8_length, hct2_len, *]
        omega
      · simp only [hs_hm, Reg.x5, wp_norm, arm64_norm, *]
      · simp only [hs_hm, Reg.x6, wp_norm, arm64_norm, *]
      · exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
    · simp only [hs_hm, Reg.lr, wp_norm, arm64_norm] at hpc_hm
      dsimp only [libcruxHmacSafeBudgetSpec]
      rw [hsp_hm]
      rcases hcs_hm with ⟨hx19_h, hx20_h, hx21_h, hx22_h, hx23_h, hx24_h, hx25_h, hx26_h,
        hx27_h, hx28_h, hfp_h, hvregs_h⟩
      simp only [hs_hm, wp_norm, arm64_norm] at hx19_h hx20_h hx21_h hx22_h hx23_h hx24_h
      simp only [hs_hm, wp_norm, arm64_norm] at hx25_h hx26_h hx27_h hx28_h hfp_h hvregs_h
      refine sepWPp_pure_left_focus (sf_hm.trace = s_hm.trace) (by sep_focus) fun htr_hm_raw => ?_
      have htr_hm : sf_hm.trace = s0.trace := by
        simpa only [hs_hm, wp_norm, arm64_norm, htr_cc] using htr_hm_raw
      have hsp_sf_hm : sf_hm.sp = s0.sp - 336#64 := hsp_hm_rel.trans hsp_hm
      have hsp_sf_hm_norm : sf_hm.readReg64 .sp = s0.sp - 336#64 := hsp_sf_hm
      simp only [wp_norm, arm64_norm] at hsp_sf_hm_norm
      have hmac_vec :
          hmacWith F x.st.auth.macKey
            (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)) = x.mac := by
        try rw [← macCtUnchecked_eq_hmacWith F x.st.auth x.st.epoch (x.st.ct1 ++ x.ct2)]
        try rw [List.append_assoc Authenticator.ctLabel,
          ← macCtUnchecked_eq_hmacWith F x.st.auth x.st.epoch (x.st.ct1 ++ x.ct2)]
        exact hmac_eq.symm
      have hpool_hm :
          M.stepEvents libcruxHmacSha256Events
            (M.stepEvents (rustAllocEvents (35 + 8 + (x.st.ct1.length + 128)) 1) stCost) =
          M.stepEvents (sendCt2ConcatHmacEvents x.st.ct1.length) stCost := by
        rw [← M.stepEvents_append]; rfl
      rw [hmac_vec, hpool_hm]
      have hmd_mr :
          (ptr_md ↦ₛ (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2))) ⊢
            memRegion ptr_md (35 + 8 + (x.st.ct1.length + 128)) := by
        simpa only [hmd_len_eq] using
          pointsToBytes_entails_memRegion ptr_md
            (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2))
      refine SepWPp.fold hmd_mr (by sep_focus) ?_
      wp_steps_rebase_pool
        (fnBase + bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      refine sepWPp_intro_state fun s_dl hs_dl => ?_
      rw [← hs_dl]
      refine SepWPp.fold
        (fold_sp_144_24 s0.sp
          (BitVec.ofNat 64 (35 + 8 + (x.st.ct1.length + 128))) ptr_md
          (BitVec.ofNat 64 (35 + 8 + (x.st.ct1.length + 128))))
        (by sep_focus) ?_
      have hstack_alloc :
          stackAt (s0.sp - 336#64) extHookStack ⊢
            memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
        Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
      refine SepWPp.fold hstack_alloc (by sep_focus) ?_
      refine call_rustDealloc_cs_wppBase h_dealloc ptr_md
        (35 + 8 + (x.st.ct1.length + 128)) 1
        (M.stepEvents (sendCt2ConcatHmacEvents x.st.ct1.length) stCost)
        (memRegion (s0.sp - 16720#64) 12288 ∗
          ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗ F_frame)
        (s0 := s0) (ret_pc := fnBase + 836#64) (sp_call := s0.sp - 336#64)
        (by rw [hs_dl]; wp_norm_goal)
        (by simp only [hs_dl, wp_norm, arm64_norm, *])
        (by simp only [hs_dl, State.sp, wp_norm, arm64_norm, *]) hfsp_align
        (by simp only [hs_dl, Reg.lr, wp_norm, arm64_norm, *])
        (by simp only [hs_dl, wp_norm, arm64_norm, *])
        (by simp only [hs_dl, Reg.x0, wp_norm, arm64_norm, *])
        (by simp only [hs_dl, Reg.x1, wp_norm, arm64_norm, hcap_md_toNat, *])
        (by simp only [hs_dl, Reg.x2, wp_norm, arm64_norm, *])
        (by sep_ac_rfl)
        (fun sf2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_)
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2,
        hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [hs_dl, wp_norm, arm64_norm] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
      simp only [hs_dl, wp_norm, arm64_norm] at hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      have hstack_back :
          memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
            stackAt (s0.sp - 336#64) extHookStack :=
        Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
      refine SepWPp.fold hstack_back (by sep_focus) ?_
      have hpool_seg5a :
          M.stepEvents (rustDeallocEvents (35 + 8 + (x.st.ct1.length + 128)) 1)
            (M.stepEvents (sendCt2ConcatHmacEvents x.st.ct1.length) stCost) =
          M.stepEvents (sendCt2Seg5aEvents x.st.ct1.length) stCost := by
        rw [← M.stepEvents_append]; rfl
      refine sepWPp_rw_pre_eq (by rw [hpool_seg5a]; sep_ac_rfl)
        (hcont sf2 hpc2 hrun2 hsp2 htr2
          (by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_h, hvregs_c, hvregs])
          (by simp only [Reg.x19, wp_norm, arm64_norm, *])
          (by simp only [Reg.x20, wp_norm, arm64_norm, *])
          (by simp only [Reg.x22, wp_norm, arm64_norm, *])
          (by simp only [Reg.x23, wp_norm, arm64_norm, *])
          (by simp only [Reg.x24, wp_norm, arm64_norm, *])
          (by simp only [Reg.x25, wp_norm, arm64_norm, *])
          (by simp only [Reg.x26, wp_norm, arm64_norm, *])
          (by simp only [Reg.x27, wp_norm, arm64_norm, *])
          (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

theorem send_ct2_append_hmac_preEnv_wpp {b : BitVec 64} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName) (sliceConcat3Spec M A lim))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsRes : List AllocEvent)
    (mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hb : b &&& 4095#64 = 0#64)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes)
    (hct2_len : x.ct2.length = 128)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 : (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 676#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State),
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 836#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = ptr_ct1' →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = mkPtr →
      st'.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
          A.pool lim
            (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) st0)
            st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        (ptr_ct1' ↦ₛ x.st.ct1) ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
        A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine send_ct2_append_hmac_wpp hA hconcat3 hhmac x
    (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0)
    mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st F_frame
    hb (fitsEvents_concatHmac_of_preEnv hPre hRes)
    hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
    hpc hrun hsp hsp_s0 htr hvregs hx1 hx25 hx26 hx27 hx29 ?_
  intro st'
  rw [← M.stepEvents_append]
  exact hcont st'

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudget
