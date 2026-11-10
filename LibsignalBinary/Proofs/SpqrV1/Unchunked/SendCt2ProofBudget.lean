/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Proof
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
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
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275 -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Epilogue and Top-Level Proof

Proves `RustCliAllocBudget`-threaded Segment 5b (`+836 → +964`) and top-level fixed-base
and `[LibsignalPlacement]` contracts for `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_347 blkPl_347 libsignalSessionCode
  lsLogFilterAddr lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack tripleRatchetProgAtExt
)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator MlKem libcruxHmacName mlkemEncaps2Name mlkemEncaps2Spec spqrAuthApi
)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Auth (
  authenticatorAt toBEBytes_8_length
)
open CryptoVerification.SpqrV1.ChainProofs (sliceConcatName)
open CryptoVerification.SpqrV1.Drop (unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt)
open CryptoVerification.SpqrV1.States.Leaves (
  UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name
  unchunkedSendCt2RoAt unchunkedSendCt2Stack
)
open CryptoVerification.SpqrV1.Unchunked (
  cap_ne_zero_of_add_128_le ctLabel_length encaps2_ok_elim fold_outA_104
  fold_sp_264_120 fold_stA_128 fold_stackAt_unchunkedSendCt2 macCt_ok_elim
  memRegion_104_cells sendCt2CalleeSavedAt send_ct2_ok_elim
  slice_and_tail_entails_live_memRegion slice_and_tail_entails_vecU8HeapAt
  spqrLibcruxHmacSym spqrMlkemEncaps2Sym spqrRustDeallocSym
  stackAt_extHook_eq_allocHook stackAt_unchunkedSendCt2_split
  unchunkedSendCt2PlacedRoAt vecU8HeapAt vecU8Tail vecU8_entails_cells_and_heap
  vecU8_entails_slice_and_tail vecU8_sp_272_entails
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustDeallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (sliceConcat3Spec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  SendCt2Reserve128Env UnchunkedCt1SentEkReceivedSendCt2PlacedOk
  UnchunkedSendCt2Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
  dealloc_ok_at_sendCt2 sendCt2PlacedPostQ sendCt2PlacedPostQOfEnv
  sendCt2PlacedPostQOfPostEnv sendCt2PlacedPostQp sendCt2PostQ
  sendCt2PostQOfEnv sendCt2PostQOfPostEnv sendCt2PostQp sendCt2Seg23Events
  send_ct2_prologue_to_scan_placed_pool send_ct2_prologue_to_scan_pool
  sepWPp_fold_eq sepWPp_intro_state sepWPp_pure_left_eq sepWPp_rw_pre_eq
  subroutine_ok_libcruxHmacSafe_of_budget
  unchunkedCt1SentEkReceivedSendCt2PlacedSpec
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv
  unchunkedCt1SentEkReceivedSendCt2Spec
  unchunkedCt1SentEkReceivedSendCt2SpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsReserveBudget (
  send_ct2_reserve_ct1_preEnv_wpp
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (
  call_rustDealloc_cs_wpp call_rustDealloc_cs_wppBase sendCt2Seg5aEvents send_ct2_628_to_690_preEnv_wpp
  sepWPp_pure_left_focus
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudget (
  send_ct2_append_hmac_preEnv_wpp
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget (
  send_ct2_segs_2_to_5a_placed_preEnv_wpp
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudgetAux (
  freeOnlyEvs_sendCt2Seg5bEvents sendCt2Seg5bEvents
  send_ct2_scan_to_628_preEnv_wpp send_ct2_scan_to_628_wpp
  unchunkedSendCt2PostEnv_of_seg5b
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  UnchunkedSendCt2PreEnv
  UnchunkedSendCt2PostEnv
  UnchunkedSendCt2Env
  UnchunkedCt1SentEkReceivedSendCt2PlacedOk
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpec
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv
  unchunkedCt1SentEkReceivedSendCt2SpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2Spec
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudgetAux (
  sendCt2Seg5bEvents
  freeOnlyEvs_sendCt2Seg5bEvents
  unchunkedSendCt2PostEnv_of_seg5b
  send_ct2_scan_to_628_wpp
  send_ct2_scan_to_628_preEnv_wpp
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
    repeat' (apply SepWPp.exists_elim; intro _)))

private theorem sepWPp_of_false_qp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun _ _ => False)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, hret | ⟨_, _, _, hf⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl hret⟩
  · exact False.elim hf
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## Fixed-Base Segment 5b (`+836 → +964`) and Top-Level Theorems -/

set_option maxHeartbeats 1600000 in
/-- Fixed-base (`tripleRatchetProgAtExt b ext`) budget-threaded Segment 5b (`+836 → +964`):
    stores `(Ct2Sent, ct2, mac)` into `outA`, deallocates `ct1`, `es`, and `ek`, restores
    callee-saved registers, and returns, witnessing `PostEnv` on
    `evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap`. -/
theorem send_ct2_epilogue_ret_wpp_ofPostEnv {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hA : AllocContracts4K b A lim ext)
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsPre5b : List AllocEvent)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hPost : PostEnv x (evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap))
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128)
    (hes_len : x.st.es.length = 2080)
    (hek_len : x.st.ek.length = 1152)
    (hmk_le : x.st.auth.macKey.length ≤ mkCap.toNat)
    (hmk_max : mkCap.toNat < 2 ^ 63)
    (hmk_ne : mkPtr ≠ 0#64)
    (hes_le : x.st.es.length ≤ esCap.toNat)
    (hes_max : esCap.toNat < 2 ^ 63)
    (hek_le : x.st.ek.length ≤ ekCap.toNat)
    (hek_max : ekCap.toNat < 2 ^ 63)
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hptr_ct2_ne : ptr_ct2 ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 836#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx22 : st.readReg64 .x22 = ptr_ct1')
    (hx23 : st.readReg64 .x23 = x.outA)
    (hx24 : st.readReg64 .x24 = x.stA)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (memRegion x.outA 104 ∗
        (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
        ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
        ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        memRegion (x.stA + 48#64) 80 ∗
        vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
        ((s0.sp - 328#64) ↦₆₄ esCap) ∗ (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
        ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        A.live ptr_ct2 128 1 ∗
        vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
        memRegion (s0.sp - 336#64) 8 ∗
        memRegion (s0.sp - 280#64) 8 ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        sendCt2CalleeSavedAt s0 ∗
        unchunkedSendCt2RoAt b ∗
        A.pool lim (M.stepEvents evsPre5b st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack)
      (sendCt2PostQOfPostEnv M A lim F K b PostEnv x st0 s0 R)
      sendCt2PostQp := by
  have h_dealloc := dealloc_ok_at_sendCt2 hA
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hcap_ct1'_ne : cap_ct1' ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
  have hcap_ct1'_beq : (cap_ct1' == 0#64) = false := beq_false_of_ne hcap_ct1'_ne
  have hesCap_ne : esCap ≠ 0#64 := by
    intro h0; subst h0; simp [hes_len] at hes_le
  have hesCap_beq : (esCap == 0#64) = false := beq_false_of_ne hesCap_ne
  have hekCap_ne : ekCap ≠ 0#64 := by
    intro h0; subst h0; simp [hek_len] at hek_le
  have hekCap_beq : (ekCap == 0#64) = false := beq_false_of_ne hekCap_ne
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27
  clear hA
  send_ct2_fetches_range b trapHooks 836 132
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at *
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc h_dealloc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, subroutine_ok, SepWPp]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc h_dealloc
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.fold
    (slice_and_tail_entails_vecU8HeapAt A.repAlloc mkCap mkPtr x.st.auth.macKey hmk_le hmk_max hmk_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (slice_and_tail_entails_live_memRegion A.repAlloc esCap esPtr x.st.es hes_le hes_max hesCap_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (slice_and_tail_entails_live_memRegion A.repAlloc ekCap ekPtr x.st.ek hek_le hek_max hekCap_ne)
    (by sep_focus) ?_
  refine SepWPp.fold (vecU8_sp_272_entails A.repAlloc s0.sp x.mac) (by sep_focus) ?_
  sep_elim_exists
  rename_i macCap macPtr
  refine sepWPp_rw_pre_eq (by simp only [RustCliAllocBudget.repAlloc_live]; rfl) ?_
  refine sepWPp_rw_pre_eq (by rw [memRegion_104_cells x.outA]) ?_
  sep_elim_exists
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_dl1 hs_dl1 => ?_
  rw [← hs_dl1]
  refine SepWPp.fold
    (fold_stA_128 x.stA rkCap rkPtr (BitVec.ofNat 64 x.st.auth.rootKey.length)
      mkCap mkPtr (BitVec.ofNat 64 x.st.auth.macKey.length))
    (by sep_focus) ?_
  have h_ct2_rep : A.live ptr_ct2 128 1 = A.repAlloc.live ptr_ct2 128 1 := by
    simp only [RustCliAllocBudget.repAlloc_live]
  refine sepWPp_rw_pre_eq (by rw [h_ct2_rep]) ?_
  refine SepWPp.fold
    (fold_outA_104 A.repAlloc x rkCap rkPtr mkCap mkPtr ptr_ct2 macCap macPtr
      houtUc hct2_len hptr_ct2_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (fold_sp_264_120 s0.sp macPtr (BitVec.ofNat 64 x.mac.length))
    (by sep_focus) ?_
  refine SepWPp.fold
    (Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp))
    (by sep_focus) ?_
  let F_post : SepProp :=
    memRegion (s0.sp - 16720#64) 12288 ∗
      unchunkedCt2SentAt A.repAlloc x.outA x.outUc ∗
      vecU8 A.repAlloc (x.outA + 56#64) x.ct2 ∗
      vecU8 A.repAlloc (x.outA + 80#64) x.mac ∗
      memRegion x.stA 128 ∗
      ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
      ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
      ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
      ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
      ((s0.sp - 272#64) ↦₆₄ macCap) ∗
      memRegion (s0.sp - 264#64) 120 ∗
      memRegion (s0.sp - 336#64) 8 ∗
      memRegion (s0.sp - 280#64) 8 ∗
      memRegion (s0.sp - 144#64) 24 ∗
      ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
      memRegion (s0.sp - 112#64) 16 ∗
      sendCt2CalleeSavedAt s0 ∗
      unchunkedSendCt2RoAt b
  refine call_rustDealloc_cs_wppBase h_dealloc ptr_ct1' cap_ct1'.toNat 1
    (M.stepEvents evsPre5b st0)
    (F_post ∗ ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
      A.live esPtr esCap.toNat 1 ∗ memRegion esPtr esCap.toNat ∗
      A.live ekPtr ekCap.toNat 1 ∗ memRegion ekPtr ekCap.toNat)
    (s0 := s0) (ret_pc := fnBase + 896#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_dl1]; wp_norm_goal)
    (by simp only [hs_dl1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_dl1, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, Reg.x1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, Reg.x2, wp_norm, arm64_norm, *])
    (by dsimp only [F_post]; sep_ac_rfl)
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  simp only [hs_dl1, wp_norm, arm64_norm, hx19, hx20, hvregs] at hx19_1 hx20_1 hvregs_1
  clear hs_dl1
  have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
  simp only [wp_norm, arm64_norm] at hsp1_norm
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_dl2 hs_dl2 => ?_
  rw [← hs_dl2]
  refine call_rustDealloc_cs_wppBase h_dealloc esPtr esCap.toNat 1
    (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1) (M.stepEvents evsPre5b st0))
    (F_post ∗ ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
      A.live ekPtr ekCap.toNat 1 ∗ memRegion ekPtr ekCap.toNat)
    (s0 := s0) (ret_pc := fnBase + 916#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_dl2]; wp_norm_goal)
    (by simp only [hs_dl2, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_dl2, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, Reg.x1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, Reg.x2, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_)
  rcases hcs2 with ⟨_, hx20_2, _, _, _, _, _, _, _, _, _, hvregs_2⟩
  simp only [hs_dl2, wp_norm, arm64_norm, hx20_1, hvregs_1] at hx20_2 hvregs_2
  clear hs_dl2
  have hsp2_norm : sf2.readReg64 .sp = s0.sp - 336#64 := hsp2
  simp only [wp_norm, arm64_norm] at hsp2_norm
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_dl3 hs_dl3 => ?_
  rw [← hs_dl3]
  refine call_rustDealloc_cs_wppBase h_dealloc ekPtr ekCap.toNat 1
    (M.stepEvents (rustDeallocEvents esCap.toNat 1)
      (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1) (M.stepEvents evsPre5b st0)))
    (F_post ∗ ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap))
    (s0 := s0) (ret_pc := fnBase + 936#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_dl3]; wp_norm_goal)
    (by simp only [hs_dl3, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_dl3, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, Reg.x1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, Reg.x2, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 => ?_)
  rcases hcs3 with ⟨_, _, _, _, _, _, _, _, _, _, _, hvregs_3⟩
  simp only [hs_dl3, wp_norm, arm64_norm, hvregs_2] at hvregs_3
  clear hs_dl3
  dsimp only [F_post]
  refine SepWPp.fold
    (Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm)
    (by sep_focus) ?_
  refine sepWPp_rw_pre_eq (by unfold sendCt2CalleeSavedAt; rfl) ?_
  have hsp3_norm : sf3.readReg64 .sp = s0.sp - 336#64 := hsp3
  simp only [wp_norm, arm64_norm] at hsp3_norm
  wp_steps_rebase_pool (s0.readReg64 .x30)
  refine sepWPp_intro_state fun s_ret hs_ret => ?_
  rw [← hs_ret]
  refine SepWPp.fold
    (fold_stackAt_unchunkedSendCt2 s0 esCap ekCap x.st.epoch
      cap_ct1' ptr_ct1' (BitVec.ofNat 64 x.st.ct1.length) macCap x.st.epoch)
    (by sep_focus) ?_
  have hpool_eq :
      M.stepEvents (rustDeallocEvents ekCap.toNat 1)
        (M.stepEvents (rustDeallocEvents esCap.toNat 1)
          (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1) (M.stepEvents evsPre5b st0))) =
      M.stepEvents (evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap) st0 := by
    rw [← M.stepEvents_append, ← M.stepEvents_append, ← M.stepEvents_append]
    unfold sendCt2Seg5bEvents
    simp only [List.append_assoc]
  refine SepWPp.done
    (by rw [hs_ret]; wp_norm_goal)
    (by simp only [hs_ret, wp_norm, arm64_norm, *]) ?_
  refine ⟨fun hm => ?_, by simp only [hs_ret, State.sp, wp_norm, arm64_norm, *], ?_⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [hs_ret, wp_norm, arm64_norm, *], hPost⟩, ?_⟩
    rw [hpool_eq] at hm
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hs_ret, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, Reg.x29, wp_norm, arm64_norm, *]

theorem send_ct2_epilogue_ret_wpp_ofEnv {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hA : AllocContracts4K b A lim ext)
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsPre5b : List AllocEvent)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hPost : Env x (evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap))
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128)
    (hes_len : x.st.es.length = 2080)
    (hek_len : x.st.ek.length = 1152)
    (hmk_le : x.st.auth.macKey.length ≤ mkCap.toNat)
    (hmk_max : mkCap.toNat < 2 ^ 63)
    (hmk_ne : mkPtr ≠ 0#64)
    (hes_le : x.st.es.length ≤ esCap.toNat)
    (hes_max : esCap.toNat < 2 ^ 63)
    (hek_le : x.st.ek.length ≤ ekCap.toNat)
    (hek_max : ekCap.toNat < 2 ^ 63)
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hptr_ct2_ne : ptr_ct2 ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 836#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx22 : st.readReg64 .x22 = ptr_ct1')
    (hx23 : st.readReg64 .x23 = x.outA)
    (hx24 : st.readReg64 .x24 = x.stA)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (memRegion x.outA 104 ∗
        (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
        ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
        ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        memRegion (x.stA + 48#64) 80 ∗
        vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
        ((s0.sp - 328#64) ↦₆₄ esCap) ∗ (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
        ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        A.live ptr_ct2 128 1 ∗
        vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
        memRegion (s0.sp - 336#64) 8 ∗
        memRegion (s0.sp - 280#64) 8 ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        sendCt2CalleeSavedAt s0 ∗
        unchunkedSendCt2RoAt b ∗
        A.pool lim (M.stepEvents evsPre5b st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack)
      (sendCt2PostQOfEnv M A lim F K b Env x st0 s0 R)
      sendCt2PostQp :=
  send_ct2_epilogue_ret_wpp_ofPostEnv hA x st0 evsPre5b
    rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2
    s0 st R hPost houtUc hct2_len hes_len hek_len
    hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
    hpc hrun hsp hsp_s0 htr hvregs hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27

theorem send_ct2_epilogue_ret_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsRes : List AllocEvent)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes)
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128)
    (hes_len : x.st.es.length = 2080)
    (hek_len : x.st.ek.length = 1152)
    (hmk_le : x.st.auth.macKey.length ≤ mkCap.toNat)
    (hmk_max : mkCap.toNat < 2 ^ 63)
    (hmk_ne : mkPtr ≠ 0#64)
    (hes_le : x.st.es.length ≤ esCap.toNat)
    (hes_max : esCap.toNat < 2 ^ 63)
    (hek_le : x.st.ek.length ≤ ekCap.toNat)
    (hek_max : ekCap.toNat < 2 ^ 63)
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hptr_ct2_ne : ptr_ct2 ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 836#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx22 : st.readReg64 .x22 = ptr_ct1')
    (hx23 : st.readReg64 .x23 = x.outA)
    (hx24 : st.readReg64 .x24 = x.stA)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (memRegion x.outA 104 ∗
        (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
        ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
        ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        memRegion (x.stA + 48#64) 80 ∗
        vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
        ((s0.sp - 328#64) ↦₆₄ esCap) ∗ (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
        ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        A.live ptr_ct2 128 1 ∗
        vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
        memRegion (s0.sp - 336#64) 8 ∗
        memRegion (s0.sp - 280#64) 8 ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        sendCt2CalleeSavedAt s0 ∗
        unchunkedSendCt2RoAt b ∗
        A.pool lim
          (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) st0)
          st ∗
        stackAt (s0.sp - 336#64) extHookStack)
      (sendCt2PostQ M A lim F K b x st0 s0 R)
      sendCt2PostQp :=
  send_ct2_epilogue_ret_wpp_ofPostEnv hA x st0
    (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length)
    rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2
    s0 st R (unchunkedSendCt2PostEnv_of_seg5b hRes cap_ct1' esCap ekCap)
    houtUc hct2_len hes_len hek_len
    hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
    hpc hrun hsp hsp_s0 htr hvregs hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27

set_option maxHeartbeats 1200000 in
/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded fixed-base correctness theorem for
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` on `tripleRatchetProgAtExt b ext`. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_ok_4k_ofPrePostEnv {b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → PostEnv x evs)
    (hA : AllocContracts4K b A lim ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName) (sliceConcat3Spec M A lim))
    (hencaps2 : HookSat ext mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv M A lim F K b PreEnv PostEnv) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  refine ⟨(unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv M A lim F K b PreEnv PostEnv).pre (x, st0) s0,
    R, hpre, sepWPp_of_false_qp ?_⟩
  change SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
    ((unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv M A lim F K b PreEnv PostEnv).pre (x, st0) s0)
    (sendCt2PostQOfPostEnv M A lim F K b PostEnv x st0 s0 R)
    sendCt2PostQp
  dsimp only [unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv]
  refine sepWPp_pure_left_eq
    (φ := b &&& 4095#64 = 0#64 ∧
      s0.readReg64 .x0 = x.outA ∧ s0.readReg64 .x1 = x.stA ∧
      x.st.send_ct2 K = .ok (x.outUc, x.ct2, x.mac) ∧
      FitsEnv M lim st0 (PreEnv x))
    (memRegion x.outA 104 ∗
      unchunkedCt1SentEkReceivedAt A.repAlloc x.stA x.st ∗
      unchunkedSendCt2RoAt b ∗
      A.pool lim st0 s0 ∗ stackAt s0.sp unchunkedSendCt2Stack)
    (by sep_ac_rfl) ?_
  rintro ⟨hb, hx0, hx1, hmodel, hPreRaw⟩
  have hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x) := hPreImp x st0 hPreRaw
  obtain ⟨henc_ok, hmac_ok, houtUc⟩ := send_ct2_ok_elim hmodel
  obtain ⟨hes_len, hek_len, esVec, ekVec, hesVec, hekVec, hct2_eq⟩ := encaps2_ok_elim henc_ok
  obtain ⟨hmk_lt32, hdata_lt32, hmac_eq⟩ := macCt_ok_elim hmac_ok
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hct1_lt32 : x.st.ct1.length < 2 ^ 32 := by
    simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len] at hdata_lt32
    omega
  unfold unchunkedCt1SentEkReceivedAt authenticatorAt
  refine SepWPp.fold (vecU8_entails_cells_and_heap A.repAlloc x.stA x.st.auth.rootKey) (by sep_focus) ?_
  sep_elim_exists
  rename_i rkCap rkPtr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hrk_le, hrk_max, hrk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A.repAlloc (x.stA + 24#64) x.st.auth.macKey) (by sep_focus) ?_
  sep_elim_exists
  rename_i mkCap mkPtr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A.repAlloc (x.stA + 48#64) x.st.es) (by sep_focus) ?_
  sep_elim_exists
  rename_i esCap esPtr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hes_le, hes_max, hes_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A.repAlloc (x.stA + 72#64) x.st.ek) (by sep_focus) ?_
  sep_elim_exists
  rename_i ekCap ekPtr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hek_le, hek_max, hek_ne⟩
  refine SepWPp.fold (vecU8_entails_cells_and_heap A.repAlloc (x.stA + 96#64) x.st.ct1) (by sep_focus) ?_
  sep_elim_exists
  rename_i ct1Cap ct1Ptr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hct1_le, hct1_max, hct1_ne⟩
  refine sepWPp_rw_pre_eq (by rw [stackAt_unchunkedSendCt2_split s0.sp]) ?_
  sep_elim_exists
  rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 e0 s64 l0 l1 l2 l3 l4 l5
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (SepWPp.of_sepWP
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
      (SepWP.mono
        (send_ct2_prologue_to_scan_pool A lim st0 x.outA x.stA x.st
          rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr
          l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 s0
          (memRegion x.outA 104 ∗
            vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
            (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
            (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
            (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
            unchunkedSendCt2RoAt b ∗
            stackAt (s0.sp - 336#64) extHookStack ∗
            memRegion (s0.sp - 336#64) 8 ∗
            memRegion (s0.sp - 280#64) 8 ∗
            memRegion (s0.sp - 144#64) 24 ∗
            memRegion (s0.sp - 112#64) 16)
          hes_len hek_len hpc hrun hsp hx0 hx1)
        ?_))
  rintro st1 _ hpc1 hrun1 ⟨_hvm1, rfl, hsp1, htr1, hvregs_1, hx8_1, hx9_1, hx10_1, hx11_1, hx13_1,
    hx19_1, hx20_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
  let F_base : SepProp :=
    memRegion x.outA 104 ∗
    (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
    ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
    ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
    ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
    memRegion (x.stA + 48#64) 80 ∗
    vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
    vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
    ((s0.sp - 328#64) ↦₆₄ esCap) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
    ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
    memRegion (s0.sp - 336#64) 8 ∗
    memRegion (s0.sp - 280#64) 8 ∗
    memRegion (s0.sp - 112#64) 16 ∗
    sendCt2CalleeSavedAt s0
  refine sepWPp_rw_pre_eq (by unfold unchunkedSendCt2RoAt; dsimp only [F_base]; sep_ac_rfl)
    (send_ct2_scan_to_628_preEnv_wpp hA x st0 esPtr s0 st1
      (F_base ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel))
      hb hPre hes_len hpc1 hrun1 hsp1 hsp htr1 hvregs_1
      hx8_1 hx9_1 hx10_1 hx11_1 hx13_1 hx19_1 hx28_1
      (fun st2 esWorkPtr hpc2 hrun2 hsp2 htr2 hvregs_2 hx19_2 hx20_2 hx21_2 hx22_2
        hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => ?_))
  rw [hx20_1] at hx20_2
  rw [hx23_1] at hx23_2
  rw [hx24_1] at hx24_2
  rw [hx25_1] at hx25_2
  rw [hx26_1] at hx26_2
  rw [hx27_1] at hx27_2
  rw [hx29_1] at hx29_2
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_628_to_690_preEnv_wpp hA hencaps2 x st0 esPtr ekPtr esWorkPtr esVec ekVec s0 st2
      (F_base ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel))
      hPre hesVec hekVec hct2_eq hek_ne hpc2 hrun2 hsp2 hsp htr2 hvregs_2
      hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hx28_2
      (fun st3 ptr_ct2 hptr_ct2_ne hpc3 hrun3 hsp3 htr3 hvregs_3
        hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 => ?_))
  rw [hx23_2] at hx23_3
  rw [hx24_2] at hx24_3
  rw [hx25_2] at hx25_3
  rw [hx26_2] at hx26_3
  rw [hx29_2] at hx29_3
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_reserve_ct1_preEnv_wpp hA x st0 ct1Cap ct1Ptr s0 st3
      (F_base ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗ A.live ptr_ct2 128 1 ∗
        memRegion (s0.sp - 272#64) 128 ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel))
      hPre hct1_lt32 hpc3 hrun3 hsp3 hsp htr3 hvregs_3
      (fun st4 cap_ct1' ptr_ct1' evsRes hRes hcap_ct1'_ne hge128 hmax_ct1' hptr_ct1'_ne
        hpc4 hrun4 hsp4 htr4 hvregs_4 hx1_4 hx19_4 hx20_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 => ?_))
  rw [hx19_3] at hx19_4
  rw [hx20_3] at hx20_4
  rw [hx23_3] at hx23_4
  rw [hx24_3] at hx24_4
  rw [hx25_3] at hx25_4
  rw [hx26_3] at hx26_4
  rw [hx27_3] at hx27_4
  rw [hx29_3] at hx29_4
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_append_hmac_preEnv_wpp hA hconcat3 hhmac x st0 evsRes mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st4
      (F_base ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        A.live ptr_ct2 128 1)
      hb hPre hRes hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
      hpc4 hrun4 hsp4 hsp htr4 hvregs_4 hx1_4 hx25_4 hx26_4 hx27_4 hx29_4
      (fun st5 hpc5 hrun5 hsp5 htr5 hvregs_5 hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx29_5 => ?_))
  rw [hx19_4] at hx19_5
  rw [hx20_4] at hx20_5
  rw [hx23_4] at hx23_5
  rw [hx24_4] at hx24_5
  refine sepWPp_rw_pre_eq (by unfold unchunkedSendCt2RoAt; dsimp only [F_base]; sep_ac_rfl)
    (send_ct2_epilogue_ret_wpp_ofPostEnv hA x st0
      (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length)
      rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2
      s0 st5 R
      (hPostImp x _ (unchunkedSendCt2PostEnv_of_seg5b hRes cap_ct1' esCap ekCap))
      houtUc hct2_len hes_len hek_len
      hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
      hpc5 hrun5 hsp5 hsp htr5 hvregs_5
      hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5)

theorem unchunked_ct1_sent_ek_received_send_ct2_ok_4k_ofEnv {b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → Env x evs)
    (hA : AllocContracts4K b A lim ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName) (sliceConcat3Spec M A lim))
    (hencaps2 : HookSat ext mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2SpecOfEnv M A lim F K b Env) :=
  unchunked_ct1_sent_ek_received_send_ct2_ok_4k_ofPrePostEnv
    hPreImp hPostImp hA hconcat3 hencaps2 hhmac

theorem unchunked_ct1_sent_ek_received_send_ct2_ok_4k {b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName) (sliceConcat3Spec M A lim))
    (hencaps2 : HookSat ext mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec M A lim F K b) :=
  unchunked_ct1_sent_ek_received_send_ct2_ok_4k_ofPrePostEnv
    (fun _ _ h => h) (fun _ _ h => h) hA hconcat3 hencaps2 hhmac

/-! ## Relocatable `[LibsignalPlacement]` Segment 5b and Top-Level Theorems -/

set_option maxHeartbeats 1600000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded Segment 5b (`+836 → +964`):
    stores `(Ct2Sent, ct2, mac)` into `outA`, deallocates `ct1`, `es`, and `ek`, restores
    callee-saved registers, and returns, witnessing `PostEnv` on
    `evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap`. -/
theorem send_ct2_epilogue_ret_placed_wpp_ofPostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsPre5b : List AllocEvent)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hPost : PostEnv x (evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap))
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128)
    (hes_len : x.st.es.length = 2080)
    (hek_len : x.st.ek.length = 1152)
    (hmk_le : x.st.auth.macKey.length ≤ mkCap.toNat)
    (hmk_max : mkCap.toNat < 2 ^ 63)
    (hmk_ne : mkPtr ≠ 0#64)
    (hes_le : x.st.es.length ≤ esCap.toNat)
    (hes_max : esCap.toNat < 2 ^ 63)
    (hek_le : x.st.ek.length ≤ ekCap.toNat)
    (hek_max : ekCap.toNat < 2 ^ 63)
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hptr_ct2_ne : ptr_ct2 ≠ 0#64)
    (hpc : st.pc = (blkPl_347).base + 836#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx22 : st.readReg64 .x22 = ptr_ct1')
    (hx23 : st.readReg64 .x23 = x.outA)
    (hx24 : st.readReg64 .x24 = x.stA)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (memRegion x.outA 104 ∗
        (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
        ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
        ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        memRegion (x.stA + 48#64) 80 ∗
        vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
        ((s0.sp - 328#64) ↦₆₄ esCap) ∗ (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
        ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        A.live ptr_ct2 128 1 ∗
        vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
        memRegion (s0.sp - 336#64) 8 ∗
        memRegion (s0.sp - 280#64) 8 ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        sendCt2CalleeSavedAt s0 ∗
        unchunkedSendCt2PlacedRoAt ∗
        A.pool lim (M.stepEvents evsPre5b st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack)
      (sendCt2PlacedPostQOfPostEnv M A lim F K PostEnv x st0 s0 R)
      sendCt2PlacedPostQp := by
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hcap_ct1'_ne : cap_ct1' ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
  have hcap_ct1'_beq : (cap_ct1' == 0#64) = false := beq_false_of_ne hcap_ct1'_ne
  have hesCap_ne : esCap ≠ 0#64 := by
    intro h0; subst h0; simp [hes_len] at hes_le
  have hesCap_beq : (esCap == 0#64) = false := beq_false_of_ne hesCap_ne
  have hekCap_ne : ekCap ≠ 0#64 := by
    intro h0; subst h0; simp [hek_len] at hek_le
  have hekCap_beq : (ekCap == 0#64) = false := beq_false_of_ne hekCap_ne
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27
  refine SepWPp.fold
    (slice_and_tail_entails_vecU8HeapAt A.repAlloc mkCap mkPtr x.st.auth.macKey hmk_le hmk_max hmk_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (slice_and_tail_entails_live_memRegion A.repAlloc esCap esPtr x.st.es hes_le hes_max hesCap_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (slice_and_tail_entails_live_memRegion A.repAlloc ekCap ekPtr x.st.ek hek_le hek_max hekCap_ne)
    (by sep_focus) ?_
  refine SepWPp.fold (vecU8_sp_272_entails A.repAlloc s0.sp x.mac) (by sep_focus) ?_
  sep_elim_exists
  rename_i macCap macPtr
  refine sepWPp_rw_pre_eq (by simp only [RustCliAllocBudget.repAlloc_live]; rfl) ?_
  refine sepWPp_rw_pre_eq (by rw [memRegion_104_cells x.outA]) ?_
  sep_elim_exists
  wp_steps_sync_pool (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_dl1 hs_dl1 => ?_
  rw [← hs_dl1]
  refine SepWPp.fold
    (fold_stA_128 x.stA rkCap rkPtr (BitVec.ofNat 64 x.st.auth.rootKey.length)
      mkCap mkPtr (BitVec.ofNat 64 x.st.auth.macKey.length))
    (by sep_focus) ?_
  have h_ct2_rep : A.live ptr_ct2 128 1 = A.repAlloc.live ptr_ct2 128 1 := by
    simp only [RustCliAllocBudget.repAlloc_live]
  refine sepWPp_rw_pre_eq (by rw [h_ct2_rep]) ?_
  refine SepWPp.fold
    (fold_outA_104 A.repAlloc x rkCap rkPtr mkCap mkPtr ptr_ct2 macCap macPtr
      houtUc hct2_len hptr_ct2_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (fold_sp_264_120 s0.sp macPtr (BitVec.ofNat 64 x.mac.length))
    (by sep_focus) ?_
  refine SepWPp.fold
    (Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp))
    (by sep_focus) ?_
  let F_post : SepProp :=
    memRegion (s0.sp - 16720#64) 12288 ∗
      unchunkedCt2SentAt A.repAlloc x.outA x.outUc ∗
      vecU8 A.repAlloc (x.outA + 56#64) x.ct2 ∗
      vecU8 A.repAlloc (x.outA + 80#64) x.mac ∗
      memRegion x.stA 128 ∗
      ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
      ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
      ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
      ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
      ((s0.sp - 272#64) ↦₆₄ macCap) ∗
      memRegion (s0.sp - 264#64) 120 ∗
      memRegion (s0.sp - 336#64) 8 ∗
      memRegion (s0.sp - 280#64) 8 ∗
      memRegion (s0.sp - 144#64) 24 ∗
      ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
      memRegion (s0.sp - 112#64) 16 ∗
      sendCt2CalleeSavedAt s0 ∗
      unchunkedSendCt2PlacedRoAt
  refine call_rustDealloc_cs_wpp h_dealloc ptr_ct1' cap_ct1'.toNat 1
    (M.stepEvents evsPre5b st0)
    (F_post ∗ ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
      A.live esPtr esCap.toNat 1 ∗ memRegion esPtr esCap.toNat ∗
      A.live ekPtr ekCap.toNat 1 ∗ memRegion ekPtr ekCap.toNat)
    (s0 := s0) (ret_pc := (blkPl_347).base + 896#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_dl1]; wp_norm_goal)
    (by simp only [hs_dl1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_dl1, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, Reg.x1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl1, Reg.x2, wp_norm, arm64_norm, *])
    (by dsimp only [F_post]; sep_ac_rfl)
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  simp only [hs_dl1, wp_norm, arm64_norm, hx19, hx20, hvregs] at hx19_1 hx20_1 hvregs_1
  clear hs_dl1
  have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
  simp only [wp_norm, arm64_norm] at hsp1_norm
  wp_steps_sync_pool (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_dl2 hs_dl2 => ?_
  rw [← hs_dl2]
  refine call_rustDealloc_cs_wpp h_dealloc esPtr esCap.toNat 1
    (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1) (M.stepEvents evsPre5b st0))
    (F_post ∗ ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
      A.live ekPtr ekCap.toNat 1 ∗ memRegion ekPtr ekCap.toNat)
    (s0 := s0) (ret_pc := (blkPl_347).base + 916#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_dl2]; wp_norm_goal)
    (by simp only [hs_dl2, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_dl2, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, Reg.x1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl2, Reg.x2, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_)
  rcases hcs2 with ⟨_, hx20_2, _, _, _, _, _, _, _, _, _, hvregs_2⟩
  simp only [hs_dl2, wp_norm, arm64_norm, hx20_1, hvregs_1] at hx20_2 hvregs_2
  clear hs_dl2
  have hsp2_norm : sf2.readReg64 .sp = s0.sp - 336#64 := hsp2
  simp only [wp_norm, arm64_norm] at hsp2_norm
  wp_steps_sync_pool (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_dl3 hs_dl3 => ?_
  rw [← hs_dl3]
  refine call_rustDealloc_cs_wpp h_dealloc ekPtr ekCap.toNat 1
    (M.stepEvents (rustDeallocEvents esCap.toNat 1)
      (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1) (M.stepEvents evsPre5b st0)))
    (F_post ∗ ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap))
    (s0 := s0) (ret_pc := (blkPl_347).base + 936#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_dl3]; wp_norm_goal)
    (by simp only [hs_dl3, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_dl3, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, Reg.x1, wp_norm, arm64_norm, *])
    (by simp only [hs_dl3, Reg.x2, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 => ?_)
  rcases hcs3 with ⟨_, _, _, _, _, _, _, _, _, _, _, hvregs_3⟩
  simp only [hs_dl3, wp_norm, arm64_norm, hvregs_2] at hvregs_3
  clear hs_dl3
  dsimp only [F_post]
  refine SepWPp.fold
    (Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm)
    (by sep_focus) ?_
  refine sepWPp_rw_pre_eq (by unfold sendCt2CalleeSavedAt; rfl) ?_
  have hsp3_norm : sf3.readReg64 .sp = s0.sp - 336#64 := hsp3
  simp only [wp_norm, arm64_norm] at hsp3_norm
  wp_steps_sync_pool (s0.readReg64 .x30)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_ret hs_ret => ?_
  rw [← hs_ret]
  refine SepWPp.fold
    (fold_stackAt_unchunkedSendCt2 s0 esCap ekCap x.st.epoch
      cap_ct1' ptr_ct1' (BitVec.ofNat 64 x.st.ct1.length) macCap x.st.epoch)
    (by sep_focus) ?_
  have hpool_eq :
      M.stepEvents (rustDeallocEvents ekCap.toNat 1)
        (M.stepEvents (rustDeallocEvents esCap.toNat 1)
          (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1) (M.stepEvents evsPre5b st0))) =
      M.stepEvents (evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap) st0 := by
    rw [← M.stepEvents_append, ← M.stepEvents_append, ← M.stepEvents_append]
    unfold sendCt2Seg5bEvents
    simp only [List.append_assoc]
  refine SepWPp.done
    (by rw [hs_ret]; wp_norm_goal)
    (by simp only [hs_ret, wp_norm, arm64_norm, *]) ?_
  refine ⟨fun hm => ?_, by simp only [hs_ret, State.sp, wp_norm, arm64_norm, *], ?_⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [hs_ret, wp_norm, arm64_norm, *], hPost⟩, ?_⟩
    rw [hpool_eq] at hm
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hs_ret, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, Reg.x29, wp_norm, arm64_norm, *]

theorem send_ct2_epilogue_ret_placed_wpp_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsPre5b : List AllocEvent)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hPost : Env x (evsPre5b ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap))
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128)
    (hes_len : x.st.es.length = 2080)
    (hek_len : x.st.ek.length = 1152)
    (hmk_le : x.st.auth.macKey.length ≤ mkCap.toNat)
    (hmk_max : mkCap.toNat < 2 ^ 63)
    (hmk_ne : mkPtr ≠ 0#64)
    (hes_le : x.st.es.length ≤ esCap.toNat)
    (hes_max : esCap.toNat < 2 ^ 63)
    (hek_le : x.st.ek.length ≤ ekCap.toNat)
    (hek_max : ekCap.toNat < 2 ^ 63)
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hptr_ct2_ne : ptr_ct2 ≠ 0#64)
    (hpc : st.pc = (blkPl_347).base + 836#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx22 : st.readReg64 .x22 = ptr_ct1')
    (hx23 : st.readReg64 .x23 = x.outA)
    (hx24 : st.readReg64 .x24 = x.stA)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (memRegion x.outA 104 ∗
        (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
        ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
        ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        memRegion (x.stA + 48#64) 80 ∗
        vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
        ((s0.sp - 328#64) ↦₆₄ esCap) ∗ (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
        ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        A.live ptr_ct2 128 1 ∗
        vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
        memRegion (s0.sp - 336#64) 8 ∗
        memRegion (s0.sp - 280#64) 8 ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        sendCt2CalleeSavedAt s0 ∗
        unchunkedSendCt2PlacedRoAt ∗
        A.pool lim (M.stepEvents evsPre5b st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack)
      (sendCt2PlacedPostQOfEnv M A lim F K Env x st0 s0 R)
      sendCt2PlacedPostQp :=
  send_ct2_epilogue_ret_placed_wpp_ofPostEnv h_dealloc x st0 evsPre5b
    rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2
    s0 st R hPost houtUc hct2_len hes_len hek_len
    hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
    hpc hrun hsp hsp_s0 htr hvregs hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27

theorem send_ct2_epilogue_ret_placed_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsRes : List AllocEvent)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes)
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128)
    (hes_len : x.st.es.length = 2080)
    (hek_len : x.st.ek.length = 1152)
    (hmk_le : x.st.auth.macKey.length ≤ mkCap.toNat)
    (hmk_max : mkCap.toNat < 2 ^ 63)
    (hmk_ne : mkPtr ≠ 0#64)
    (hes_le : x.st.es.length ≤ esCap.toNat)
    (hes_max : esCap.toNat < 2 ^ 63)
    (hek_le : x.st.ek.length ≤ ekCap.toNat)
    (hek_max : ekCap.toNat < 2 ^ 63)
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hptr_ct2_ne : ptr_ct2 ≠ 0#64)
    (hpc : st.pc = (blkPl_347).base + 836#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx22 : st.readReg64 .x22 = ptr_ct1')
    (hx23 : st.readReg64 .x23 = x.outA)
    (hx24 : st.readReg64 .x24 = x.stA)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (memRegion x.outA 104 ∗
        (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
        ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
        ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        memRegion (x.stA + 48#64) 80 ∗
        vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
        ((s0.sp - 328#64) ↦₆₄ esCap) ∗ (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
        ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        A.live ptr_ct2 128 1 ∗
        vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
        memRegion (s0.sp - 336#64) 8 ∗
        memRegion (s0.sp - 280#64) 8 ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        sendCt2CalleeSavedAt s0 ∗
        unchunkedSendCt2PlacedRoAt ∗
        A.pool lim
          (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) st0)
          st ∗
        stackAt (s0.sp - 336#64) extHookStack)
      (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
      sendCt2PlacedPostQp :=
  send_ct2_epilogue_ret_placed_wpp_ofPostEnv h_dealloc x st0
    (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length)
    rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2
    s0 st R (unchunkedSendCt2PostEnv_of_seg5b hRes cap_ct1' esCap ekCap)
    houtUc hct2_len hes_len hek_len
    hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
    hpc hrun hsp hsp_s0 htr hvregs hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` two-envelope (`PreEnv` / `PostEnv`) correctness theorem for
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (Block `347`) from `subroutine_ok`
    contracts. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_of_contracts_ofPrePostEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → PostEnv x evs)
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv) := by
  have hhmac_safe := subroutine_ok_libcruxHmacSafe_of_budget hhmac
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  refine ⟨(unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv).pre (x, st0) s0,
    R, hpre, sepWPp_of_false_qp ?_⟩
  change SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) s0
    ((unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv).pre (x, st0) s0)
    (sendCt2PlacedPostQOfPostEnv M A lim F K PostEnv x st0 s0 R)
    sendCt2PlacedPostQp
  dsimp only [unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]
  refine sepWPp_pure_left_eq
    (φ := s0.readReg64 .x0 = x.outA ∧ s0.readReg64 .x1 = x.stA ∧
      x.st.send_ct2 K = .ok (x.outUc, x.ct2, x.mac) ∧
      FitsEnv M lim st0 (PreEnv x))
    (memRegion x.outA 104 ∗
      unchunkedCt1SentEkReceivedAt A.repAlloc x.stA x.st ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim st0 s0 ∗ stackAt s0.sp unchunkedSendCt2Stack)
    (by sep_ac_rfl) ?_
  rintro ⟨hx0, hx1, hmodel, hPreRaw⟩
  have hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x) := hPreImp x st0 hPreRaw
  obtain ⟨henc_ok, hmac_ok, houtUc⟩ := send_ct2_ok_elim hmodel
  obtain ⟨hes_len, hek_len, esVec, ekVec, hesVec, hekVec, hct2_eq⟩ := encaps2_ok_elim henc_ok
  obtain ⟨hmk_lt32, hdata_lt32, hmac_eq⟩ := macCt_ok_elim hmac_ok
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hct1_lt32 : x.st.ct1.length < 2 ^ 32 := by
    simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len] at hdata_lt32
    omega
  unfold unchunkedCt1SentEkReceivedAt authenticatorAt
  refine SepWPp.fold (vecU8_entails_cells_and_heap A.repAlloc x.stA x.st.auth.rootKey) (by sep_focus) ?_
  sep_elim_exists
  rename_i rkCap rkPtr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hrk_le, hrk_max, hrk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A.repAlloc (x.stA + 24#64) x.st.auth.macKey) (by sep_focus) ?_
  sep_elim_exists
  rename_i mkCap mkPtr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A.repAlloc (x.stA + 48#64) x.st.es) (by sep_focus) ?_
  sep_elim_exists
  rename_i esCap esPtr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hes_le, hes_max, hes_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A.repAlloc (x.stA + 72#64) x.st.ek) (by sep_focus) ?_
  sep_elim_exists
  rename_i ekCap ekPtr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hek_le, hek_max, hek_ne⟩
  refine SepWPp.fold (vecU8_entails_cells_and_heap A.repAlloc (x.stA + 96#64) x.st.ct1) (by sep_focus) ?_
  sep_elim_exists
  rename_i ct1Cap ct1Ptr
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hct1_le, hct1_max, hct1_ne⟩
  refine sepWPp_rw_pre_eq (by rw [stackAt_unchunkedSendCt2_split s0.sp]) ?_
  sep_elim_exists
  rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 e0 s64 l0 l1 l2 l3 l4 l5
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (SepWPp.of_sepWP
      (mid := (blkPl_347).base + 0x88#64)
      (SepWP.mono
        (send_ct2_prologue_to_scan_placed_pool A lim st0 x.outA x.stA x.st
          rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr
          l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 s0
          (memRegion x.outA 104 ∗
            vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
            (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
            (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
            (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
            unchunkedSendCt2PlacedRoAt ∗
            stackAt (s0.sp - 336#64) extHookStack ∗
            memRegion (s0.sp - 336#64) 8 ∗
            memRegion (s0.sp - 280#64) 8 ∗
            memRegion (s0.sp - 144#64) 24 ∗
            memRegion (s0.sp - 112#64) 16)
          hes_len hek_len hpc hrun hsp hx0 hx1)
        ?_))
  rintro st1 _ hpc1 hrun1 ⟨rfl, hsp1, htr1, hvregs_1, hx8_1, hx9_1, hx10_1, hx11_1, hx13_1,
    hx19_1, hx20_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _hvm1⟩
  let F_base : SepProp :=
    memRegion x.outA 104 ∗
    (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
    ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
    ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
    ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
    memRegion (x.stA + 48#64) 80 ∗
    vecU8HeapAt A.repAlloc rkCap rkPtr x.st.auth.rootKey ∗
    vecU8Tail A.repAlloc mkCap mkPtr x.st.auth.macKey ∗
    ((s0.sp - 328#64) ↦₆₄ esCap) ∗ vecU8Tail A.repAlloc esCap esPtr x.st.es ∗
    ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ vecU8Tail A.repAlloc ekCap ekPtr x.st.ek ∗
    memRegion (s0.sp - 336#64) 8 ∗
    memRegion (s0.sp - 280#64) 8 ∗
    memRegion (s0.sp - 112#64) 16 ∗
    sendCt2CalleeSavedAt s0
  refine sepWPp_rw_pre_eq (by dsimp only [F_base]; sep_ac_rfl)
    (send_ct2_segs_2_to_5a_placed_preEnv_wpp h_res h_concat3 hshim halloc hdealloc
      hmemcpy henc hhmac_safe x st0 mkPtr esPtr ekPtr ct1Cap ct1Ptr e0 esVec ekVec
      s0 st1 F_base hPre hes_len hesVec hekVec hct2_eq hct2_len hek_ne
      hct1_lt32 hmk_lt32 hdata_lt32 hmac_eq hpc1 hrun1 hsp1 hsp htr1 hvregs_1
      hx8_1 hx9_1 hx10_1 hx11_1 hx13_1 hx19_1 hx20_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      (fun st5 cap_ct1' ptr_ct1' ptr_ct2 evsRes hRes
        _hcap_ct1'_ne hge128 _hmax_ct1' _hptr_ct1'_ne hptr_ct2_ne
        hpc5 hrun5 hsp5 htr5 hvregs_5
        hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 _hx29_5 => ?_))
  rw [hx23_1] at hx23_5
  rw [hx24_1] at hx24_5
  exact sepWPp_rw_pre_eq (by dsimp only [F_base]; sep_ac_rfl)
    (send_ct2_epilogue_ret_placed_wpp_ofPostEnv hdealloc x st0
      (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length)
      rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2
      s0 st5 R
      (hPostImp x _ (unchunkedSendCt2PostEnv_of_seg5b hRes cap_ct1' esCap ekCap))
      houtUc hct2_len hes_len hek_len
      hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
      hpc5 hrun5 hsp5 hsp htr5 hvregs_5
      hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5)

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_of_contracts_ofEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → Env x evs)
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv M A lim F K Env) :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok_of_contracts_ofPrePostEnv
    hPreImp hPostImp h_res h_concat3 hshim halloc hdealloc hmemcpy henc hhmac

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_of_contracts
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K) :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok_of_contracts_ofPrePostEnv
    (fun _ _ h => h) (fun _ _ h => h) h_res h_concat3 hshim halloc hdealloc hmemcpy henc hhmac

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_ofPrePostEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → PostEnv x evs)
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv) :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok_of_contracts_ofPrePostEnv
    hPreImp hPostImp h_res h_concat3
    (spqr_hook_ok_of_mem (sym := spqrRustNoAllocShimSym) hshim)
    (spqr_hook_ok_of_mem (sym := spqrRustAllocSym) halloc)
    (spqr_hook_ok_of_mem (sym := spqrRustDeallocSym) hdealloc)
    (spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy)
    (spqr_hook_ok_of_mem (sym := spqrMlkemEncaps2Sym) hencaps2)
    (spqr_hook_ok_of_mem (sym := spqrLibcruxHmacSym) hhmac)

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_ofEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → Env x evs)
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv M A lim F K Env) :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok_ofPrePostEnv
    hPreImp hPostImp h_res h_concat3 hshim halloc hdealloc hmemcpy hencaps2 hhmac

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K) :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok_ofPrePostEnv
    (fun _ _ h => h) (fun _ _ h => h) h_res h_concat3 hshim halloc hdealloc hmemcpy hencaps2 hhmac

theorem unchunkedCt1SentEkReceivedSendCt2PlacedOk_of_hooks
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    UnchunkedCt1SentEkReceivedSendCt2PlacedOk M A lim F K H :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok
    h_res h_concat3 hshim halloc hdealloc hmemcpy hencaps2 hhmac

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_x_ofPrePostEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → PostEnv x evs)
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv)) := by
  refine subroutine_ok_mono
    (unchunked_ct1_sent_ek_received_send_ct2_placed_ok_ofPrePostEnv
      hPreImp hPostImp h_res h_concat3 hshim halloc hdealloc hmemcpy hencaps2 hhmac)
    (fun _ _ _ hpre => ?_) (fun _ _ _ _ hpost => hpost)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_x_ofEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → Env x evs)
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv M A lim F K Env)) :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok_x_ofPrePostEnv
    hPreImp hPostImp h_res h_concat3 hshim halloc hdealloc hmemcpy hencaps2 hhmac

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_x
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)) :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok_x_ofPrePostEnv
    (fun _ _ h => h) (fun _ _ h => h) h_res h_concat3 hshim halloc hdealloc hmemcpy hencaps2 hhmac

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudget
