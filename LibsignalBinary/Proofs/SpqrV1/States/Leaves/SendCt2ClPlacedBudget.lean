/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlaced
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: Closed Budget-Threaded Contract (Block `347`)

Relocatable `[LibsignalPlacement]` budget-threaded Segment 5a (`+676 → +836`) and closed
Block `347` contracts for `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`,
discharging cross-block callees in Blocks `320` and `386` under `withLsCodeLoaded` and
`withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_347 blkPl_347
  extract_withLsCodeLoaded lsLogFilterAddr ls_subroutine_ok_of_block lsmpl lsρ
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator MlKem flipEndiannessOfEncapsulationStateBytes issue1275NeedsFlip
  mlkemEncaps2Spec spqrAuthApi
)
open CryptoVerification.SpqrV1.Alloc (
  spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Auth (
  authenticatorAt pointsTo64_rev64_eq_toBEBytes toBEBytes_8_length
)
open CryptoVerification.SpqrV1.ChainProofs (
  SliceConcat3Ghost bytesAt_false bytesAt_true
)
open CryptoVerification.SpqrV1.Drop (unchunkedCt1SentEkReceivedAt)
open CryptoVerification.SpqrV1.States.Leaves (
  UnchunkedSendCt2Ghost unchunkedSendCt2Stack
)
open CryptoVerification.SpqrV1.Unchunked (
  bytes_rem_entails_memRegion_cap ctLabel_length encaps2_ok_elim
  exists_unpack64_of_length_128 fold_sp_144_24 fold_sp_272_24_24 macCtUnchecked_eq_hmacWith
  macCt_ok_elim memRegion_128_cells memRegion_ct1_split_128_len memRegion_sp_272_split_48_80
  pointsToBytes_append_ct1_ct2 sendCt2CalleeSavedAt send_ct2_ok_elim
  spqrLibcruxHmacSym spqrMlkemEncaps2Sym spqrRustDeallocSym stackAt_extHook_eq_allocHook
  stackAt_unchunkedSendCt2_split unchunkedSendCt2PlacedRoAt vecU8HeapAt vecU8Tail
  vecU8_entails_cells_and_heap vecU8_entails_slice_and_tail
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustCliReallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (
  libcruxHmacBudgetSpec libcruxHmacSha256Events withVmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  SliceConcat3Env sessionMemcpyRegionROSpec sliceConcat3Events sliceConcat3Spec
  slice_concat_3_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  doReserveSpec do_reserve_7_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget (of_sepWP_lscl)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudgetAux (
  call_mlkemEncaps2_vm_lscl_wpp call_rustAllocNoOom_cs_lscl_wpp call_rustDealloc_cs_lscl_wpp
  send_ct2_5d8_to_604_cl_placed_wpp send_ct2_628_to_690_cl_placed_preEnv_wpp
  send_ct2_628_to_690_cl_placed_wpp send_ct2_reserve_ct1_cl_placed_preEnv_wpp
  send_ct2_reserve_ct1_cl_placed_wpp send_ct2_scan_to_628_cl_placed_preEnv_wpp
  send_ct2_scan_to_628_cl_placed_wpp sepWPp_call_lscl_noPanic sepWPp_call_withLscl_noPanic
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (
  call_rustDealloc_cs_wpp expose_concat3_md_sp_144 fitsEvents_hmac_of_concatHmac
  sendCt2Seg5aEvents sepWPp_pure_left_focus
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudget (
  send_ct2_epilogue_ret_placed_wpp_ofPostEnv unchunkedSendCt2PostEnv_of_seg5b
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  SendCt2Reserve128Env UnchunkedCt1SentEkReceivedSendCt2PlacedOk
  UnchunkedSendCt2Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
  fitsEnv_sliceConcat3_of_concatHmac fitsEvents_concatHmac_of_preEnv
  libcruxHmacSafeBudgetSpec sendCt2ConcatHmacEvents sendCt2PlacedPostQOfPostEnv
  sendCt2PlacedPostQp sendCt2Seg23Events send_ct2_prologue_to_scan_placed_pool
  sepWPp_call_noPanic sepWPp_intro_state sepWPp_pure_left_eq sepWPp_rw_pre_eq
  subroutine_ok_libcruxHmacSafe_of_budget unchunkedCt1SentEkReceivedSendCt2PlacedSpec
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv
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

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudgetAux (
  sepWPp_call_lscl_noPanic
  sepWPp_call_withLscl_noPanic
  call_mlkemEncaps2_vm_lscl_wpp
  call_rustAllocNoOom_cs_lscl_wpp
  call_rustDealloc_cs_lscl_wpp
)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudgetAux (
  send_ct2_5d8_to_604_cl_placed_wpp
  send_ct2_scan_to_628_cl_placed_wpp
  send_ct2_scan_to_628_cl_placed_preEnv_wpp
)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudgetAux (
  send_ct2_628_to_690_cl_placed_wpp
  send_ct2_628_to_690_cl_placed_preEnv_wpp
  send_ct2_reserve_ct1_cl_placed_wpp
  send_ct2_reserve_ct1_cl_placed_preEnv_wpp
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

/-! ## 1. `HookSat` Bridge (`rustAllocShimVmSpec` → `DefsBudget.noAllocShimSpec`) -/

/-- Weakens `HookSat H sym rustAllocShimVmSpec` (`AllocCallPreserved ∧ VmPreserved`) to
    `HookSat H sym DefsBudget.noAllocShimSpec` (`sf.trace = s0.trace ∧ VmPreserved`) for
    `DoReserveBudget.do_reserve_7_placed_ok`. -/
theorem hookSat_defsNoAllocShim_of_rustAllocShimVm {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym rustAllocShimVmSpec) :
    HookSat H sym LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec := by
  rcases h with ⟨fn, hH, hok⟩
  refine ⟨fn, hH, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [rustAllocShimVmSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1.2.1, hpost.1.2⟩, hpost.2⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

/-! ## 2. Relocatable Segment 5a (`+676 → +836`) Calling `withLsCodeLoaded` `slice_concat_3` -/

set_option maxHeartbeats 1600000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded Segment 5a (`+676 → +836`) calling
    `slice_concat_3` (Block `386`) under `withLsCodeLoaded lsmpl (sliceConcat3Spec M A lim)`,
    calling `libcrux_hmac::hmac`, and freeing the temporary `35 + 8 + (x.st.ct1.length + 128)`-byte
    MAC input buffer. -/
theorem send_ct2_append_hmac_cl_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat3Spec M A lim)))
    (h_hmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeBudgetSpec F M A lim))
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ)
    (mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hFit : FitsEvents M lim stCost (sendCt2ConcatHmacEvents x.st.ct1.length))
    (hct2_len : x.ct2.length = 128)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 : (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hpc : st.pc = (blkPl_347).base + 676#64)
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
      st'.pc = (blkPl_347).base + 836#64 →
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
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
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
          ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
          A.pool lim (M.stepEvents (sendCt2Seg5aEvents x.st.ct1.length) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
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
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
        A.pool lim stCost st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
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
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hct2_cells⟩ :=
    exists_unpack64_of_length_128 hct2_len
  refine sepWPp_rw_pre_eq (by
    rw [memRegion_ct1_split_128_len ptr_ct1' hge128 hmax_ct1',
      memRegion_128_cells (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length),
      hct2_cells ptr_ct2,
      memRegion_sp_272_split_48_80 s0.sp]) ?_
  sep_elim_exists
  refine of_sepWP_lscl hcl (mid := lsmpl.base 386) ?_
  wp_steps_sync_pool (lsmpl.base 386)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) fun hcl_cc0 => ?_
  refine sepWPp_intro_state fun s_cc hs_cc => ?_
  have hcl_s_cc : LibsignalCodeLoaded lsmpl s_cc.mem := by rw [hs_cc]; exact hcl_cc0
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
  let g_cc : SliceConcat3Ghost :=
    ⟨s0.sp - 144#64, s0.sp - 272#64,
      true, lsρ "spqr:.rodata..Lanon.137", Authenticator.ctLabel,
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
  refine sepWPp_call_withLscl_noPanic hcl_s_cc h_concat3 (g_cc, stCost)
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
    (fun sf_cc hpc_cc hrun_cc hsp_cc_rel hcs_cc _hcl_sf_cc => ?_)
  · intro R' hm
    dsimp only [sliceConcat3Spec, g_cc]
    rw [hsp_cc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, ?_, ?_, ?_, hFit_cc⟩, ?_⟩
    · simp only [hs_cc, Reg.x0, wp_norm, arm64_norm, *]
    · simp only [hs_cc, Reg.x1, wp_norm, arm64_norm, *]
    · simp only [hs_cc, Reg.x2, wp_norm, arm64_norm, *]
    · simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len]; omega
    · simp only [bytesAt_true, bytesAt_false, ctLabel_length, toBEBytes_8_length,
        BitVec.ofNat_eq_ofNat, hs8, hs16, hs24, hs32, hs40] at hm ⊢
      try rw [hct1_full_len] at hm
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
  · simp only [hs_cc, Reg.lr, wp_norm, arm64_norm] at hpc_cc
    dsimp only [sliceConcat3Spec, g_cc]
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
        (lsρ "spqr:.rodata..Lanon.137") 35#64
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
    wp_steps_sync_pool (lsρ spqrLibcruxHmacSym)
    simp only [State.setMem_setMem]
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
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
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
      wp_steps_sync_pool (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
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
      refine call_rustDealloc_cs_wpp h_dealloc ptr_md
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
          ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗ F_frame)
        (s0 := s0) (ret_pc := (blkPl_347).base + 836#64) (sp_call := s0.sp - 336#64)
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

/-- Specialization of `send_ct2_append_hmac_cl_placed_wpp` at
    `stCost := M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0` under
    `FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x)` and
    `SendCt2Reserve128Env x.st.ct1.length evsRes`. -/
theorem send_ct2_append_hmac_cl_placed_preEnv_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat3Spec M A lim)))
    (h_hmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeBudgetSpec F M A lim))
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsRes : List AllocEvent)
    (mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes)
    (hct2_len : x.ct2.length = 128)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 : (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hpc : st.pc = (blkPl_347).base + 676#64)
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
      st'.pc = (blkPl_347).base + 836#64 →
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
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
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
          ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
          A.pool lim
            (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) st0)
            st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
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
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
        A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine send_ct2_append_hmac_cl_placed_wpp h_concat3 h_hmac h_dealloc x
    (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0)
    mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st F_frame hcl
    (fitsEvents_concatHmac_of_preEnv hPre hRes)
    hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
    hpc hrun hsp hsp_s0 htr hvregs hx1 hx25 hx26 hx27 hx29 ?_
  intro st'
  rw [← M.stepEvents_append]
  exact hcont st'

/-! ## 3. Combined Segments 2–5a (`+136 → +836`) & Closed Block-`347` Contracts -/

set_option maxHeartbeats 1200000 in
/-- Combined relocatable `[LibsignalPlacement]` Segments 2–5a (`+136 → +836`) under
    `LibsignalCodeLoaded lsmpl`. -/
theorem send_ct2_segs_2_to_5a_cl_placed_preEnv_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat3Spec M A lim)))
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
    (hhmac_safe : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeBudgetSpec F M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (mkPtr esPtr ekPtr ct1Cap ct1Ptr e0 : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hes_len : x.st.es.length = 2080)
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hct2_len : x.ct2.length = 128)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 :
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
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
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = 1152#64)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st5 : State) (cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
        (evsRes : List AllocEvent),
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      ptr_ct2 ≠ 0#64 →
      st5.pc = (blkPl_347).base + 836#64 →
      st5.status = .Running →
      st5.sp = s0.sp - 336#64 →
      st5.trace = s0.trace →
      calleeSavedVRegs st5 = calleeSavedVRegs s0 →
      st5.readReg64 .x19 = esPtr →
      st5.readReg64 .x20 = ekPtr →
      st5.readReg64 .x22 = ptr_ct1' →
      st5.readReg64 .x23 = st.readReg64 .x23 →
      st5.readReg64 .x24 = st.readReg64 .x24 →
      st5.readReg64 .x25 = mkPtr →
      st5.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length →
      st5.readReg64 .x27 = ptr_ct2 →
      st5.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st5
        (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          unchunkedSendCt2PlacedRoAt ∗
          A.pool lim
            (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) st0)
            st5 ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        unchunkedSendCt2PlacedRoAt ∗
        A.pool lim st0 st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine sepWPp_rw_pre_eq (by unfold unchunkedSendCt2PlacedRoAt; sep_ac_rfl)
    (send_ct2_scan_to_628_cl_placed_preEnv_wpp hshim halloc hmemcpy x st0 esPtr s0 st
      (F_frame ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel))
      hcl hPre hes_len hpc hrun hsp hsp_s0 htr hvregs
      hx8 hx9 hx10 hx11 hx13 hx19 hx28
      (fun st2 esWorkPtr hcl2 hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2
        hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => ?_))
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_628_to_690_cl_placed_preEnv_wpp henc hshim halloc hdealloc x st0
      esPtr ekPtr esWorkPtr esVec ekVec s0 st2
      (F_frame ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel))
      hcl2 hPre hesVec hekVec hct2_eq hekPtr_ne hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2
      hx19_2 (hx20_2.trans hx20) hx21_2 hx22_2 (hx27_2.trans hx27) hx28_2
      (fun st3 ptr_ct2 hcl3 hptr_ct2_ne hpc3 hrun3 hsp3 htr3 hvregs3
        hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 => ?_))
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_reserve_ct1_cl_placed_preEnv_wpp h_res x st0 ct1Cap ct1Ptr s0 st3
      (F_frame ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗ A.live ptr_ct2 128 1 ∗
        memRegion (s0.sp - 272#64) 128 ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel))
      hcl3 hPre hct1_lt32 hpc3 hrun3 hsp3 hsp_s0 htr3 hvregs3
      (fun st4 cap_ct1' ptr_ct1' evsRes hcl4 hRes hcap_ct1'_ne hge128 hmax_ct1' hptr_ct1'_ne
        hpc4 hrun4 hsp4 htr4 hvregs4 hx1_4 hx19_4 hx20_4 hx23_4 hx24_4 hx25_4
        hx26_4 hx27_4 hx29_4 => ?_))
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_append_hmac_cl_placed_preEnv_wpp h_concat3 hhmac_safe hdealloc x st0 evsRes
      mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st4
      (F_frame ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        A.live ptr_ct2 128 1)
      hcl4 hPre hRes hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
      hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hx1_4
      (((hx25_4.trans hx25_3).trans hx25_2).trans hx25)
      (((hx26_4.trans hx26_3).trans hx26_2).trans hx26)
      (hx27_4.trans hx27_3)
      (((hx29_4.trans hx29_3).trans hx29_2).trans hx29)
      (fun st5 hpc5 hrun5 hsp5 htr5 hvregs5 hx19_5 hx20_5 hx22_5 hx23_5 hx24_5
        hx25_5 hx26_5 hx27_5 hx29_5 => ?_))
  exact sepWPp_rw_pre_eq (by unfold unchunkedSendCt2PlacedRoAt; sep_ac_rfl)
    (hcont st5 cap_ct1' ptr_ct1' ptr_ct2 evsRes hRes
      hcap_ct1'_ne hge128 hmax_ct1' hptr_ct1'_ne hptr_ct2_ne
      hpc5 hrun5 hsp5 htr5 hvregs5
      ((hx19_5.trans hx19_4).trans hx19_3)
      ((hx20_5.trans hx20_4).trans hx20_3)
      hx22_5
      (((hx23_5.trans hx23_4).trans hx23_3).trans hx23_2)
      (((hx24_5.trans hx24_4).trans hx24_3).trans hx24_2)
      hx25_5 hx26_5 hx27_5 hx29_5)

private theorem sepWPp_of_false_qp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun _ _ => False)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, hret | ⟨_, _, _, hf⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl hret⟩
  · exact False.elim hf
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` two-envelope (`PreEnv` / `PostEnv`) correctness theorem for
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (Block `347`) under
    `withLsCodeLoaded lsmpl`, from `withLsCodeLoaded` contracts on Block `320` and Block `386`. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts_ofPrePostEnv
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
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat3Spec M A lim)))
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
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv)) := by
  have hhmac_safe := subroutine_ok_libcruxHmacSafe_of_budget hhmac
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre0 hsp
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre0
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
    (of_sepWP_lscl hcl0
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
    hx19_1, hx20_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _hvm1⟩ hcl1
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
    (send_ct2_segs_2_to_5a_cl_placed_preEnv_wpp h_res h_concat3 hshim halloc hdealloc
      hmemcpy henc hhmac_safe x st0 mkPtr esPtr ekPtr ct1Cap ct1Ptr e0 esVec ekVec
      s0 st1 F_base hcl1 hPre hes_len hesVec hekVec hct2_eq hct2_len hek_ne
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

theorem unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts_ofEnv
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
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat3Spec M A lim)))
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
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv M A lim F K Env)) :=
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts_ofPrePostEnv
    hPreImp hPostImp h_res h_concat3 hshim halloc hdealloc hmemcpy henc hhmac

/-- Canonical relocatable `[LibsignalPlacement]` correctness theorem for Block `347` under
    `withLsCodeLoaded lsmpl` from `withLsCodeLoaded` contracts on Block `320` and Block `386`. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat3Spec M A lim)))
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
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)) :=
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts_ofPrePostEnv
    (fun _ _ h => h) (fun _ _ h => h) h_res h_concat3 hshim halloc hdealloc hmemcpy henc hhmac

/-- Closed `[LibsignalPlacement]` two-envelope (`PreEnv` / `PostEnv`) contract for Block `347`
    with `withLsCodeLoaded lsmpl`, discharging Block `320` (`do_reserve_7_placed_ok`) and
    Block `386` (`slice_concat_3_placed_ok`) purely from `HookSat` contracts. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofPrePostEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → PostEnv x evs)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv)) :=
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_of_contracts_ofPrePostEnv
    hPreImp hPostImp
    (ls_subroutine_ok_of_block (i := 347) (j := 320)
      (do_reserve_7_placed_ok h_panic
        (hookSat_defsNoAllocShim_of_rustAllocShimVm hshim) halloc hrealloc))
    (ls_subroutine_ok_of_block (i := 347) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_3_placed_ok hshim halloc hmemcpy hRO)))
    (spqr_hook_ok_of_mem (sym := spqrRustNoAllocShimSym) hshim)
    (spqr_hook_ok_of_mem (sym := spqrRustAllocSym) halloc)
    (spqr_hook_ok_of_mem (sym := spqrRustDeallocSym) hdealloc)
    (spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy)
    (spqr_hook_ok_of_mem (sym := spqrMlkemEncaps2Sym) hencaps2)
    (spqr_hook_ok_of_mem (sym := spqrLibcruxHmacSym) hhmac)

theorem unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → Env x evs)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv M A lim F K Env)) :=
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofPrePostEnv
    hPreImp hPostImp h_panic hshim halloc hrealloc hdealloc hmemcpy hRO hencaps2 hhmac

/-- Closed `[LibsignalPlacement]` contract for
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (Block `347`) with
    `withLsCodeLoaded lsmpl`, purely from `HookSat` contracts. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)) :=
  unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofPrePostEnv
    (fun _ _ h => h) (fun _ _ h => h)
    h_panic hshim halloc hrealloc hdealloc hmemcpy hRO hencaps2 hhmac

/-- Closed `[LibsignalPlacement]` two-envelope (`PreEnv` / `PostEnv`) contract for Block `347`
    with `withLsCodeRoLoaded lsmpl`, purely from `HookSat` contracts. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok_ofPrePostEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → PostEnv x evs)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeRoLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofPrePostEnv
      hPreImp hPostImp h_panic hshim halloc hrealloc hdealloc hmemcpy hRO hencaps2 hhmac)

theorem unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok_ofEnv
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    (hPreImp : ∀ (x : UnchunkedSendCt2Ghost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (UnchunkedSendCt2PreEnv x))
    (hPostImp : ∀ (x : UnchunkedSendCt2Ghost F) (evs : List AllocEvent),
      UnchunkedSendCt2PostEnv x evs → Env x evs)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeRoLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv M A lim F K Env)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok_ofEnv
      hPreImp hPostImp h_panic hshim halloc hrealloc hdealloc hmemcpy hRO hencaps2 hhmac)

/-- Closed `[LibsignalPlacement]` contract for
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (Block `347`) with
    `withLsCodeRoLoaded lsmpl`, purely from `HookSat` contracts. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_cro_placed_ok
    [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeRoLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
      h_panic hshim halloc hrealloc hdealloc hmemcpy hRO hencaps2 hhmac)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2ClPlacedBudget
