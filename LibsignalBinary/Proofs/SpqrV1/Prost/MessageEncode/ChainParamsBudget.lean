/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams1Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `ChainParams::encode [local#2]` (`Block 313`)

Proves the 1-byte capacity reservation steppers for Block `313` (`[local#2]`) and instantiates
`ChainParams1Budget.chainParams_core_placed_ok` to establish the `[LibsignalPlacement]` budget
and exact-capacity contracts for `ChainParams::encode [local#2]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAlloc RustCliAllocBudget RustLayoutOk
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalPlacement blkPC_292 blkPC_313 blkPl_292 blkPl_313 blkPl_313_ρ blkPl_320
   lsProg_292 lsProg_313 lsProg_320 ls_resolve_blk_320 ls_subroutine_ok_of_block
   lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack doReserveStackX reserveCap)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero ofNat_countLeadingZeros_32
   ofNat_countLeadingZeros_64 ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (MsgEnc48CalleeSavedPlaced cap_toNat_eq_of_beq lt_cap_toNat_of_beq_false
   reserveCap_one_bounds subroutine_ok_withMsgEnc48CSPlaced_placed withMsgEnc48CSPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (do_reserve_7_placed_ok do_reserve_7_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget (encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
  (encodeVarint4_det_placed_ok_of_doReserve encode_varint4_det_placed_ok
   encode_varint4_det_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep reserveStep_of_need_doReserveEvents reserveStep_of_spare
   sepWP_done_tpidr_placed sepWP_done_vm_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
  (step_msg48_do_reserve7_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (encodeChainParamsSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBasePlacedBudget
  (EncodeChainParams313ExactPlacedOk EncodeChainParams313PlacedOk EncodeChainParams313PlacedOkExt
   EncodeChainParams313PlacedOkExtX EncodeChainParams313PlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams1Budget
  (CpReserve1Stepper chainParams_exact_placed_ok_of_core chainParams_full_placed_ok_of_core
   extract_vecU8At_bounds hookSat_withPanics_spqr isCpPlacedProg_313 rawVmRecordBudget
   vacuous_doReserve7_placed_ok vmRecordBudget zeroEnforcedLimits)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm]
private theorem bv_pc_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_omega

@[local arm64_norm]
private theorem bv_pc_rel_target (b k t : BitVec 64) : b + k + (t - b - k) = t := by bv_omega

local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(CryptoVerification.SpqrV1.Prost.MessageEncode.MsgEnc48CalleeSavedPlaced.step $hcs
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) $hinv)

/-! ## 1. Block `313` (`[local#2]`) 1-Byte Capacity Reservation Steppers -/

theorem step_reserve_212_2_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_313 H) (lsmpl.base 320)
      (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A lim))) :
    CpReserve1Stepper resStack A lim (lsProg_313 H) blkPl_313 212#64 228#64 s0 := by
  intro v curCap curPtr sp curBs p curSt hfit1 hfits s ret P F Q Qp
    hpc hrun hsp halign htr hx19 hx20 hx21 hcs hP hnext
  have hx21' := hx21 rfl; subst hP
  refine extract_vecU8At_bounds A.repAlloc v curCap curPtr curBs
    (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F)
    (by sep_ac_rfl) fun hcap_le _ _ => ?_
  rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    have hres_eq := reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
    have hfits_do : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      rwa [hres_eq] at hfits
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 320)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0; rw [← A.pool_of_vmPreserved hvmp0]
      refine step_msg48_do_reserve7_call_placed hres A lim hdoReserve v curCap curPtr sp
        ((blkPl_313).base + 328#64) curBs 1 curSt hbound1 hfits_do (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      have hx20_1 : s1.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs01.2.1]; simp only [arm64_norm, *]
      have hx21_1 : s1.readReg64 .x21 = p.maxJump.zeroExtend 64 := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_313).base + 228#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvmp1 hinv1
        have hst_eq : M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) curSt =
            M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by rw [hres_eq]
        rw [← A.pool_of_vmPreserved hvmp1, hst_eq]
        refine SepWPp.weaken_pre
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (fun _ => by simp only [arm64_norm, *])
            (cs_step hcs1 hinv1)
            (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega))
            (htoNat1.trans (congrArg Prod.fst hres_eq.symm)))))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    have hres_eq := reserveStep_of_spare (cap := curCap.toNat) (len := curBs.length) (additional := 1) (by omega)
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_313).base + 228#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0
      have hst_eq : curSt = M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by rw [hres_eq]; rfl
      rw [← A.pool_of_vmPreserved hvmp0, hst_eq]
      refine SepWPp.weaken_pre
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (fun _ => by simp only [arm64_norm, *])
          (cs_step hcs hinv0)
          hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (congrArg Prod.fst hres_eq.symm)))

theorem step_reserve_128_2_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_313 H) (lsmpl.base 320)
      (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A lim))) :
    CpReserve1Stepper resStack A lim (lsProg_313 H) blkPl_313 128#64 144#64 s0 := by
  intro v curCap curPtr sp curBs p curSt hfit1 hfits s ret P F Q Qp
    hpc hrun hsp halign htr hx19 hx20 _ hcs hP hnext
  subst hP
  refine extract_vecU8At_bounds A.repAlloc v curCap curPtr curBs
    (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F)
    (by sep_ac_rfl) fun hcap_le _ _ => ?_
  rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    have hres_eq := reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
    have hfits_do : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      rwa [hres_eq] at hfits
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 320)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0; rw [← A.pool_of_vmPreserved hvmp0]
      refine step_msg48_do_reserve7_call_placed hres A lim hdoReserve v curCap curPtr sp
        ((blkPl_313).base + 300#64) curBs 1 curSt hbound1 hfits_do (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      have hx20_1 : s1.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs01.2.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_313).base + 144#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvmp1 hinv1
        have hst_eq : M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) curSt =
            M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by rw [hres_eq]
        rw [← A.pool_of_vmPreserved hvmp1, hst_eq]
        refine SepWPp.weaken_pre
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (fun h => absurd h (by decide))
            (cs_step hcs1 hinv1)
            (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega))
            (htoNat1.trans (congrArg Prod.fst hres_eq.symm)))))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    have hres_eq := reserveStep_of_spare (cap := curCap.toNat) (len := curBs.length) (additional := 1) (by omega)
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_313).base + 144#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0
      have hst_eq : curSt = M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by rw [hres_eq]; rfl
      rw [← A.pool_of_vmPreserved hvmp0, hst_eq]
      refine SepWPp.weaken_pre
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (fun h => absurd h (by decide))
          (cs_step hcs hinv0)
          hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (congrArg Prod.fst hres_eq.symm)))

/-! ## 2. Block `313` (`[local#2]`) Placed Contracts -/

theorem encode_chainParams_2_placed_ok_of_callees [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)}
    (henc0 : subroutine_ok (lsProg_313 H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_313 H) (lsmpl.base 320)
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A lim))) :
    subroutine_ok (lsProg_313 H) (blkPl_313).base
      (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf resStack A lim)) :=
  chainParams_full_placed_ok_of_core hres (isCpPlacedProg_313 H) A lim henc0
    (fun s0 hcl0 => step_reserve_212_2_placed hres A lim
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0))
    (fun s0 hcl0 => step_reserve_128_2_placed hres A lim
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0))
    (fun s0 => ls_subroutine_ok_of_block (callerProg := lsProg_313 H)
      (encodeVarint4_det_placed_ok_of_doReserve (by omega) (vmRecordBudget A s0) zeroEnforcedLimits H
        (vacuous_doReserve7_placed_ok (vmRecordBudget A s0))))
    (fun s0 hcl0 => step_reserve_212_2_placed hres (vmRecordBudget A s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
        (vacuous_doReserve7_placed_ok (vmRecordBudget A s0))))
    (fun s0 hcl0 => step_reserve_128_2_placed hres (vmRecordBudget A s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
        (vacuous_doReserve7_placed_ok (vmRecordBudget A s0))))

theorem encode_chainParams_2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams313PlacedOk A lim H :=
  encode_chainParams_2_placed_ok_of_callees (resStack := doReserveStack) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_313 H)
      (encode_varint4_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_313 H)
      (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))

theorem encode_chainParams_2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams313PlacedOkX A lim H :=
  encode_chainParams_2_placed_ok_of_callees (resStack := doReserveStackX) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_313 H)
      (encode_varint4_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_313 H)
      (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc))

theorem encode_chainParams_2_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams313PlacedOkExt A lim ext :=
  encode_chainParams_2_placed_ok h_panic
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustNoAllocShimSym]) hshim)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustAllocSym]) halloc)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustReallocSym]) hrealloc)

theorem encode_chainParams_2_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams313PlacedOkExtX A lim ext :=
  encode_chainParams_2_placed_ok_x h_panic
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustNoAllocShimSym]) hshim)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustAllocSym]) halloc)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustReallocSym]) hrealloc)

theorem encode_chainParams_2_exact_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (H : String → Option (State → State)) : EncodeChainParams313ExactPlacedOk resStack A H :=
  chainParams_exact_placed_ok_of_core hres (isCpPlacedProg_313 H) A hblk
    (fun s0 => ls_subroutine_ok_of_block (callerProg := lsProg_313 H)
      (encodeVarint4_det_placed_ok_of_doReserve (by omega) (rawVmRecordBudget A hblk s0) zeroEnforcedLimits H
        (vacuous_doReserve7_placed_ok (rawVmRecordBudget A hblk s0))))
    (fun s0 hcl0 => step_reserve_212_2_placed hres (rawVmRecordBudget A hblk s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
        (vacuous_doReserve7_placed_ok (rawVmRecordBudget A hblk s0))))
    (fun s0 hcl0 => step_reserve_128_2_placed hres (rawVmRecordBudget A hblk s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0
        (vacuous_doReserve7_placed_ok (rawVmRecordBudget A hblk s0))))

theorem encode_chainParams_2_exact_cli_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) (A : RustCliAlloc) (H : String → Option (State → State)) :
    EncodeChainParams313ExactPlacedOk resStack A.repAlloc H :=
  encode_chainParams_2_exact_placed_ok hres A.repAlloc A.block_valid H

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBudget
