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
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedAuxBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `unchunked::EkSentCt1Received::encode [local#2]` (`Block 318`)

Re-exports Stages 1–4 from `EkSentCt1ReceivedPlacedAuxBudget`, proves Stage 5 (`ct1: Vec<u8>`)
and the epilogue on `lsProg_318`, establishes unconditional `[LibsignalPlacement]` budget contracts,
and provides exact-capacity callee bridges for `EncodeToVec` (`Block 426`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement
   blkPC_318 blkPl_292 blkPl_318 blkPl_318_ρ blkPl_320 blkPl_421
   lsMemcpySym lsProg_292 lsProg_318 lsProg_320 lsProg_421 lsmpl lsρ
   ls_resolve_blk_292 ls_resolve_blk_314 ls_resolve_blk_320 ls_resolve_blk_421
   ls_subroutine_ok_of_block withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack doReserveStackX reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost StepInv vecU8At_eq_header_sep_buf)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Varint
  (elem_len_after_reserve_not_ult elem_len_ult_spare_iff
   vecU8At_expose_slice vecU8At_pack_slice)
open CryptoVerification.SpqrV1.ProtoRepr
  (Unchunked4PBGhost ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt
   optAuthenticatorPBPinnedAt unchunked4PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ofNat_length_beq_zero_of_lt ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32)
open CryptoVerification.SpqrV1.Auth
  (authEncodeStackOf cap_toNat_eq_of_beq lt_cap_toNat_of_beq_false reserveCap_one_bounds
   sp_sub_64_aligned vecU8At_bounds_of_satisfies vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (EtvUnchunkedMsgEncodeGhost blkPC_426 blkPl_426 encodeToVecCalleeStackOf)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EkSentCt1ReceivedEncodePinnedGhost UnchunkedEncodeCalleeSavedPlaced
   bs0_append_encodeEkSentCt1ReceivedMsg bs_append_bytesField4_of_ne_empty
   bs_append_bytesFieldTagged_of_empty bytesField4_len_of_ne_empty
   bytesFieldTagged ekSentCt1ReceivedPBEncodedLen_eq_fields_len encodeEkSentCt1ReceivedMsg
   encodeEkSentCt1ReceivedMsg_len_split msgHeaderBytes msgHeaderBytes_len_bounds
   optAuthField2Bytes stackAt_unchunkedMsgEncode
   subroutine_ok_withLsCodeLoaded_unchunked
   subroutine_ok_withUnchunkedEncodeCSPlaced_placed
   subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk
   u64Field1Bytes unchunkedMsgEncodeStackOf vecU8At_expose_src_of_ne_nil_placed
   withUnchunkedEncodeCSPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents fitsEvents_append
   RustCliAllocBudget VmPreserved rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (do_reserve_7_placed_ok do_reserve_7_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
  (encode_varint4_fit_placed_ok encode_varint4_fit_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
  (ekSentCt1ReceivedEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
  (ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_hooks)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (authEncodePinnedSpecOf sepWPp_extract_vecU8At_bounds)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedBudget
  (auth_encode_2_pinned_placed_ok auth_encode_2_pinned_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep reserveStep_of_need_doReserveEvents reserveStep_of_spare
   sepWP_done_tpidr_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (ekSentCt1ReceivedEncodeExactSpecOf ekSentCt1ReceivedEncodePinnedSpecOfEnv
   ekSentCt1ReceivedPinnedToUnpinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
  (CapAfter EkSentCt1ReceivedEncodeEnvS FitsEnv.stageSeq_left FitsEnv.stageSeq_right
   StageSeqEnv StageSeqEnv.intro StageSeqEnv.nonempty
   ekSentCt1ReceivedEncodeEnvS_eq_nil_of_spare ekSentCt1ReceivedEncodePinnedSpecOfS
   fitsEnv_ekSentCt1ReceivedEncodeS_of_spare
   fitsEvents_optBytesReserve_of_fitsEnv fitsEvents_optBytesTag_of_fitsEnv
   hdrFieldEnv optAuthField2Env optAuthField2Env_nonempty
   optBytesField1ByteTagEnv optBytesField1ByteTagEnv_nonempty
   optBytesField1ByteTagEnv_of_empty optBytesField1ByteTagEnv_of_ne_empty
   subroutine_ok_ekSentCt1ReceivedExact_of_pinnedS
   u64Field1Env u64Field1Env_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
  (EkSentCt1ReceivedEncode2PinnedPlacedOkExt EkSentCt1ReceivedEncode2PinnedPlacedOkX
   EkSentCt1ReceivedEncode2PlacedOkExt EkSentCt1ReceivedEncode2PlacedOkX
   ekSentCt1ReceivedEncode_unpinned_of_pinned_placed
   step_unchunked_do_reserve7_call_placed step_unchunked_encode_varint_call_placed
   step_unchunked_memcpy_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlacedAuxBudget
  (doReserveOne_append_encodeVarintEvents_of_eq encodeVarintEvents_after_tag_of_lt)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedAuxBudget
  (IsEkEnc2PlacedProg step_ek_auth_2_placed step_ek_dk_2_placed
   step_ek_epoch_2_placed step_ek_hdr_2_placed)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  blkPl_318_ρ ls_resolve_blk_421 ls_resolve_blk_292 ls_resolve_blk_314 ls_resolve_blk_320

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) :
    a + (b - a) = b := by bv_omega

@[local arm64_norm] private theorem bv_bl_reloc_target (base target k : BitVec 64) :
    base + k + (target - base - k) = target := by bv_omega

@[local arm64_norm] private theorem lsmpl_base_421 [LibsignalPlacement] :
    lsmpl.base 421 = (blkPl_421).base := rfl

@[local arm64_norm] private theorem lsmpl_base_292 [LibsignalPlacement] :
    lsmpl.base 292 = (blkPl_292).base := rfl

@[local arm64_norm] private theorem lsmpl_base_320 [LibsignalPlacement] :
    lsmpl.base 320 = (blkPl_320).base := rfl

@[local arm64_norm] private theorem lsmpl_rho_memcpy [LibsignalPlacement] :
    lsmpl.ρ "memcpy" = lsρ lsMemcpySym := rfl

local macro "an" : term => `(by simp only [arm64_norm, *])
local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(UnchunkedEncodeCalleeSavedPlaced.step $hcs (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) $hinv)

/-! ## 5. Stage 5: Field 4 — `ct1: Vec<u8>` -/

private theorem step_ek_ct1_from_344_2_placed [LibsignalPlacement]
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    (A : RustAlloc)
    (hfn : IsEkEnc2PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr ct1Cap ct1Ptr sp : BitVec 64) (bs_mid ct1 : List (BitVec 8))
    (hct1_ne : ct1.isEmpty = false) (hle : bs_mid.length + ct1.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 344#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ct1Ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs_mid.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = fnBase + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        ((vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr (bs_mid ++ ct1)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  have hct1_ne_nil : ct1 ≠ [] := List.isEmpty_eq_false_iff.mp hct1_ne
  have hct1_pos : 0 < ct1.length := List.length_pos_of_ne_nil hct1_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F) (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x18#64) (cap := ct1Cap) (ptr := ct1Ptr) (bs := ct1)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by sep_ac_rfl) fun hct1_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid ct1.length hle hcap_lt hptr_ne hct1_pos,
    vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 hct1_ne_nil hct1_le]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := memcpy_pc)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        refine step_unchunked_memcpy_call_placed hmemcpy
          (curPtr + BitVec.ofNat 64 bs_mid.length) ct1Ptr sp ((blkPl_318).base + 364#64) ct1
          (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
            A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗
            memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 ct1.length)
              (curCap.toNat - bs_mid.length - ct1.length) ∗
            (vecHeader (msgA + 0x18#64) ct1Cap ct1Ptr (BitVec.ofNat 64 ct1.length) ∗
              ⌜ct1Ptr ≠ 0 ∧ ct1.length ≤ ct1Cap.toNat ∧ ct1Cap.toNat < 2 ^ 63⌝ ∗
              memRegion (ct1Ptr + BitVec.ofNat 64 ct1.length) (ct1Cap.toNat - ct1.length) ∗
              A.live ct1Ptr ct1Cap.toNat 1) ∗ F)
          an an an halign an an an an
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (cs_step hcs hinv1) (by sep_ac_rfl) ?_
        intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hvm_mc
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by
          rw [hcs01.2.2.1]; simp only [arm64_norm, *]
        have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs_mid.length := by
          rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_318).base + 372#64)
        by_vm_steps (
          wp_steps
          exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
            (fun hvm2 hinv2 =>
              SepWPp.weaken_pre
                (by rw [← vecU8At_pack_slice A v curCap curPtr bs_mid ct1 hle hcap_lt hptr_ne hct1_ne_nil,
                      vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 hct1_ne_nil hct1_le]
                    exact Entails.of_eq (by sep_ac_rfl))
                (hnext _ an an an an (cs_step hcs1 hinv2) (hvm1.trans (hvm_mc.trans hvm2)))))))

private theorem step_ek_ct1_from_292_2_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsEkEnc2PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 : State}
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr ct1Cap ct1Ptr sp : BitVec 64) (bs4 ct1 : List (BitVec 8)) (st_tag : M.σ)
    (hct1_ne : ct1.isEmpty = false) (hlt : bs4.length < curCap.toNat)
    (hfit : bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ curCap.toNat ∨
      bs4.length + (bytesFieldTagged 4#32 ct1).length + 10 < 2 ^ 62)
    (hfits_var : FitsEvents M lim st_tag
      (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v curCap curPtr (bs4 ++ [0x22#8]))))
    (hfits_res : ∀ (cap_mid : BitVec 64),
      curCap.toNat ≤ cap_mid.toNat →
      (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat →
        cap_mid = curCap) →
      FitsEvents M lim
        (M.stepEvents
          (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v curCap curPtr (bs4 ++ [0x22#8])))
          st_tag)
        ((reserveStep cap_mid.toNat
          (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 292#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs4.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ct1Ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗
      vecU8At A.repAlloc v curCap curPtr bs4 ∗ A.pool lim st_tag s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap_mid cap5 ptr5 : BitVec 64),
      sm.pc = fnBase + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap_mid.toNat →
      (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat →
        cap_mid = curCap) →
      cap_mid.toNat ≤ cap5.toNat →
      (bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ curCap.toNat →
        cap5 = curCap ∧ ptr5 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗
          vecU8At A.repAlloc v cap5 ptr5 (bs4 ++ bytesFieldTagged 4#32 ct1) ∗
          A.pool lim
            (M.stepEvents
              ((reserveStep cap_mid.toNat
                (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2)
              (M.stepEvents
                (encodeVarintEvents
                  (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v curCap curPtr (bs4 ++ [0x22#8])))
                st_tag))
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hstep344 := step_ek_ct1_from_344_2_placed A.repAlloc hfn hmemcpy
  subst hP
  have hct1_len := bytesField4_len_of_ne_empty hct1_ne
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs4 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        have hvarint_fit :
            (bs4 ++ [0x22#8]).length +
              (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat ∨
            (bs4 ++ [0x22#8]).length + 10 < 2 ^ 62 := by
          rw [List.length_append, List.length_singleton]
          rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
        refine step_unchunked_encode_varint_call_placed hres A lim henc
          (BitVec.ofNat 64 ct1.length) v curCap curPtr sp ((blkPl_318).base + 324#64)
          (bs4 ++ [0x22#8]) st_tag hvarint_fit hfits_var
          (F := vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F)
          an an an halign an an an an (cs_step hcs hinv1)
          (by rw [← A.pool_of_vmPreserved hvm1,
                ← vecU8At_close_one A.repAlloc v curCap curPtr bs4 0x22#8 hlt]; try sep_ac_rfl) ?_
        intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
        let bs_mid := (bs4 ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 ct1.length)
        let st_mid := M.stepEvents
          (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v curCap curPtr (bs4 ++ [0x22#8])))
          st_tag
        have hbs_mid_len :
            bs_mid.length + ct1.length = bs4.length + (bytesFieldTagged 4#32 ct1).length := by
          dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hct1_len]; omega
        have hcap_mid_pres :
            bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat →
            cap_mid = curCap := by
          intro h; apply (hpres_mid ?_).1; rw [List.length_append, List.length_singleton]; exact h
        have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
        have hx20_2 : s2.readReg64 .x20 = ct1Ptr := by rw [hcs12.2.1]; simp only [arm64_norm, *]
        have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by
          rw [hcs12.2.2.1]; simp only [arm64_norm, *]
        refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap_mid)
          (ptr := ptr_mid) (bs := bs_mid)
          (F := A.pool lim st_mid s2 ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
            vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F)
          (by dsimp [bs_mid, st_mid]; try sep_ac_rfl) fun hle_mid hcap_mid_lt _ => ?_
        rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_mid ptr_mid bs_mid, vecHeader]
        have hct1_lt63 : ct1.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
        by_cases hneed : cap_mid.toNat < bs_mid.length + ct1.length
        · have hfit_ct1 : bs_mid.length + ct1.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
          have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 ct1.length) = true :=
            (elem_len_ult_spare_iff hle_mid hcap_mid_lt hct1_lt63).mpr hneed
          obtain ⟨hnot_ult, hle_res, hge_res, hbound_ct1⟩ := elem_len_after_reserve_not_ult hfit_ct1 hneed
          have hneed' : ¬ (bs_mid.length + ct1.length ≤ cap_mid.toNat) := by omega
          have hev_res : doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid ct1.length) =
              (reserveStep cap_mid.toNat
                (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2 := by
            have h1 := congrArg Prod.snd
              (reserveStep_of_need_doReserveEvents v cap_mid ptr_mid bs_mid ct1.length hneed')
            dsimp only at h1
            have hbs_eq : bs_mid.length = bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← h1, hbs_eq]
          have hfits_res_call : FitsEvents M lim st_mid
              (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid ct1.length)) := by
            rw [hev_res]; exact hfits_res cap_mid hge_mid hcap_mid_pres
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_320).base)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 => by
                refine step_unchunked_do_reserve7_call_placed hres A lim hdoReserve v cap_mid ptr_mid sp
                  ((blkPl_318).base + 612#64) bs_mid ct1.length st_mid hbound_ct1 hfits_res_call
                  (F := vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F)
                  an an an halign an an an
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  an an (cs_step hcs2 hinv2)
                  (by rw [← A.pool_of_vmPreserved hvm2]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
                intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
                let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length ct1.length)
                change (BitVec.ofNat 64 ct1.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
                have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
                have hx20_3 : s3.readReg64 .x20 = ct1Ptr := by rw [hcs23.2.1]; simp only [arm64_norm, *]
                have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by
                  rw [hcs23.2.2.1]; simp only [arm64_norm, *]
                rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_res ptr_res bs_mid, vecHeader]
                apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_318).base + 344#64)
                by_vm_steps (
                  wp_steps
                  exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                    (fun hvm3 hinv3 =>
                      hstep344 msgA v cap_res ptr_res ct1Cap ct1Ptr sp bs_mid ct1 hct1_ne hle_res
                        (F := A.pool lim
                            (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid ct1.length)) st_mid) s3 ∗
                          stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
                        an an an halign an an an an an (cs_step hcs3 hinv3)
                        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                        (fun sm hpcm hrunm hspm htrm hcsm hvm344 =>
                          SepWPp.weaken_pre
                            (by dsimp [bs_mid, st_mid]
                                rw [← A.pool_of_vmPreserved (hvm3.trans hvm344), hev_res,
                                  bs_append_bytesField4_of_ne_empty hct1_ne bs4]
                                exact Entails.of_eq (by sep_ac_rfl))
                            (hnext sm cap_mid cap_res ptr_res hpcm hrunm hspm htrm hcsm
                              hge_mid hcap_mid_pres hge_res (fun h => absurd h (by omega))))))))
        · have hle_fast : bs_mid.length + ct1.length ≤ cap_mid.toNat := by omega
          have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 ct1.length) = false :=
            Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hct1_lt63).mp h)
          have hpres_all : bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ curCap.toNat →
              cap_mid = curCap ∧ ptr_mid = curPtr := by
            intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
          have hev_res_nil :
              (reserveStep cap_mid.toNat
                (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2 = [] := by
            have hbs_eq : bs_mid.length = bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← hbs_eq, reserveStep_of_spare hle_fast]
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_318).base + 344#64)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 =>
                hstep344 msgA v cap_mid ptr_mid ct1Cap ct1Ptr sp bs_mid ct1 hct1_ne hle_fast
                  (F := A.pool lim st_mid s2 ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
                  an an an halign an an an an an (cs_step hcs2 hinv2)
                  (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                  (fun sm hpcm hrunm hspm htrm hcsm hvm344 =>
                    SepWPp.weaken_pre
                      (by dsimp [bs_mid, st_mid]
                          rw [← A.pool_of_vmPreserved (hvm2.trans hvm344), hev_res_nil, M.stepEvents_nil,
                            bs_append_bytesField4_of_ne_empty hct1_ne bs4]
                          exact Entails.of_eq (by sep_ac_rfl))
                      (hnext sm cap_mid cap_mid ptr_mid hpcm hrunm hspm htrm hcsm
                        hge_mid hcap_mid_pres (Nat.le_refl _) hpres_all))))))


theorem step_ek_ct1_2_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsEkEnc2PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 s : State}
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v cap4 ptr4 ct1Cap ct1Ptr sp : BitVec 64) (bs4 ct1 : List (BitVec 8)) (curSt : M.σ)
    (hfit : bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ cap4.toNat ∨
      bs4.length + (bytesFieldTagged 4#32 ct1).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (optBytesField1ByteTagEnv cap4 bs4.length ct1))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 264#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗
      vecU8At A.repAlloc v cap4 ptr4 bs4 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64) (evs₅ : List AllocEvent),
      sm.pc = fnBase + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap4.toNat ≤ cap5.toNat →
      (bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ cap4.toNat →
        cap5 = cap4 ∧ ptr5 = ptr4) →
      optBytesField1ByteTagEnv cap4 bs4.length ct1 evs₅ →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗
          vecU8At A.repAlloc v cap5 ptr5 (bs4 ++ bytesFieldTagged 4#32 ct1) ∗
          A.pool lim (M.stepEvents evs₅ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hstep292 := step_ek_ct1_from_292_2_placed hres A lim hfn henc hdoReserve hmemcpy
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := msgA + 0x18#64) (cap := ct1Cap)
    (ptr := ct1Ptr) (bs := ct1)
    (F := vecU8At A.repAlloc v cap4 ptr4 bs4 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hct1_le hct1_cap_lt _ => ?_
  have ⟨hct1_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := ct1) (by omega)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases hct1 : ct1.isEmpty
  · have hct1_len := bytesField4_len_of_ne_empty hct1
    have hfits_tag := fitsEvents_optBytesTag_of_fitsEnv hct1 hfits
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap4)
      (ptr := ptr4) (bs := bs4)
      (F := vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ A.pool lim curSt s ∗
        stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun hcap4_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap4 ptr4 bs4, vecHeader,
      vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1, vecHeader]
    by_cases hcap4 : cap4 == BitVec.ofNat 64 bs4.length
    · have hcap_eq : cap4.toNat = bs4.length :=
        cap_toNat_eq_of_beq hcap4 (Nat.lt_of_le_of_lt hcap4_le (BitVec.isLt cap4))
      have hfit2 : bs4.length + (bytesFieldTagged 4#32 ct1).length + 10 < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      have hres_lt64 : reserveCap cap4.toNat bs4.length 1 < 2 ^ 64 := by omega
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_320).base)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 => by
            have hfits_res1 : FitsEvents M lim curSt
                (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bs4 1)) := by
              have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
                (BitVec.ofNat 64 ct1.length) v cap4 ptr4 0#64 bs4 0x22#8 hcap_eq hres_lt64
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).1
            refine step_unchunked_do_reserve7_call_placed hres A lim hdoReserve v cap4 ptr4 sp
              ((blkPl_318).base + 580#64) bs4 1 curSt hbound1 hfits_res1
              (F := vecU8At A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F)
              an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
              an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]
                  simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
            intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
            let newCap1 := BitVec.ofNat 64 (reserveCap cap4.toNat bs4.length 1)
            have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
              (BitVec.ofNat 64 ct1.length) v cap4 ptr4 newPtr1 bs4 0x22#8 hcap_eq hres_lt64
            have hfits_var : FitsEvents M lim
                (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bs4 1)) curSt)
                (encodeVarintEvents
                  (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v newCap1 newPtr1 (bs4 ++ [0x22#8]))) := by
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).2
            have hfits_res2 : ∀ (cap_mid : BitVec 64),
                newCap1.toNat ≤ cap_mid.toNat →
                (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ newCap1.toNat →
                  cap_mid = newCap1) →
                FitsEvents M lim
                  (M.stepEvents
                    (encodeVarintEvents
                      (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v newCap1 newPtr1 (bs4 ++ [0x22#8])))
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bs4 1)) curSt))
                  ((reserveStep cap_mid.toNat
                    (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2) := by
              intro cap_mid hge_m _
              rw [← M.stepEvents_append, hev_eq]
              exact fitsEvents_optBytesReserve_of_fitsEnv hct1 hfits
                ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩
            have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
            rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs4, vecHeader]
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_318).base + 292#64)
            by_vm_steps (
              wp_steps
              exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                (fun hvm1 hinv1 =>
                  hstep292 msgA v newCap1 newPtr1 ct1Cap ct1Ptr sp bs4 ct1
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bs4 1)) curSt)
                    hct1 hlt1 (Or.inr hfit2) hfits_var hfits_res2 (F := F)
                    an an an halign an an an
                    (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
                    (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
                    (cs_step hcs1 hinv1)
                    (by rw [← A.pool_of_vmPreserved hvm1]
                        simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                    (fun sm cap_mid cap5 ptr5 hpcm hrunm hspm htrm hcsm hge_m _ hge5 _ =>
                      SepWPp.weaken_pre
                        (by rw [← M.stepEvents_append, ← M.stepEvents_append, ← List.append_assoc]
                            dsimp only [newCap1]; rw [hev_eq]
                            exact Entails.of_eq (by sep_ac_rfl))
                        (hnext sm cap5 ptr5 _ hpcm hrunm hspm htrm hcsm
                          (Nat.le_trans hge1 (Nat.le_trans hge_m hge5))
                          (fun h => absurd h (by omega))
                          (optBytesField1ByteTagEnv_of_ne_empty hct1
                            ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩)))))))
    · have hcap4_f : (cap4 == BitVec.ofNat 64 bs4.length) = false := Bool.eq_false_iff.mpr hcap4
      have hlt4 : bs4.length < cap4.toNat :=
        lt_cap_toNat_of_beq_false hcap4_f hcap4_le (Nat.lt_of_le_of_lt hcap4_le (BitVec.isLt cap4))
      have hev_eq := encodeVarintEvents_after_tag_of_lt
        (BitVec.ofNat 64 ct1.length) v cap4 ptr4 bs4 0x22#8 hlt4
      have hfits_var : FitsEvents M lim curSt
          (encodeVarintEvents
            (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v cap4 ptr4 (bs4 ++ [0x22#8]))) := by
        rwa [hev_eq]
      have hfits_res2 : ∀ (cap_mid : BitVec 64),
          cap4.toNat ≤ cap_mid.toNat →
          (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ cap4.toNat →
            cap_mid = cap4) →
          FitsEvents M lim
            (M.stepEvents
              (encodeVarintEvents
                (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v cap4 ptr4 (bs4 ++ [0x22#8])))
              curSt)
            ((reserveStep cap_mid.toNat
              (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2) := by
        intro cap_mid hge_m hpres_m
        rw [hev_eq]
        exact fitsEvents_optBytesReserve_of_fitsEnv hct1 hfits
          ⟨hge_m, fun h => hpres_m (by omega)⟩
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_318).base + 292#64)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 =>
            hstep292 msgA v cap4 ptr4 ct1Cap ct1Ptr sp bs4 ct1 curSt hct1 hlt4 hfit
              hfits_var hfits_res2 (F := F)
              an an an halign an an an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]
                  simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
              (fun sm cap_mid cap5 ptr5 hpcm hrunm hspm htrm hcsm hge_m hpres_m hge5 hpres5 =>
                SepWPp.weaken_pre
                  (by rw [hev_eq, ← M.stepEvents_append]; exact Entails.of_eq (by sep_ac_rfl))
                  (hnext sm cap5 ptr5 _ hpcm hrunm hspm htrm hcsm
                    (Nat.le_trans hge_m hge5) hpres5
                    (optBytesField1ByteTagEnv_of_ne_empty hct1
                      ⟨hge_m, fun h => hpres_m (by omega)⟩)))))
  · rw [vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_318).base + 372#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 =>
          SepWPp.weaken_pre
            (by rw [← A.pool_of_vmPreserved hvm0, ← M.stepEvents_nil curSt,
                  ← bs_append_bytesFieldTagged_of_empty 4#32 hct1 bs4,
                  vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x18#64) ct1Cap ct1Ptr ct1, vecHeader]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ cap4 ptr4 [] an an an an (cs_step hcs hinv0)
              (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (optBytesField1ByteTagEnv_of_empty hct1))))

/-! ## 6. Epilogue & Top-Level Placed `subroutine_ok` for `encode<EkSentCt1Received> [local#2]` -/

/-- Epilogue (`+0x174 .. +0x188`) of `encode<EkSentCt1Received> [local#2]` (Block `318`). -/
theorem step_ek_epilogue_2_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn : IsEkEnc2PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (sp sv3 : BitVec 64) {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnBase + 372#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State), sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp →
      sf.trace = s0.trace → CalleeSavedPreserved s0 sf → StepInv s0 sf → VmPreserved s sf →
      Q sf (stackAt sp (unchunkedMsgEncodeStackOf resStack) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  subst hP
  have hsp_aligned := sp_sub_64_aligned halign
  apply sepWPp_of_sepWP_cs_vm_placed (mid := s0.readReg64 .lr)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm hinv => by
        have hcs' := cs_step hcs hinv
        refine SepWPp.weaken_pre ?_
          (SepWPp.done an an
            (hnext _ an an an an
              ⟨an, an, an, an, an, hcs'.1, hcs'.2.1, hcs'.2.2.1, hcs'.2.2.2.1,
                hcs'.2.2.2.2.1, an, hcs'.2.2.2.2.2.1⟩
              hcs'.2.2.2.2.2.2.1 hvm))
        rw [stackAt_unchunkedMsgEncode hres sp]
        refine sepConj_mono_left (sepConj_mono_right ?_)
        exact Entails.sepExists_right (s0.readReg64 .fp)
          (Entails.sepExists_right (s0.readReg64 .lr)
            (Entails.sepExists_right (s0.readReg64 .x23)
              (Entails.sepExists_right sv3
                (Entails.sepExists_right (s0.readReg64 .x22)
                  (Entails.sepExists_right (s0.readReg64 .x21)
                    (Entails.sepExists_right (s0.readReg64 .x20)
                      (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))))

/-- General `SepWPp` correctness for `encode<EkSentCt1Received> [local#2]` under `IsEkEnc2PlacedProg`. -/
theorem ekSentCt1ReceivedEncode2_gen_ok_prog [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn : IsEkEnc2PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {x : EkSentCt1ReceivedEncodePinnedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hencLen : subroutine_ok prog encLen_pc
      (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A.repAlloc)))
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hauth : subroutine_ok prog auth_pc
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (hpc : s0.pc = fnBase) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp prog (s0.readReg64 .lr) s0 P
      (fun s' Q =>
        ((s'.mem ⊨ Q ∗ R) →
          (s'.mem ⊨ (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      Qp oom := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre
  dsimp only [ekSentCt1ReceivedEncodePinnedSpecOfS, ekSentCt1ReceivedEncodePinnedSpecOfEnv] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hfit, hfits0⟩, hpre_mem⟩ := hpre_pure
  obtain ⟨hcap_le, _, _⟩ := vecU8At_bounds_of_satisfies (A := A.repAlloc)
    (v := x.v) (cap := x.cap) (ptr := x.ptr) (bs := x.bs)
    (F := ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗ A.pool lim st0 s0 ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R)
    (by convert hpre_mem using 1; sep_ac_rfl)
  have hpre_rewritten : s0.mem ⊨
      ((ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
        vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s0 ∗
        stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)) ∗ emp) ∗ R := by
    rw [sepConj_emp]; convert hpre_mem using 1
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodeEkSentCt1ReceivedMsg_len_split x.m
  have hhdr_bds := msgHeaderBytes_len_bounds (ekSentCt1ReceivedPBEncodedLen x.m)
  have hlen_eq_fields := ekSentCt1ReceivedPBEncodedLen_eq_fields_len x.m
  have hlen_fit : ekSentCt1ReceivedPBEncodedLen x.m < 2 ^ 64 := by rcases hfit with h | h <;> omega
  have hfit_hdr :
      x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length ≤ x.cap.toNat ∨
      x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  dsimp only [EkSentCt1ReceivedEncodeEnvS, ekSentCt1ReceivedPinnedToUnpinned] at hfits0
  let innerLen := ekSentCt1ReceivedPBEncodedLen x.m
  let l0 := x.bs.length
  let a1 := (msgHeaderBytes innerLen).length
  let l1 := l0 + a1
  let a2 := (u64Field1Bytes x.m.epoch).length
  let l2 := l1 + a2
  let a3 := (optAuthField2Bytes x.m.auth).length
  let l3 := l2 + a3
  let a4 := (bytesFieldTagged 3#32 x.m.dk).length
  let l4 := l3 + a4
  have hne4 : ∀ c, ∃ e, StageSeqEnv c l3 a4 (optBytesField1ByteTagEnv c l3 x.m.dk)
      (fun cap4 => optBytesField1ByteTagEnv cap4 l4 x.m.ct1) e :=
    fun c => StageSeqEnv.nonempty
      (optBytesField1ByteTagEnv_nonempty c l3 x.m.dk)
      (optBytesField1ByteTagEnv_nonempty _ l4 x.m.ct1)
  have hne3 : ∀ c, ∃ e, StageSeqEnv c l2 a3 (optAuthField2Env c l2 x.m.auth)
      (fun cap3 => StageSeqEnv cap3 l3 a4 (optBytesField1ByteTagEnv cap3 l3 x.m.dk)
        fun cap4 => optBytesField1ByteTagEnv cap4 l4 x.m.ct1) e :=
    fun c => StageSeqEnv.nonempty (optAuthField2Env_nonempty c l2 x.m.auth) (hne4 c)
  have hne2 : ∀ c, ∃ e, StageSeqEnv c l1 a2 (u64Field1Env c l1 x.m.epoch)
      (fun cap2 => StageSeqEnv cap2 l2 a3 (optAuthField2Env cap2 l2 x.m.auth)
        fun cap3 => StageSeqEnv cap3 l3 a4 (optBytesField1ByteTagEnv cap3 l3 x.m.dk)
          fun cap4 => optBytesField1ByteTagEnv cap4 l4 x.m.ct1) e :=
    fun c => StageSeqEnv.nonempty (u64Field1Env_nonempty c l1 x.m.epoch) (hne3 c)
  refine step_ek_hdr_2_placed hres A lim hfn hencLen henc hdoReserve
    x.g x.msgA x.v x.cap x.ptr s0.sp x.bs x.m st0 hcap_le hlen_fit hfit_hdr
    (FitsEnv.stageSeq_left hfits0 (hne2 x.cap))
    (F := emp) hpc hrun rfl halign rfl hx0 hx1 (UnchunkedEncodeCalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 sv3 evs₁ hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hge1 hpres1 hev1
  have hcap1 : CapAfter x.cap l0 a1 cap1 := ⟨hge1, fun h => (hpres1 h).1⟩
  have hfits1 := FitsEnv.stageSeq_right hfits0 hev1 hcap1
  let bs1 := x.bs ++ msgHeaderBytes innerLen
  let st1 := M.stepEvents evs₁ st0
  let S := ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ sv3) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hbs1_len : bs1.length = l1 := List.length_append
  have hfit_ep : bs1.length + a2 ≤ cap1.toNat ∨ bs1.length + a2 + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1, a2] at hbs1_len ⊢
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_epoch_2_placed hres A lim hfn henc hdoReserve
    x.msgA x.v cap1 ptr1 x.m.epoch s0.sp bs1 st1 hfit_ep
    (by rw [hbs1_len]; exact FitsEnv.stageSeq_left hfits1 (hne3 cap1))
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.dk ∗
      vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.ct1 ∗
      optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x30#64) x.m.auth ∗ S ∗ emp)
    (by dsimp [bs1, st1, S, ekSentCt1ReceivedPBPinnedAt, unchunked4PinnedAt]; sep_ac_rfl) ?_
  intro s2 cap2 ptr2 evs₂ hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2 hev2
  rw [hbs1_len] at hev2
  have hcap2 : CapAfter cap1 l1 a2 cap2 :=
    ⟨hge2, fun h => (hpres2 (by rw [hbs1_len]; exact h)).1⟩
  have hfits2 := FitsEnv.stageSeq_right hfits1 hev2 hcap2
  let bs2 := bs1 ++ u64Field1Bytes x.m.epoch
  let st2 := M.stepEvents evs₂ st1
  have hbs2_len : bs2.length = l2 := by dsimp [bs2, l2]; rw [List.length_append, hbs1_len]
  have hfit_auth : bs2.length + a3 ≤ cap2.toNat ∨ bs2.length + a3 + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1, a2, l2, a3] at hbs2_len ⊢
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_auth_2_placed A lim hfn hauth
    x.g.auth x.msgA x.v cap2 ptr2 s0.sp bs2 x.m.auth st2 hfit_auth
    (by rw [hbs2_len]; exact FitsEnv.stageSeq_left hfits2 (hne4 cap2))
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := ((x.msgA + 0x60#64) ↦₆₄ x.m.epoch) ∗
      vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.dk ∗
      vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs2, st2]; sep_ac_rfl) ?_
  intro s3 cap3 ptr3 evs₃ hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hge3 hpres3 hev3
  rw [hbs2_len] at hev3
  have hcap3 : CapAfter cap2 l2 a3 cap3 :=
    ⟨hge3, fun h => (hpres3 (by rw [hbs2_len]; exact h)).1⟩
  have hfits3 := FitsEnv.stageSeq_right hfits2 hev3 hcap3
  let bs3 := bs2 ++ optAuthField2Bytes x.m.auth
  let st3 := M.stepEvents evs₃ st2
  have hbs3_len : bs3.length = l3 := by dsimp [bs3, l3]; rw [List.length_append, hbs2_len]
  have hfit_dk : bs3.length + a4 ≤ cap3.toNat ∨ bs3.length + a4 + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1, a2, l2, a3, l3, a4] at hbs3_len ⊢
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_dk_2_placed hres A lim hfn henc hdoReserve hmemcpy
    x.msgA x.v cap3 ptr3 x.g.f3.cap x.g.f3.ptr s0.sp bs3 x.m.dk st3 hfit_dk
    (by rw [hbs3_len]; exact FitsEnv.stageSeq_left hfits3 (optBytesField1ByteTagEnv_nonempty _ l4 x.m.ct1))
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x30#64) x.m.auth ∗
      ((x.msgA + 0x60#64) ↦₆₄ x.m.epoch) ∗
      vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs3, st3]; sep_ac_rfl) ?_
  intro s4 cap4 ptr4 evs₄ hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 hge4 hpres4 hev4
  rw [hbs3_len] at hev4
  have hcap4 : CapAfter cap3 l3 a4 cap4 :=
    ⟨hge4, fun h => (hpres4 (by rw [hbs3_len]; exact h)).1⟩
  have hfits4 := FitsEnv.stageSeq_right hfits3 hev4 hcap4
  let bs4 := bs3 ++ bytesFieldTagged 3#32 x.m.dk
  let st4 := M.stepEvents evs₄ st3
  have hbs4_len : bs4.length = l4 := by dsimp [bs4, l4]; rw [List.length_append, hbs3_len]
  have hfit_ct1 : bs4.length + (bytesFieldTagged 4#32 x.m.ct1).length ≤ cap4.toNat ∨
      bs4.length + (bytesFieldTagged 4#32 x.m.ct1).length + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1, a2, l2, a3, l3, a4, l4] at hbs4_len ⊢
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_ct1_2_placed hres A lim hfn henc hdoReserve hmemcpy
    x.msgA x.v cap4 ptr4 x.g.f4.cap x.g.f4.ptr s0.sp bs4 x.m.ct1 st4 hfit_ct1
    (by rw [hbs4_len]; exact hfits4)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4
    (F := vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.dk ∗
      optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x30#64) x.m.auth ∗
      ((x.msgA + 0x60#64) ↦₆₄ x.m.epoch) ∗ S ∗ emp)
    (by dsimp [bs4, st4]; sep_ac_rfl) ?_
  intro s5 cap5 ptr5 evs₅ hpc5 hrun5 hsp5 htr5 hcs5 hge5 hpres5 hev5
  rw [hbs4_len] at hev5
  let st5 := M.stepEvents evs₅ st4
  refine step_ek_epilogue_2_placed hres hfn s0.sp sv3
    (F := vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.ct1 ∗
      vecU8At A.repAlloc x.v cap5 ptr5 (bs4 ++ bytesFieldTagged 4#32 x.m.ct1) ∗
      A.pool lim st5 s5 ∗
      vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.dk ∗
      optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x30#64) x.m.auth ∗
      ((x.msgA + 0x60#64) ↦₆₄ x.m.epoch) ∗ emp)
    hpc5 hrun5 hsp5 halign htr5 hcs5 (by dsimp [S, st5]; sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hcc _ hvmf
  refine ⟨fun hm => ?_, hspf, hcc⟩
  have hge_all : x.cap.toNat ≤ cap5.toNat :=
    Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 (Nat.le_trans hge4 hge5)))
  have hpres_all : x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
      cap5 = x.cap ∧ ptr5 = x.ptr := by
    intro hfit_cap
    dsimp only [innerLen, l0, a1, l1, a2, l2, a3, l3, a4, l4]
      at hbs1_len hbs2_len hbs3_len hbs4_len
    obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
    obtain ⟨hc2, hp2⟩ := hpres2 (by omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by omega)
    obtain ⟨hc4, hp4⟩ := hpres4 (by omega)
    obtain ⟨hc5, hp5⟩ := hpres5 (by omega)
    exact ⟨hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))),
      hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1)))⟩
  let evsAll := evs₁ ++ (evs₂ ++ (evs₃ ++ (evs₄ ++ evs₅)))
  have hevAll : EkSentCt1ReceivedEncodeEnvS (ekSentCt1ReceivedPinnedToUnpinned x) evsAll :=
    StageSeqEnv.intro hev1 hcap1
      (StageSeqEnv.intro hev2 hcap2
        (StageSeqEnv.intro hev3 hcap3
          (StageSeqEnv.intro hev4 hcap4 hev5)))
  have hst_eq : M.stepEvents evsAll st0 = st5 := by
    dsimp only [evsAll, st5, st4, st3, st2, st1]
    simp only [M.stepEvents_append]
  dsimp only [ekSentCt1ReceivedEncodePinnedSpecOfS, ekSentCt1ReceivedEncodePinnedSpecOfEnv]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evsAll, cap5, ptr5, ?_⟩
  have hpure1 : (x.cap.toNat ≤ cap5.toNat ∧
      (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
        cap5 = x.cap ∧ ptr5 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  have hpure2 :
      EkSentCt1ReceivedEncodeEnvS (ekSentCt1ReceivedPinnedToUnpinned x) evsAll = True :=
    eq_true hevAll
  rw [hpure1, hpure2, pure_true, emp_sepConj, emp_sepConj, hst_eq,
    ekSentCt1ReceivedPBPinnedAt, unchunked4PinnedAt, ← bs0_append_encodeEkSentCt1ReceivedMsg x.bs x.m]
  dsimp only [bs4, bs3, bs2, bs1, innerLen] at hm
  rw [← A.pool_of_vmPreserved hvmf, sepConj_emp] at hm
  convert hm using 1; sep_ac_rfl

theorem ek_sent_ct1_received_encode_2_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode2PinnedPlacedOkExt A lim H := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  have hfn2 : IsEkEnc2PlacedProg (lsProg_318 H) (blkPl_318).base (blkPl_421).base
      (blkPl_292).base (lsmpl.base 314) (blkPl_320).base (lsρ lsMemcpySym) :=
    ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hencLen0 : subroutine_ok (lsProg_421 H) (blkPl_421).base
      (ekSentCt1ReceivedEncodedLenPinnedSpec A.repAlloc) :=
    ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_hooks A.repAlloc H
  have henc0 : subroutine_ok (lsProg_292 H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf doReserveStack A lim)) :=
    encode_varint4_fit_placed_ok h_panic hshim halloc hrealloc
  have hauth0 : subroutine_ok (lsProg_318 H) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf doReserveStack A lim)) :=
    ls_subroutine_ok_of_block (auth_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc)
  have hdoRes0 : subroutine_ok (lsProg_320 H) (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveSpecOf doReserveStack A lim)) :=
    do_reserve_7_placed_ok h_panic hshim halloc hrealloc
  obtain ⟨P, hP, hwp⟩ := ekSentCt1ReceivedEncode2_gen_ok_prog (by decide) hfn2 A lim
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded_unchunked hencLen0))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 henc0)
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed s0 hcl0 hauth0)
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 hdoRes0)
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem ek_sent_ct1_received_encode_2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode2PlacedOkExt A lim H :=
  ekSentCt1ReceivedEncode_unpinned_of_pinned_placed
    (ek_sent_ct1_received_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem ek_sent_ct1_received_encode_2_pinned_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode2PinnedPlacedOkX A lim H := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  have hfn2 : IsEkEnc2PlacedProg (lsProg_318 H) (blkPl_318).base (blkPl_421).base
      (blkPl_292).base (lsmpl.base 314) (blkPl_320).base (lsρ lsMemcpySym) :=
    ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hencLen0 : subroutine_ok (lsProg_421 H) (blkPl_421).base
      (ekSentCt1ReceivedEncodedLenPinnedSpec A.repAlloc) :=
    ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_hooks A.repAlloc H
  have henc0 : subroutine_ok (lsProg_292 H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf doReserveStackX A lim)) :=
    encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc
  have hauth0 : subroutine_ok (lsProg_318 H) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf doReserveStackX A lim)) :=
    ls_subroutine_ok_of_block (auth_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)
  have hdoRes0 : subroutine_ok (lsProg_320 H) (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveSpecOf doReserveStackX A lim)) :=
    do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc
  obtain ⟨P, hP, hwp⟩ := ekSentCt1ReceivedEncode2_gen_ok_prog (by decide) hfn2 A lim
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded_unchunked hencLen0))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 henc0)
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed s0 hcl0 hauth0)
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 hdoRes0)
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem ek_sent_ct1_received_encode_2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode2PlacedOkX A lim H :=
  ekSentCt1ReceivedEncode_unpinned_of_pinned_placed
    (ek_sent_ct1_received_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

/-! ## 7. `EncodeToVec` (`Block 426`) Callee Bridges (`lsmpl.base 318`) -/

section EncodeToVecBridge

theorem unchunkedMsgEncodeStackOf_eq_etv_ek (resStack : Nat) :
    unchunkedMsgEncodeStackOf resStack = encodeToVecCalleeStackOf resStack := by
  dsimp [unchunkedMsgEncodeStackOf, authEncodeStackOf, encodeToVecCalleeStackOf]; omega

/-- Exact-capacity (`0`-allocation) `EncodeToVec` callee contract for
`encode<EkSentCt1Received>` (`s.sp = sp - 144#64`, `A.pool lim st` preserved unchanged). -/
def etvEkSentCt1ReceivedEncodeExactBudgetSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked4PBGhost V1State.Unchunked.EkSentCt1Received × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length +
        (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length ≤ x.cap.toNat⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr
        (x.bs ++ encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

theorem etv_ekSentCt1ReceivedEncode_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hek_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeExactBudgetSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  dsimp only [etvEkSentCt1ReceivedEncodeExactBudgetSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hfit⟩, hmem⟩ := hpre
  let xg : EkSentCt1ReceivedEncodePinnedGhost :=
    ⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩
  have hfit_xg : xg.bs.length + (encodeEkSentCt1ReceivedMsg xg.m).length ≤ xg.cap.toNat := hfit
  have hfits : FitsEnv M lim st
      (EkSentCt1ReceivedEncodeEnvS (ekSentCt1ReceivedPinnedToUnpinned xg)) :=
    fitsEnv_ekSentCt1ReceivedEncodeS_of_spare hfit_xg
  have hpre' : s.mem ⊨
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim)).pre
        (xg, st) s ∗ R := by
    dsimp only [withLsCodeLoaded, ekSentCt1ReceivedEncodePinnedSpecOfS,
      ekSentCt1ReceivedEncodePinnedSpecOfEnv, xg]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inl hfit_xg, hfits⟩, ?_⟩
    rwa [unchunkedMsgEncodeStackOf_eq_etv_ek]
  refine (hek_ok.to_outcome (xg, st) R s hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, ekSentCt1ReceivedEncodePinnedSpecOfS,
      ekSentCt1ReceivedEncodePinnedSpecOfEnv] at hq
    dsimp only [withLsCodeLoaded, etvEkSentCt1ReceivedEncodeExactBudgetSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨htrf, hq⟩ := hq
    refine ⟨htrf, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq
    rcases hq with ⟨evs, cap', ptr', hq⟩
    have hq' : sf.mem ⊨
        ⌜xg.cap.toNat ≤ cap'.toNat ∧
          (xg.bs.length + (encodeEkSentCt1ReceivedMsg xg.m).length ≤ xg.cap.toNat →
            cap' = xg.cap ∧ ptr' = xg.ptr)⌝ ∗
        (⌜EkSentCt1ReceivedEncodeEnvS (ekSentCt1ReceivedPinnedToUnpinned xg) evs⌝ ∗
          (ekSentCt1ReceivedPBPinnedAt A.repAlloc xg.g xg.msgA xg.m ∗
            vecU8At A.repAlloc xg.v cap' ptr' (xg.bs ++ encodeEkSentCt1ReceivedMsg xg.m) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp (unchunkedMsgEncodeStackOf resStack) ∗ R)) := by
      convert hq using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hq'
    obtain ⟨⟨_, hpres⟩, hev, hmem'⟩ := hq'
    obtain ⟨hcap_eq, hptr_eq⟩ := hpres hfit_xg
    have hevs_nil := ekSentCt1ReceivedEncodeEnvS_eq_nil_of_spare hfit_xg hev
    subst hevs_nil
    dsimp only [xg, encodeEkSentCt1ReceivedMsg] at hcap_eq hptr_eq hmem'
    subst hcap_eq hptr_eq
    simp only [AllocCostModel.stepEvents_nil] at hmem'
    rw [← unchunkedMsgEncodeStackOf_eq_etv_ek]
    convert hmem' using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem etv_ekSentCt1ReceivedEncode_exact_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeExactBudgetSpecOf doReserveStack A lim)) :=
  etv_ekSentCt1ReceivedEncode_exact_of_lscl
    (ls_subroutine_ok_of_block
      (ek_sent_ct1_received_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc))

theorem etv_ekSentCt1ReceivedEncode_exact_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeExactBudgetSpecOf doReserveStackX A lim)) :=
  etv_ekSentCt1ReceivedEncode_exact_of_lscl
    (ls_subroutine_ok_of_block
      (ek_sent_ct1_received_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc))

theorem etv_ekSentCt1ReceivedEncode_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOfS doReserveStack A lim)) :=
  ls_subroutine_ok_of_block
    (ek_sent_ct1_received_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem etv_ekSentCt1ReceivedEncode_pinned_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOfS doReserveStackX A lim)) :=
  ls_subroutine_ok_of_block
    (ek_sent_ct1_received_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

end EncodeToVecBridge

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget
