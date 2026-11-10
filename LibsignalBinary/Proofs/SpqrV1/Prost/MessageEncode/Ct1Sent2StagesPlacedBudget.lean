/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlacedAuxBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Stages 4–5 of `unchunked::Ct1Sent::encode [local#2]` (`Block 319`)

Re-exports Stages 1–3 from `Ct1Sent2StagesPlacedAuxBudget` and proves relocatable
`[LibsignalPlacement]` stage steppers on `lsProg_319` for Stage 4 (`hdr: Vec<u8>`) and Stage 5
(`es: Vec<u8>`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl lsρ lsMemcpySym
   blkPC_319 blkPl_292 blkPl_319 blkPl_319_ρ blkPl_320 blkPl_408 lsProg_319
   ls_resolve_blk_292 ls_resolve_blk_314 ls_resolve_blk_320 ls_resolve_blk_408)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB V1State)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost vecU8At_eq_header_sep_buf)
open CryptoVerification.SpqrV1.Varint
  (elem_len_after_reserve_not_ult elem_len_ult_spare_iff encodeVarint_length_bounds
   vecU8At_expose_slice vecU8At_pack_slice)
open CryptoVerification.SpqrV1.ProtoRepr
  (AuthenticatorPBGhost Unchunked5PBGhost authenticatorPBPinnedAt
   ct1SentPBEncodedLen ct1SentPBPinnedAt optAuthenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (cap_add_one_beq_zero_false cap_add_one_bne_zero_true
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ofNat_length_beq_zero_of_lt ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32)
open CryptoVerification.SpqrV1.Auth
  (authEncodeStackOf cap_toNat_eq_of_beq lt_cap_toNat_of_beq_false reserveCap_one_bounds
   sp_sub_64_aligned vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (UnchunkedEncodeCalleeSavedPlaced
   bs_append_bytesField3_of_ne_empty bs_append_bytesField4_of_ne_empty
   bs_append_bytesFieldTagged_of_empty bs_append_msgHeaderBytes
   bs_append_optAuthField2Bytes_none bs_append_optAuthField2Bytes_some
   bs_append_u64Field1Bytes_of_ne_zero bs_append_u64Field1Bytes_of_zero
   bytesField3_len_of_ne_empty bytesField4_len_of_ne_empty bytesFieldTagged
   msgHeaderBytes msgHeaderBytes_len_bounds optAuthField2Bytes
   stackAt_unchunkedMsgEncode u64Field1Bytes u64Field1Bytes_len_of_ne_zero
   unchunkedMsgEncodeStackOf vecU8At_expose_src_of_ne_nil_placed
   withUnchunkedEncodeCSPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents fitsEvents_append
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget (ct1SentEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (authEncodePinnedSpecOf sepWPp_extract_vecU8At_bounds)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep reserveStep_of_need_doReserveEvents reserveStep_of_spare
   reserveStep_one_eq_pushByteStep sepWP_done_tpidr_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget (u64Field1Step)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
  (CapAfter fitsEvents_optBytesReserve_of_fitsEnv fitsEvents_optBytesTag_of_fitsEnv
   hdrFieldEnv optAuthField2Env optBytesField1ByteTagEnv
   optBytesField1ByteTagEnv_of_empty optBytesField1ByteTagEnv_of_ne_empty
   u64Field1Env)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
  (step_ct1Sent_encoded_len_call_placed step_unchunked_auth_encode_call_placed
   step_unchunked_do_reserve7_call_placed step_unchunked_encode_varint_call_placed
   step_unchunked_memcpy_call_placed)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  blkPl_319_ρ ls_resolve_blk_408 ls_resolve_blk_292 ls_resolve_blk_314 ls_resolve_blk_320

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) :
    a + (b - a) = b := by bv_omega

@[local arm64_norm] private theorem bv_bl_reloc_target (base target k : BitVec 64) :
    base + k + (target - base - k) = target := by bv_omega

@[local arm64_norm] private theorem lsmpl_base_408 [LibsignalPlacement] :
    lsmpl.base 408 = (blkPl_408).base := rfl

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

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlacedAuxBudget
  (IsCt1Enc2PlacedProg doReserveOne_append_encodeVarintEvents_of_eq
   encodeVarintEvents_after_tag_of_lt step_ct1_auth_2_placed step_ct1_epoch_2_placed
   step_ct1_hdr_2_placed)

/-! ## 4. Stage 4: Field 3 — `hdr: Vec<u8>` -/

private theorem step_hdrf_from_236_2_placed [LibsignalPlacement]
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    (A : CryptoVerification.RustHeap.RustAlloc)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs_mid dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hle : bs_mid.length + dk.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 236#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length)
    (hx22 : s.readReg64 .x22 = dkPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm ((vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr (bs_mid ++ dk)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  have hdk_ne_nil : dk ≠ [] := List.isEmpty_eq_false_iff.mp hdk_ne
  have hdk_pos : 0 < dk.length := List.length_pos_of_ne_nil hdk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A msgA dkCap dkPtr dk ∗ F) (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA) (cap := dkCap) (ptr := dkPtr) (bs := dk)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by sep_ac_rfl) fun hdk_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid dk.length hle hcap_lt hptr_ne hdk_pos,
    vecU8At_expose_src_of_ne_nil_placed A msgA dkCap dkPtr dk hdk_ne_nil hdk_le]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := memcpy_pc)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        refine step_unchunked_memcpy_call_placed hmemcpy
          (curPtr + BitVec.ofNat 64 bs_mid.length) dkPtr sp ((blkPl_319).base + 256#64) dk
          (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
            A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗
            memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 dk.length)
              (curCap.toNat - bs_mid.length - dk.length) ∗
            (vecHeader msgA dkCap dkPtr (BitVec.ofNat 64 dk.length) ∗
              ⌜dkPtr ≠ 0 ∧ dk.length ≤ dkCap.toNat ∧ dkCap.toNat < 2 ^ 63⌝ ∗
              memRegion (dkPtr + BitVec.ofNat 64 dk.length) (dkCap.toNat - dk.length) ∗
              A.live dkPtr dkCap.toNat 1) ∗ F)
          an an an halign an an an an
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (cs_step hcs hinv1) (by sep_ac_rfl) ?_
        intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hvm_mc
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 dk.length := by
          rw [hcs01.2.2.1]; simp only [arm64_norm, *]
        have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length := by
          rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 264#64)
        by_vm_steps (
          wp_steps
          exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
            (fun hvm2 hinv2 =>
              SepWPp.weaken_pre
                (by rw [← vecU8At_pack_slice A v curCap curPtr bs_mid dk hle hcap_lt hptr_ne hdk_ne_nil,
                      vecU8At_expose_src_of_ne_nil_placed A msgA dkCap dkPtr dk hdk_ne_nil hdk_le]
                    exact Entails.of_eq (by sep_ac_rfl))
                (hnext _ an an an an an an (cs_step hcs1 hinv2) (hvm1.trans (hvm_mc.trans hvm2)))))))

private theorem step_hdrf_from_184_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 : State}
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8)) (st_tag : M.σ)
    (hdk_ne : dk.isEmpty = false) (hlt : bs3.length < curCap.toNat)
    (hfit : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat ∨
      bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62)
    (hfits_var : FitsEvents M lim st_tag
      (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x1a#8]))))
    (hfits_res : ∀ (cap_mid : BitVec 64),
      curCap.toNat ≤ cap_mid.toNat →
      (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat →
        cap_mid = curCap) →
      FitsEvents M lim
        (M.stepEvents
          (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x1a#8])))
          st_tag)
        ((reserveStep cap_mid.toNat
          (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 184#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs3.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length)
    (hx22 : s.readReg64 .x22 = dkPtr) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc msgA dkCap dkPtr dk ∗
      vecU8At A.repAlloc v curCap curPtr bs3 ∗ A.pool lim st_tag s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap_mid cap4 ptr4 : BitVec 64),
      sm.pc = entry + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap_mid.toNat →
      (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat →
        cap_mid = curCap) →
      cap_mid.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat →
        cap4 = curCap ∧ ptr4 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc msgA dkCap dkPtr dk ∗
          vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ bytesFieldTagged 3#32 dk) ∗
          A.pool lim
            (M.stepEvents
              ((reserveStep cap_mid.toNat
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2)
              (M.stepEvents
                (encodeVarintEvents
                  (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x1a#8])))
                st_tag))
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hstep236 := step_hdrf_from_236_2_placed A.repAlloc hfn hmemcpy
  subst hP
  have hdk_len := bytesField3_len_of_ne_empty hdk_ne
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs3 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        have hvarint_fit :
            (bs3 ++ [0x1a#8]).length +
              (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat ∨
            (bs3 ++ [0x1a#8]).length + 10 < 2 ^ 62 := by
          rw [List.length_append, List.length_singleton]
          rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
        refine step_unchunked_encode_varint_call_placed hres A lim henc
          (BitVec.ofNat 64 dk.length) v curCap curPtr sp ((blkPl_319).base + 216#64)
          (bs3 ++ [0x1a#8]) st_tag hvarint_fit hfits_var
          (F := vecU8At A.repAlloc msgA dkCap dkPtr dk ∗ F)
          an an an halign an an an an (cs_step hcs hinv1)
          (by rw [← A.pool_of_vmPreserved hvm1,
                ← vecU8At_close_one A.repAlloc v curCap curPtr bs3 0x1a#8 hlt]; try sep_ac_rfl) ?_
        intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
        let bs_mid := (bs3 ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 dk.length)
        let st_mid := M.stepEvents
          (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x1a#8])))
          st_tag
        have hbs_mid_len :
            bs_mid.length + dk.length = bs3.length + (bytesFieldTagged 3#32 dk).length := by
          dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hdk_len]; omega
        have hcap_mid_pres :
            bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat →
            cap_mid = curCap := by
          intro h; apply (hpres_mid ?_).1; rw [List.length_append, List.length_singleton]; exact h
        have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
        have hx20_2 : s2.readReg64 .x20 = msgA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
        have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dk.length := by
          rw [hcs12.2.2.1]; simp only [arm64_norm, *]
        have hx22_2 : s2.readReg64 .x22 = dkPtr := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
        refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap_mid)
          (ptr := ptr_mid) (bs := bs_mid)
          (F := A.pool lim st_mid s2 ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
            vecU8At A.repAlloc msgA dkCap dkPtr dk ∗ F)
          (by dsimp [bs_mid, st_mid]; try sep_ac_rfl) fun hle_mid hcap_mid_lt _ => ?_
        rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_mid ptr_mid bs_mid, vecHeader]
        have hdk_lt63 : dk.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
        by_cases hneed : cap_mid.toNat < bs_mid.length + dk.length
        · have hfit_dk : bs_mid.length + dk.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
          have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = true :=
            (elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mpr hneed
          obtain ⟨hnot_ult, hle_res, hge_res, hbound_dk⟩ := elem_len_after_reserve_not_ult hfit_dk hneed
          have hneed' : ¬ (bs_mid.length + dk.length ≤ cap_mid.toNat) := by omega
          have hev_res : doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid dk.length) =
              (reserveStep cap_mid.toNat
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2 := by
            have h1 := congrArg Prod.snd
              (reserveStep_of_need_doReserveEvents v cap_mid ptr_mid bs_mid dk.length hneed')
            dsimp only at h1
            have hbs_eq : bs_mid.length = bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← h1, hbs_eq]
          have hfits_res_call : FitsEvents M lim st_mid
              (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid dk.length)) := by
            rw [hev_res]; exact hfits_res cap_mid hge_mid hcap_mid_pres
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_320).base)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 => by
                refine step_unchunked_do_reserve7_call_placed hres A lim hdoReserve v cap_mid ptr_mid sp
                  ((blkPl_319).base + 616#64) bs_mid dk.length st_mid hbound_dk hfits_res_call
                  (F := vecU8At A.repAlloc msgA dkCap dkPtr dk ∗ F)
                  an an an halign an an an
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  an an (cs_step hcs2 hinv2)
                  (by rw [← A.pool_of_vmPreserved hvm2]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
                intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
                let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length dk.length)
                change (BitVec.ofNat 64 dk.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
                have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
                have hx20_3 : s3.readReg64 .x20 = msgA := by rw [hcs23.2.1]; simp only [arm64_norm, *]
                have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 dk.length := by
                  rw [hcs23.2.2.1]; simp only [arm64_norm, *]
                have hx22_3 : s3.readReg64 .x22 = dkPtr := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
                rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_res ptr_res bs_mid, vecHeader]
                apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 236#64)
                by_vm_steps (
                  wp_steps
                  exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                    (fun hvm3 hinv3 =>
                      hstep236 msgA v cap_res ptr_res dkCap dkPtr sp bs_mid dk hdk_ne hle_res
                        (F := A.pool lim
                            (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid dk.length)) st_mid) s3 ∗
                          stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
                        an an an halign an an an an an an (cs_step hcs3 hinv3)
                        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                        (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm hvm236 =>
                          SepWPp.weaken_pre
                            (by dsimp [bs_mid, st_mid]
                                rw [← A.pool_of_vmPreserved (hvm3.trans hvm236), hev_res,
                                  bs_append_bytesField3_of_ne_empty hdk_ne bs3]
                                exact Entails.of_eq (by sep_ac_rfl))
                            (hnext sm cap_mid cap_res ptr_res hpcm hrunm hspm htrm hx19m hx20m hcsm
                              hge_mid hcap_mid_pres hge_res (fun h => absurd h (by omega))))))))
        · have hle_fast : bs_mid.length + dk.length ≤ cap_mid.toNat := by omega
          have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = false :=
            Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mp h)
          have hpres_all : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat →
              cap_mid = curCap ∧ ptr_mid = curPtr := by
            intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
          have hev_res_nil :
              (reserveStep cap_mid.toNat
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2 = [] := by
            have hbs_eq : bs_mid.length = bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← hbs_eq, reserveStep_of_spare hle_fast]
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 236#64)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 =>
                hstep236 msgA v cap_mid ptr_mid dkCap dkPtr sp bs_mid dk hdk_ne hle_fast
                  (F := A.pool lim st_mid s2 ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
                  an an an halign an an an an an an (cs_step hcs2 hinv2)
                  (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                  (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm hvm236 =>
                    SepWPp.weaken_pre
                      (by dsimp [bs_mid, st_mid]
                          rw [← A.pool_of_vmPreserved (hvm2.trans hvm236), hev_res_nil, M.stepEvents_nil,
                            bs_append_bytesField3_of_ne_empty hdk_ne bs3]
                          exact Entails.of_eq (by sep_ac_rfl))
                      (hnext sm cap_mid cap_mid ptr_mid hpcm hrunm hspm htrm hx19m hx20m hcsm
                        hge_mid hcap_mid_pres (Nat.le_refl _) hpres_all))))))

theorem step_ct1_hdrf_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 s : State}
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v cap3 ptr3 dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8)) (curSt : M.σ)
    (hfit : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ cap3.toNat ∨
      bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (optBytesField1ByteTagEnv cap3 bs3.length dk))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 156#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc msgA dkCap dkPtr dk ∗
      vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64) (evs₄ : List AllocEvent),
      sm.pc = entry + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap3.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 3#32 dk).length ≤ cap3.toNat →
        cap4 = cap3 ∧ ptr4 = ptr3) →
      optBytesField1ByteTagEnv cap3 bs3.length dk evs₄ →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc msgA dkCap dkPtr dk ∗
          vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ bytesFieldTagged 3#32 dk) ∗
          A.pool lim (M.stepEvents evs₄ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hstep184 := step_hdrf_from_184_2_placed hres A lim hfn henc hdoReserve hmemcpy
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := msgA) (cap := dkCap)
    (ptr := dkPtr) (bs := dk)
    (F := vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hdk_le hdk_cap_lt _ => ?_
  have ⟨hdk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := dk) (by omega)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases hdk : dk.isEmpty
  · have hdk_len := bytesField3_len_of_ne_empty hdk
    have hfits_tag := fitsEvents_optBytesTag_of_fitsEnv hdk hfits
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap3)
      (ptr := ptr3) (bs := bs3)
      (F := vecU8At A.repAlloc msgA dkCap dkPtr dk ∗ A.pool lim curSt s ∗
        stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun hcap3_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap3 ptr3 bs3, vecHeader,
      vecU8At_eq_header_sep_buf A.repAlloc msgA dkCap dkPtr dk, vecHeader]
    by_cases hcap3 : cap3 == BitVec.ofNat 64 bs3.length
    · have hcap_eq : cap3.toNat = bs3.length :=
        cap_toNat_eq_of_beq hcap3 (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hfit2 : bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      have hres_lt64 : reserveCap cap3.toNat bs3.length 1 < 2 ^ 64 := by omega
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_320).base)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 => by
            have hfits_res1 : FitsEvents M lim curSt
                (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) := by
              have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
                (BitVec.ofNat 64 dk.length) v cap3 ptr3 0#64 bs3 0x1a#8 hcap_eq hres_lt64
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).1
            refine step_unchunked_do_reserve7_call_placed hres A lim hdoReserve v cap3 ptr3 sp
              ((blkPl_319).base + 584#64) bs3 1 curSt hbound1 hfits_res1
              (F := vecU8At A.repAlloc msgA dkCap dkPtr dk ∗ F)
              an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
              an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]
                  simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
            intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
            let newCap1 := BitVec.ofNat 64 (reserveCap cap3.toNat bs3.length 1)
            have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
              (BitVec.ofNat 64 dk.length) v cap3 ptr3 newPtr1 bs3 0x1a#8 hcap_eq hres_lt64
            have hfits_var : FitsEvents M lim
                (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) curSt)
                (encodeVarintEvents
                  (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v newCap1 newPtr1 (bs3 ++ [0x1a#8]))) := by
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).2
            have hfits_res2 : ∀ (cap_mid : BitVec 64),
                newCap1.toNat ≤ cap_mid.toNat →
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ newCap1.toNat →
                  cap_mid = newCap1) →
                FitsEvents M lim
                  (M.stepEvents
                    (encodeVarintEvents
                      (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v newCap1 newPtr1 (bs3 ++ [0x1a#8])))
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) curSt))
                  ((reserveStep cap_mid.toNat
                    (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2) := by
              intro cap_mid hge_m _
              rw [← M.stepEvents_append, hev_eq]
              exact fitsEvents_optBytesReserve_of_fitsEnv hdk hfits
                ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩
            have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
            rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs3, vecHeader]
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 184#64)
            by_vm_steps (
              wp_steps
              exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                (fun hvm1 hinv1 =>
                  hstep184 msgA v newCap1 newPtr1 dkCap dkPtr sp bs3 dk
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) curSt)
                    hdk hlt1 (Or.inr hfit2) hfits_var hfits_res2 (F := F)
                    an an an halign an an an
                    (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
                    (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
                    (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
                    (cs_step hcs1 hinv1)
                    (by rw [← A.pool_of_vmPreserved hvm1]
                        simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                    (fun sm cap_mid cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge_m _ hge4 _ =>
                      SepWPp.weaken_pre
                        (by rw [← M.stepEvents_append, ← M.stepEvents_append, ← List.append_assoc]; dsimp only [newCap1]; rw [hev_eq]
                            exact Entails.of_eq (by sep_ac_rfl))
                        (hnext sm cap4 ptr4 _ hpcm hrunm hspm htrm hx19m hx20m hcsm
                          (Nat.le_trans hge1 (Nat.le_trans hge_m hge4))
                          (fun h => absurd h (by omega))
                          (optBytesField1ByteTagEnv_of_ne_empty hdk
                            ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩)))))))
    · have hcap3_f : (cap3 == BitVec.ofNat 64 bs3.length) = false := Bool.eq_false_iff.mpr hcap3
      have hlt3 : bs3.length < cap3.toNat :=
        lt_cap_toNat_of_beq_false hcap3_f hcap3_le (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hev_eq := encodeVarintEvents_after_tag_of_lt
        (BitVec.ofNat 64 dk.length) v cap3 ptr3 bs3 0x1a#8 hlt3
      have hfits_var : FitsEvents M lim curSt
          (encodeVarintEvents
            (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v cap3 ptr3 (bs3 ++ [0x1a#8]))) := by
        rwa [hev_eq]
      have hfits_res2 : ∀ (cap_mid : BitVec 64),
          cap3.toNat ≤ cap_mid.toNat →
          (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ cap3.toNat →
            cap_mid = cap3) →
          FitsEvents M lim
            (M.stepEvents
              (encodeVarintEvents
                (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v cap3 ptr3 (bs3 ++ [0x1a#8])))
              curSt)
            ((reserveStep cap_mid.toNat
              (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2) := by
        intro cap_mid hge_m hpres_m
        rw [hev_eq]
        exact fitsEvents_optBytesReserve_of_fitsEnv hdk hfits
          ⟨hge_m, fun h => hpres_m (by omega)⟩
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 184#64)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 =>
            hstep184 msgA v cap3 ptr3 dkCap dkPtr sp bs3 dk curSt hdk hlt3 hfit
              hfits_var hfits_res2 (F := F)
              an an an halign an an an an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]
                  simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
              (fun sm cap_mid cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge_m hpres_m hge4 hpres4 =>
                SepWPp.weaken_pre
                  (by rw [hev_eq, ← M.stepEvents_append]; exact Entails.of_eq (by sep_ac_rfl))
                  (hnext sm cap4 ptr4 _ hpcm hrunm hspm htrm hx19m hx20m hcsm
                    (Nat.le_trans hge_m hge4) hpres4
                    (optBytesField1ByteTagEnv_of_ne_empty hdk
                      ⟨hge_m, fun h => hpres_m (by omega)⟩)))))
  · rw [vecU8At_eq_header_sep_buf A.repAlloc msgA dkCap dkPtr dk, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 264#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 =>
          SepWPp.weaken_pre
            (by rw [← A.pool_of_vmPreserved hvm0, ← M.stepEvents_nil curSt,
                  ← bs_append_bytesFieldTagged_of_empty 3#32 hdk bs3,
                  vecU8At_eq_header_sep_buf A.repAlloc msgA dkCap dkPtr dk, vecHeader]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ cap3 ptr3 [] an an an an an an (cs_step hcs hinv0)
              (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (optBytesField1ByteTagEnv_of_empty hdk))))

/-! ## 5. Stage 5: Field 4 — `es: Vec<u8>` -/

private theorem step_es_from_344_2_placed [LibsignalPlacement]
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    (A : CryptoVerification.RustHeap.RustAlloc)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs_mid dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hle : bs_mid.length + dk.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 344#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length)
    (hx22 : s.readReg64 .x22 = dkPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm
        ((vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v curCap curPtr (bs_mid ++ dk)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  have hdk_ne_nil : dk ≠ [] := List.isEmpty_eq_false_iff.mp hdk_ne
  have hdk_pos : 0 < dk.length := List.length_pos_of_ne_nil hdk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ F) (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x18#64) (cap := dkCap) (ptr := dkPtr) (bs := dk)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by sep_ac_rfl) fun hdk_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid dk.length hle hcap_lt hptr_ne hdk_pos,
    vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) dkCap dkPtr dk hdk_ne_nil hdk_le]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := memcpy_pc)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        refine step_unchunked_memcpy_call_placed hmemcpy
          (curPtr + BitVec.ofNat 64 bs_mid.length) dkPtr sp ((blkPl_319).base + 364#64) dk
          (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
            A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗
            memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 dk.length)
              (curCap.toNat - bs_mid.length - dk.length) ∗
            (vecHeader (msgA + 0x18#64) dkCap dkPtr (BitVec.ofNat 64 dk.length) ∗
              ⌜dkPtr ≠ 0 ∧ dk.length ≤ dkCap.toNat ∧ dkCap.toNat < 2 ^ 63⌝ ∗
              memRegion (dkPtr + BitVec.ofNat 64 dk.length) (dkCap.toNat - dk.length) ∗
              A.live dkPtr dkCap.toNat 1) ∗ F)
          an an an halign an an an an
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (cs_step hcs hinv1) (by sep_ac_rfl) ?_
        intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hvm_mc
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 dk.length := by
          rw [hcs01.2.2.1]; simp only [arm64_norm, *]
        have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length := by
          rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 372#64)
        by_vm_steps (
          wp_steps
          exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
            (fun hvm2 hinv2 =>
              SepWPp.weaken_pre
                (by rw [← vecU8At_pack_slice A v curCap curPtr bs_mid dk hle hcap_lt hptr_ne hdk_ne_nil,
                      vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) dkCap dkPtr dk hdk_ne_nil hdk_le]
                    exact Entails.of_eq (by sep_ac_rfl))
                (hnext _ an an an an an an (cs_step hcs1 hinv2) (hvm1.trans (hvm_mc.trans hvm2)))))))

private theorem step_es_from_292_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 : State}
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8)) (st_tag : M.σ)
    (hdk_ne : dk.isEmpty = false) (hlt : bs3.length < curCap.toNat)
    (hfit : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat ∨
      bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62)
    (hfits_var : FitsEvents M lim st_tag
      (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x22#8]))))
    (hfits_res : ∀ (cap_mid : BitVec 64),
      curCap.toNat ≤ cap_mid.toNat →
      (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat →
        cap_mid = curCap) →
      FitsEvents M lim
        (M.stepEvents
          (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x22#8])))
          st_tag)
        ((reserveStep cap_mid.toNat
          (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 292#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs3.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length)
    (hx22 : s.readReg64 .x22 = dkPtr) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗
      vecU8At A.repAlloc v curCap curPtr bs3 ∗ A.pool lim st_tag s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap_mid cap4 ptr4 : BitVec 64),
      sm.pc = entry + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap_mid.toNat →
      (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat →
        cap_mid = curCap) →
      cap_mid.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat →
        cap4 = curCap ∧ ptr4 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗
          vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ bytesFieldTagged 4#32 dk) ∗
          A.pool lim
            (M.stepEvents
              ((reserveStep cap_mid.toNat
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2)
              (M.stepEvents
                (encodeVarintEvents
                  (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x22#8])))
                st_tag))
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hstep344 := step_es_from_344_2_placed A.repAlloc hfn hmemcpy
  subst hP
  have hdk_len := bytesField4_len_of_ne_empty hdk_ne
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs3 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        have hvarint_fit :
            (bs3 ++ [0x22#8]).length +
              (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat ∨
            (bs3 ++ [0x22#8]).length + 10 < 2 ^ 62 := by
          rw [List.length_append, List.length_singleton]
          rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
        refine step_unchunked_encode_varint_call_placed hres A lim henc
          (BitVec.ofNat 64 dk.length) v curCap curPtr sp ((blkPl_319).base + 324#64)
          (bs3 ++ [0x22#8]) st_tag hvarint_fit hfits_var
          (F := vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
          an an an halign an an an an (cs_step hcs hinv1)
          (by rw [← A.pool_of_vmPreserved hvm1,
                ← vecU8At_close_one A.repAlloc v curCap curPtr bs3 0x22#8 hlt]; try sep_ac_rfl) ?_
        intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
        let bs_mid := (bs3 ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 dk.length)
        let st_mid := M.stepEvents
          (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x22#8])))
          st_tag
        have hbs_mid_len :
            bs_mid.length + dk.length = bs3.length + (bytesFieldTagged 4#32 dk).length := by
          dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hdk_len]; omega
        have hcap_mid_pres :
            bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat →
            cap_mid = curCap := by
          intro h; apply (hpres_mid ?_).1; rw [List.length_append, List.length_singleton]; exact h
        have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
        have hx20_2 : s2.readReg64 .x20 = msgA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
        have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dk.length := by
          rw [hcs12.2.2.1]; simp only [arm64_norm, *]
        have hx22_2 : s2.readReg64 .x22 = dkPtr := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
        refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap_mid)
          (ptr := ptr_mid) (bs := bs_mid)
          (F := A.pool lim st_mid s2 ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
            vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
          (by dsimp [bs_mid, st_mid]; try sep_ac_rfl) fun hle_mid hcap_mid_lt _ => ?_
        rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_mid ptr_mid bs_mid, vecHeader]
        have hdk_lt63 : dk.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
        by_cases hneed : cap_mid.toNat < bs_mid.length + dk.length
        · have hfit_dk : bs_mid.length + dk.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
          have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = true :=
            (elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mpr hneed
          obtain ⟨hnot_ult, hle_res, hge_res, hbound_dk⟩ := elem_len_after_reserve_not_ult hfit_dk hneed
          have hneed' : ¬ (bs_mid.length + dk.length ≤ cap_mid.toNat) := by omega
          have hev_res : doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid dk.length) =
              (reserveStep cap_mid.toNat
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2 := by
            have h1 := congrArg Prod.snd
              (reserveStep_of_need_doReserveEvents v cap_mid ptr_mid bs_mid dk.length hneed')
            dsimp only at h1
            have hbs_eq : bs_mid.length = bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← h1, hbs_eq]
          have hfits_res_call : FitsEvents M lim st_mid
              (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid dk.length)) := by
            rw [hev_res]; exact hfits_res cap_mid hge_mid hcap_mid_pres
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_320).base)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 => by
                refine step_unchunked_do_reserve7_call_placed hres A lim hdoReserve v cap_mid ptr_mid sp
                  ((blkPl_319).base + 720#64) bs_mid dk.length st_mid hbound_dk hfits_res_call
                  (F := vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
                  an an an halign an an an
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  an an (cs_step hcs2 hinv2)
                  (by rw [← A.pool_of_vmPreserved hvm2]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
                intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
                let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length dk.length)
                change (BitVec.ofNat 64 dk.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
                have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
                have hx20_3 : s3.readReg64 .x20 = msgA := by rw [hcs23.2.1]; simp only [arm64_norm, *]
                have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 dk.length := by
                  rw [hcs23.2.2.1]; simp only [arm64_norm, *]
                have hx22_3 : s3.readReg64 .x22 = dkPtr := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
                rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_res ptr_res bs_mid, vecHeader]
                apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 344#64)
                by_vm_steps (
                  wp_steps
                  exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                    (fun hvm3 hinv3 =>
                      hstep344 msgA v cap_res ptr_res dkCap dkPtr sp bs_mid dk hdk_ne hle_res
                        (F := A.pool lim
                            (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid dk.length)) st_mid) s3 ∗
                          stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
                        an an an halign an an an an an an (cs_step hcs3 hinv3)
                        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                        (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm hvm344 =>
                          SepWPp.weaken_pre
                            (by dsimp [bs_mid, st_mid]
                                rw [← A.pool_of_vmPreserved (hvm3.trans hvm344), hev_res,
                                  bs_append_bytesField4_of_ne_empty hdk_ne bs3]
                                exact Entails.of_eq (by sep_ac_rfl))
                            (hnext sm cap_mid cap_res ptr_res hpcm hrunm hspm htrm hx19m hx20m hcsm
                              hge_mid hcap_mid_pres hge_res (fun h => absurd h (by omega))))))))
        · have hle_fast : bs_mid.length + dk.length ≤ cap_mid.toNat := by omega
          have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = false :=
            Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mp h)
          have hpres_all : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat →
              cap_mid = curCap ∧ ptr_mid = curPtr := by
            intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
          have hev_res_nil :
              (reserveStep cap_mid.toNat
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2 = [] := by
            have hbs_eq : bs_mid.length = bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← hbs_eq, reserveStep_of_spare hle_fast]
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 344#64)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 =>
                hstep344 msgA v cap_mid ptr_mid dkCap dkPtr sp bs_mid dk hdk_ne hle_fast
                  (F := A.pool lim st_mid s2 ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
                  an an an halign an an an an an an (cs_step hcs2 hinv2)
                  (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                  (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm hvm344 =>
                    SepWPp.weaken_pre
                      (by dsimp [bs_mid, st_mid]
                          rw [← A.pool_of_vmPreserved (hvm2.trans hvm344), hev_res_nil, M.stepEvents_nil,
                            bs_append_bytesField4_of_ne_empty hdk_ne bs3]
                          exact Entails.of_eq (by sep_ac_rfl))
                      (hnext sm cap_mid cap_mid ptr_mid hpcm hrunm hspm htrm hx19m hx20m hcsm
                        hge_mid hcap_mid_pres (Nat.le_refl _) hpres_all))))))

theorem step_ct1_es_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 s : State}
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionBudgetSpec)
    (msgA v cap3 ptr3 dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8)) (curSt : M.σ)
    (hfit : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ cap3.toNat ∨
      bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (optBytesField1ByteTagEnv cap3 bs3.length dk))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 264#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗
      vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64) (evs₄ : List AllocEvent),
      sm.pc = entry + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap3.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 4#32 dk).length ≤ cap3.toNat →
        cap4 = cap3 ∧ ptr4 = ptr3) →
      optBytesField1ByteTagEnv cap3 bs3.length dk evs₄ →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗
          vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ bytesFieldTagged 4#32 dk) ∗
          A.pool lim (M.stepEvents evs₄ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hstep292 := step_es_from_292_2_placed hres A lim hfn henc hdoReserve hmemcpy
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := msgA + 0x18#64) (cap := dkCap)
    (ptr := dkPtr) (bs := dk)
    (F := vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hdk_le hdk_cap_lt _ => ?_
  have ⟨hdk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := dk) (by omega)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases hdk : dk.isEmpty
  · have hdk_len := bytesField4_len_of_ne_empty hdk
    have hfits_tag := fitsEvents_optBytesTag_of_fitsEnv hdk hfits
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap3)
      (ptr := ptr3) (bs := bs3)
      (F := vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ A.pool lim curSt s ∗
        stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun hcap3_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap3 ptr3 bs3, vecHeader,
      vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk, vecHeader]
    by_cases hcap3 : cap3 == BitVec.ofNat 64 bs3.length
    · have hcap_eq : cap3.toNat = bs3.length :=
        cap_toNat_eq_of_beq hcap3 (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hfit2 : bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      have hres_lt64 : reserveCap cap3.toNat bs3.length 1 < 2 ^ 64 := by omega
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_320).base)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 => by
            have hfits_res1 : FitsEvents M lim curSt
                (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) := by
              have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
                (BitVec.ofNat 64 dk.length) v cap3 ptr3 0#64 bs3 0x22#8 hcap_eq hres_lt64
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).1
            refine step_unchunked_do_reserve7_call_placed hres A lim hdoReserve v cap3 ptr3 sp
              ((blkPl_319).base + 688#64) bs3 1 curSt hbound1 hfits_res1
              (F := vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
              an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
              an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]
                  simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
            intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
            let newCap1 := BitVec.ofNat 64 (reserveCap cap3.toNat bs3.length 1)
            have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
              (BitVec.ofNat 64 dk.length) v cap3 ptr3 newPtr1 bs3 0x22#8 hcap_eq hres_lt64
            have hfits_var : FitsEvents M lim
                (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) curSt)
                (encodeVarintEvents
                  (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v newCap1 newPtr1 (bs3 ++ [0x22#8]))) := by
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).2
            have hfits_res2 : ∀ (cap_mid : BitVec 64),
                newCap1.toNat ≤ cap_mid.toNat →
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ newCap1.toNat →
                  cap_mid = newCap1) →
                FitsEvents M lim
                  (M.stepEvents
                    (encodeVarintEvents
                      (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v newCap1 newPtr1 (bs3 ++ [0x22#8])))
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) curSt))
                  ((reserveStep cap_mid.toNat
                    (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2) := by
              intro cap_mid hge_m _
              rw [← M.stepEvents_append, hev_eq]
              exact fitsEvents_optBytesReserve_of_fitsEnv hdk hfits
                ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩
            have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
            rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs3, vecHeader]
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 292#64)
            by_vm_steps (
              wp_steps
              exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                (fun hvm1 hinv1 =>
                  hstep292 msgA v newCap1 newPtr1 dkCap dkPtr sp bs3 dk
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) curSt)
                    hdk hlt1 (Or.inr hfit2) hfits_var hfits_res2 (F := F)
                    an an an halign an an an
                    (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
                    (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
                    (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
                    (cs_step hcs1 hinv1)
                    (by rw [← A.pool_of_vmPreserved hvm1]
                        simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                    (fun sm cap_mid cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge_m _ hge4 _ =>
                      SepWPp.weaken_pre
                        (by rw [← M.stepEvents_append, ← M.stepEvents_append, ← List.append_assoc]; dsimp only [newCap1]; rw [hev_eq]
                            exact Entails.of_eq (by sep_ac_rfl))
                        (hnext sm cap4 ptr4 _ hpcm hrunm hspm htrm hx19m hx20m hcsm
                          (Nat.le_trans hge1 (Nat.le_trans hge_m hge4))
                          (fun h => absurd h (by omega))
                          (optBytesField1ByteTagEnv_of_ne_empty hdk
                            ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩)))))))
    · have hcap3_f : (cap3 == BitVec.ofNat 64 bs3.length) = false := Bool.eq_false_iff.mpr hcap3
      have hlt3 : bs3.length < cap3.toNat :=
        lt_cap_toNat_of_beq_false hcap3_f hcap3_le (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hev_eq := encodeVarintEvents_after_tag_of_lt
        (BitVec.ofNat 64 dk.length) v cap3 ptr3 bs3 0x22#8 hlt3
      have hfits_var : FitsEvents M lim curSt
          (encodeVarintEvents
            (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v cap3 ptr3 (bs3 ++ [0x22#8]))) := by
        rwa [hev_eq]
      have hfits_res2 : ∀ (cap_mid : BitVec 64),
          cap3.toNat ≤ cap_mid.toNat →
          (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ cap3.toNat →
            cap_mid = cap3) →
          FitsEvents M lim
            (M.stepEvents
              (encodeVarintEvents
                (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v cap3 ptr3 (bs3 ++ [0x22#8])))
              curSt)
            ((reserveStep cap_mid.toNat
              (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2) := by
        intro cap_mid hge_m hpres_m
        rw [hev_eq]
        exact fitsEvents_optBytesReserve_of_fitsEnv hdk hfits
          ⟨hge_m, fun h => hpres_m (by omega)⟩
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 292#64)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 =>
            hstep292 msgA v cap3 ptr3 dkCap dkPtr sp bs3 dk curSt hdk hlt3 hfit
              hfits_var hfits_res2 (F := F)
              an an an halign an an an an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]
                  simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
              (fun sm cap_mid cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge_m hpres_m hge4 hpres4 =>
                SepWPp.weaken_pre
                  (by rw [hev_eq, ← M.stepEvents_append]; exact Entails.of_eq (by sep_ac_rfl))
                  (hnext sm cap4 ptr4 _ hpcm hrunm hspm htrm hx19m hx20m hcsm
                    (Nat.le_trans hge_m hge4) hpres4
                    (optBytesField1ByteTagEnv_of_ne_empty hdk
                      ⟨hge_m, fun h => hpres_m (by omega)⟩)))))
  · rw [vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 372#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 =>
          SepWPp.weaken_pre
            (by rw [← A.pool_of_vmPreserved hvm0, ← M.stepEvents_nil curSt,
                  ← bs_append_bytesFieldTagged_of_empty 4#32 hdk bs3,
                  vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk, vecHeader]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ cap3 ptr3 [] an an an an an an (cs_step hcs hinv0)
              (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (optBytesField1ByteTagEnv_of_empty hdk))))

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlacedBudget
