/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1PlacedAuxBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.ReprPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Stages 5–7 and Core Proof of `encode<Ct1Sent> [local#3]` (Block `459`)

Proves budget-threaded `SepWPp` lemmas for Stages 5–6 (`es`, `ct1`), the epilogue, and
`ct1SentEncode1_gen_placed_ok` on CLI Block `459` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1PlacedBudget

export LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1PlacedAuxBudget
  (step_ct1_hdr_1_placed step_ct1_epoch_1_placed step_ct1_auth_1_placed step_ct1_hdrf_1_placed)

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsMemcpySym lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost StepInv vecU8At_eq_header_sep_buf)
open CryptoVerification.SpqrV1.Varint
  (elem_len_after_reserve_not_ult elem_len_ult_spare_iff vecU8At_expose_slice vecU8At_pack_slice)
open CryptoVerification.SpqrV1.ProtoRepr
  (ct1SentPBEncodedLen ct1SentPBPinnedAt optAuthenticatorPBPinnedAt unchunked5PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ofNat_length_beq_zero_of_lt ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32)
open CryptoVerification.SpqrV1.Auth
  (authEncodeStackOf cap_toNat_eq_of_beq lt_cap_toNat_of_beq_false reserveCap_one_bounds
   sp_sub_64_aligned vecU8At_bounds_of_satisfies vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (Ct1SentEncodePinnedGhost UnchunkedEncodeCalleeSavedPlaced
   bs0_append_encodeCt1SentMsg bs_append_bytesField4_of_ne_empty
   bs_append_bytesField5_of_ne_empty bs_append_bytesFieldTagged_of_empty
   bytesField4_len_of_ne_empty bytesField5_len_of_ne_empty bytesFieldTagged
   ct1SentPBEncodedLen_eq_fields_len encodeCt1SentMsg encodeCt1SentMsg_len_split
   msgHeaderBytes msgHeaderBytes_len_bounds optAuthField2Bytes
   stackAt_unchunkedMsgEncode u64Field1Bytes unchunkedMsgEncodeStackOf
   vecU8At_expose_src_of_ne_nil_placed withUnchunkedEncodeCSPlaced)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed
  (blkPl_459 blkPl_459_ρ lsProg_459)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents fitsEvents_append
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget (ct1SentEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (authEncodePinnedSpecOf sepWPp_extract_vecU8At_bounds)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep reserveStep_of_need_doReserveEvents reserveStep_of_spare
   sepWP_done_tpidr_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (ct1SentEncodePinnedSpecOfEnv ct1SentPinnedToUnpinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
  (CapAfter Ct1SentEncodeEnvS FitsEnv.stageSeq_left FitsEnv.stageSeq_right
   StageSeqEnv StageSeqEnv.intro StageSeqEnv.nonempty ct1SentEncodePinnedSpecOfS
   fitsEvents_optBytesReserve_of_fitsEnv fitsEvents_optBytesTag_of_fitsEnv
   hdrFieldEnv optAuthField2Env optAuthField2Env_nonempty
   optBytesField1ByteTagEnv optBytesField1ByteTagEnv_nonempty
   optBytesField1ByteTagEnv_of_empty optBytesField1ByteTagEnv_of_ne_empty
   u64Field1Env u64Field1Env_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
  (step_unchunked_do_reserve2_call_placed step_unchunked_encode_varint_call_placed
   step_unchunked_memcpy_call_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1PlacedAuxBudget
  (doReserveOne_append_encodeVarintEvents_of_eq encodeVarintEvents_after_tag_of_lt)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  blkPl_459_ρ

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) :
    a + (b - a) = b := by bv_omega

@[local arm64_norm] private theorem bv_bl_target_norm (base off target : BitVec 64) :
    (base + off) + (target - base - off) = target := by bv_omega

@[local arm64_norm] private theorem bv_bl_entry_norm (base target : BitVec 64) :
    base + (target - base - 0#64) = target := by bv_omega

@[local arm64_norm] private theorem lsmpl_rho_memcpy [LibsignalPlacement] :
    lsmpl.ρ "memcpy" = lsρ lsMemcpySym := rfl

local macro "an" : term => `(by simp only [arm64_norm, *])
local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(UnchunkedEncodeCalleeSavedPlaced.step $hcs (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) $hinv)

/-! ## 5. Stage 5: Field 4 — `es: Vec<u8>` -/

private theorem step_ct1_es_from_344_1_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_459 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs_mid dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hle : bs_mid.length + dk.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_459).base + 344#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length) (hx22 : s.readReg64 .x22 = dkPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_459).base + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_459 H) ret sm
        ((vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v curCap curPtr (bs_mid ++ dk)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_459 H) ret s P Q Qp oom := by
  subst hP
  have hdk_ne_nil : dk ≠ [] := List.isEmpty_eq_false_iff.mp hdk_ne
  have hdk_pos : 0 < dk.length := List.length_pos_of_ne_nil hdk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ F) (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x18#64) (cap := dkCap) (ptr := dkPtr) (bs := dk)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by sep_ac_rfl) fun hdk_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid dk.length hle hcap_lt hptr_ne hdk_pos,
    vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) dkCap dkPtr dk hdk_ne_nil hdk_le]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsρ lsMemcpySym)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        refine step_unchunked_memcpy_call_placed hmemcpy
          (curPtr + BitVec.ofNat 64 bs_mid.length) dkPtr sp ((blkPl_459).base + 364#64) dk
          (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
            A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗
            memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 dk.length)
              (curCap.toNat - bs_mid.length - dk.length) ∗
            (vecHeader (msgA + 0x18#64) dkCap dkPtr (BitVec.ofNat 64 dk.length) ∗
              ⌜dkPtr ≠ 0 ∧ dk.length ≤ dkCap.toNat ∧ dkCap.toNat < 2 ^ 63⌝ ∗
              memRegion (dkPtr + BitVec.ofNat 64 dk.length) (dkCap.toNat - dk.length) ∗
              A.live dkPtr dkCap.toNat 1) ∗ F)
          an an an halign an an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (cs_step hcs hinv1) (by sep_ac_rfl) ?_
        intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hvm_mc
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
        have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length := by rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 372#64)
        by_vm_steps (
          wp_steps
          exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
            (fun hvm2 hinv2 =>
              SepWPp.weaken_pre
                (by rw [← vecU8At_pack_slice A v curCap curPtr bs_mid dk hle hcap_lt hptr_ne hdk_ne_nil,
                      vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) dkCap dkPtr dk hdk_ne_nil hdk_le]
                    exact Entails.of_eq (by sep_ac_rfl))
                (hnext _ an an an an an an (cs_step hcs1 hinv2) (hvm1.trans (hvm_mc.trans hvm2)))))))

private theorem step_ct1_es_from_292_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_459 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_459 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_459 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8)) (st_tag : M.σ)
    (hdk_ne : dk.isEmpty = false) (hlt : bs3.length < curCap.toNat)
    (hfit : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat ∨
      bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62)
    (hfits_var : FitsEvents M lim st_tag
      (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x22#8]))))
    (hfits_res : ∀ (cap_mid : BitVec 64),
      curCap.toNat ≤ cap_mid.toNat →
      (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat → cap_mid = curCap) →
      FitsEvents M lim
        (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x22#8]))) st_tag)
        ((reserveStep cap_mid.toNat (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_459).base + 292#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs3.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length) (hx22 : s.readReg64 .x22 = dkPtr)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗
      vecU8At A.repAlloc v curCap curPtr bs3 ∗ A.pool lim st_tag s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap_mid cap4 ptr4 : BitVec 64),
      sm.pc = (blkPl_459).base + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap_mid.toNat →
      (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat → cap_mid = curCap) →
      cap_mid.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat → cap4 = curCap ∧ ptr4 = curPtr) →
      SepWPp (lsProg_459 H) ret sm
        ((vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗
          vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ bytesFieldTagged 4#32 dk) ∗
          A.pool lim
            (M.stepEvents
              ((reserveStep cap_mid.toNat (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2)
              (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x22#8]))) st_tag))
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_459 H) ret s P Q Qp oom := by
  have hstep344 := step_ct1_es_from_344_1_placed A.repAlloc H hmemcpy
  subst hP; have hdk_len := bytesField4_len_of_ne_empty hdk_ne
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs3 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 451)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        have hvarint_fit : (bs3 ++ [0x22#8]).length + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat ∨
            (bs3 ++ [0x22#8]).length + 10 < 2 ^ 62 := by
          rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
        refine step_unchunked_encode_varint_call_placed hres A lim henc
          (BitVec.ofNat 64 dk.length) v curCap curPtr sp ((blkPl_459).base + 324#64)
          (bs3 ++ [0x22#8]) st_tag hvarint_fit hfits_var
          (F := vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
          an an an halign an an an an (cs_step hcs hinv1)
          (by rw [← A.pool_of_vmPreserved hvm1, ← vecU8At_close_one A.repAlloc v curCap curPtr bs3 0x22#8 hlt]; try sep_ac_rfl) ?_
        intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
        let bs_mid := (bs3 ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 dk.length)
        let st_mid := M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v curCap curPtr (bs3 ++ [0x22#8]))) st_tag
        have hbs_mid_len : bs_mid.length + dk.length = bs3.length + (bytesFieldTagged 4#32 dk).length := by
          dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hdk_len]; omega
        have hcap_mid_pres : bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat → cap_mid = curCap := by
          intro h; apply (hpres_mid ?_).1; rw [List.length_append, List.length_singleton]; exact h
        have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
        have hx20_2 : s2.readReg64 .x20 = msgA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
        have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
        have hx22_2 : s2.readReg64 .x22 = dkPtr := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
        refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap_mid) (ptr := ptr_mid) (bs := bs_mid)
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
              (reserveStep cap_mid.toNat (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2 := by
            have h1 := congrArg Prod.snd (reserveStep_of_need_doReserveEvents v cap_mid ptr_mid bs_mid dk.length hneed')
            dsimp only at h1
            have hbs_eq : bs_mid.length = bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← h1, hbs_eq]
          have hfits_res_call : FitsEvents M lim st_mid (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid dk.length)) := by
            rw [hev_res]; exact hfits_res cap_mid hge_mid hcap_mid_pres
          apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 => by
                refine step_unchunked_do_reserve2_call_placed hres A lim hdoReserve v cap_mid ptr_mid sp
                  ((blkPl_459).base + 664#64) bs_mid dk.length st_mid hbound_dk hfits_res_call
                  (F := vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
                  an an an halign an an an
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  (cs_step hcs2 hinv2)
                  (by rw [← A.pool_of_vmPreserved hvm2]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
                intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
                let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length dk.length)
                change (BitVec.ofNat 64 dk.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
                have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
                have hx20_3 : s3.readReg64 .x20 = msgA := by rw [hcs23.2.1]; simp only [arm64_norm, *]
                have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
                have hx22_3 : s3.readReg64 .x22 = dkPtr := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
                rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_res ptr_res bs_mid, vecHeader]
                apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 344#64)
                by_vm_steps (
                  wp_steps
                  exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                    (fun hvm3 hinv3 =>
                      hstep344 msgA v cap_res ptr_res dkCap dkPtr sp bs_mid dk hdk_ne hle_res
                        (F := A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid dk.length)) st_mid) s3 ∗
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
          have hpres_all : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat → cap_mid = curCap ∧ ptr_mid = curPtr := by
            intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
          have hev_res_nil :
              (reserveStep cap_mid.toNat (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2 = [] := by
            have hbs_eq : bs_mid.length = bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← hbs_eq, reserveStep_of_spare hle_fast]
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 344#64)
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

theorem step_ct1_es_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_459 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_459 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_459 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (msgA v cap3 ptr3 dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8)) (curSt : M.σ)
    (hfit : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ cap3.toNat ∨
      bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (optBytesField1ByteTagEnv cap3 bs3.length dk))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_459).base + 264#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗
      vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64) (evs₅ : List AllocEvent),
      sm.pc = (blkPl_459).base + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap3.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 4#32 dk).length ≤ cap3.toNat → cap4 = cap3 ∧ ptr4 = ptr3) →
      optBytesField1ByteTagEnv cap3 bs3.length dk evs₅ →
      SepWPp (lsProg_459 H) ret sm
        ((vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗
          vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ bytesFieldTagged 4#32 dk) ∗
          A.pool lim (M.stepEvents evs₅ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_459 H) ret s P Q Qp oom := by
  have hstep292 := step_ct1_es_from_292_1_placed hres A lim H henc hdoReserve hmemcpy
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := msgA + 0x18#64) (cap := dkCap) (ptr := dkPtr) (bs := dk)
    (F := vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hdk_le hdk_cap_lt _ => ?_
  have ⟨hdk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := dk) (by omega)
  cases hdk : dk.isEmpty
  · have hdk_len := bytesField4_len_of_ne_empty hdk
    have hfits_tag := fitsEvents_optBytesTag_of_fitsEnv hdk hfits
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap3) (ptr := ptr3) (bs := bs3)
      (F := vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ A.pool lim curSt s ∗
        stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun hcap3_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap3 ptr3 bs3, vecHeader,
      vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk, vecHeader]
    by_cases hcap3 : cap3 == BitVec.ofNat 64 bs3.length
    · have hcap_eq : cap3.toNat = bs3.length :=
        cap_toNat_eq_of_beq hcap3 (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hfit2 : bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      have hres_lt64 : reserveCap cap3.toNat bs3.length 1 < 2 ^ 64 := by omega
      apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 => by
            have hfits_res1 : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) := by
              have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
                (BitVec.ofNat 64 dk.length) v cap3 ptr3 0#64 bs3 0x22#8 hcap_eq hres_lt64
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).1
            refine step_unchunked_do_reserve2_call_placed hres A lim hdoReserve v cap3 ptr3 sp
              ((blkPl_459).base + 640#64) bs3 1 curSt hbound1 hfits_res1
              (F := vecU8At A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
              an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
              (by simp only [arm64_norm]) (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
            intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
            let newCap1 := BitVec.ofNat 64 (reserveCap cap3.toNat bs3.length 1)
            have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
              (BitVec.ofNat 64 dk.length) v cap3 ptr3 newPtr1 bs3 0x22#8 hcap_eq hres_lt64
            have hfits_var : FitsEvents M lim
                (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) curSt)
                (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v newCap1 newPtr1 (bs3 ++ [0x22#8]))) := by
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).2
            have hfits_res2 : ∀ (cap_mid : BitVec 64),
                newCap1.toNat ≤ cap_mid.toNat →
                (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ newCap1.toNat → cap_mid = newCap1) →
                FitsEvents M lim
                  (M.stepEvents
                    (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v newCap1 newPtr1 (bs3 ++ [0x22#8])))
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) curSt))
                  ((reserveStep cap_mid.toNat (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2) := by
              intro cap_mid hge_m _
              rw [← M.stepEvents_append, hev_eq]
              exact fitsEvents_optBytesReserve_of_fitsEnv hdk hfits ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩
            have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
            rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs3, vecHeader]
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 292#64)
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
                    (by rw [← A.pool_of_vmPreserved hvm1]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                    (fun sm cap_mid cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge_m _ hge4 _ =>
                      SepWPp.weaken_pre
                        (by rw [← M.stepEvents_append, ← M.stepEvents_append, ← List.append_assoc]; dsimp only [newCap1]; rw [hev_eq]
                            exact Entails.of_eq (by sep_ac_rfl))
                        (hnext sm cap4 ptr4 _ hpcm hrunm hspm htrm hx19m hx20m hcsm
                          (Nat.le_trans hge1 (Nat.le_trans hge_m hge4))
                          (fun h => absurd h (by omega))
                          (optBytesField1ByteTagEnv_of_ne_empty hdk ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩)))))))
    · have hcap3_f : (cap3 == BitVec.ofNat 64 bs3.length) = false := Bool.eq_false_iff.mpr hcap3
      have hlt3 : bs3.length < cap3.toNat :=
        lt_cap_toNat_of_beq_false hcap3_f hcap3_le (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hev_eq := encodeVarintEvents_after_tag_of_lt (BitVec.ofNat 64 dk.length) v cap3 ptr3 bs3 0x22#8 hlt3
      have hfits_var : FitsEvents M lim curSt
          (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v cap3 ptr3 (bs3 ++ [0x22#8]))) := by
        rwa [hev_eq]
      have hfits_res2 : ∀ (cap_mid : BitVec 64),
          cap3.toNat ≤ cap_mid.toNat →
          (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ cap3.toNat → cap_mid = cap3) →
          FitsEvents M lim
            (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 dk.length) v cap3 ptr3 (bs3 ++ [0x22#8]))) curSt)
            ((reserveStep cap_mid.toNat (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length) dk.length).2) := by
        intro cap_mid hge_m hpres_m
        rw [hev_eq]; exact fitsEvents_optBytesReserve_of_fitsEnv hdk hfits ⟨hge_m, fun h => hpres_m (by omega)⟩
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 292#64)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 =>
            hstep292 msgA v cap3 ptr3 dkCap dkPtr sp bs3 dk curSt hdk hlt3 hfit hfits_var hfits_res2 (F := F)
              an an an halign an an an an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
              (fun sm cap_mid cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge_m hpres_m hge4 hpres4 =>
                SepWPp.weaken_pre
                  (by rw [hev_eq, ← M.stepEvents_append]; exact Entails.of_eq (by sep_ac_rfl))
                  (hnext sm cap4 ptr4 _ hpcm hrunm hspm htrm hx19m hx20m hcsm
                    (Nat.le_trans hge_m hge4) hpres4
                    (optBytesField1ByteTagEnv_of_ne_empty hdk ⟨hge_m, fun h => hpres_m (by omega)⟩)))))
  · rw [vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x18#64) dkCap dkPtr dk, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 372#64)
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

/-! ## 6. Stage 6: Field 5 — `ct1: Vec<u8>` -/

private theorem step_ct1_ct1f_from_452_1_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_459 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr ct1Cap ct1Ptr sp : BitVec 64) (bs_mid ct1 : List (BitVec 8))
    (hct1_ne : ct1.isEmpty = false) (hle : bs_mid.length + ct1.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_459).base + 452#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ct1Ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs_mid.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_459).base + 480#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_459 H) ret sm
        ((vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr (bs_mid ++ ct1)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_459 H) ret s P Q Qp oom := by
  subst hP
  have hct1_ne_nil : ct1 ≠ [] := List.isEmpty_eq_false_iff.mp hct1_ne
  have hct1_pos : 0 < ct1.length := List.length_pos_of_ne_nil hct1_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F) (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x30#64) (cap := ct1Cap) (ptr := ct1Ptr) (bs := ct1)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by sep_ac_rfl) fun hct1_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid ct1.length hle hcap_lt hptr_ne hct1_pos,
    vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 hct1_ne_nil hct1_le]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsρ lsMemcpySym)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        refine step_unchunked_memcpy_call_placed hmemcpy
          (curPtr + BitVec.ofNat 64 bs_mid.length) ct1Ptr sp ((blkPl_459).base + 472#64) ct1
          (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
            A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗
            memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 ct1.length)
              (curCap.toNat - bs_mid.length - ct1.length) ∗
            (vecHeader (msgA + 0x30#64) ct1Cap ct1Ptr (BitVec.ofNat 64 ct1.length) ∗
              ⌜ct1Ptr ≠ 0 ∧ ct1.length ≤ ct1Cap.toNat ∧ ct1Cap.toNat < 2 ^ 63⌝ ∗
              memRegion (ct1Ptr + BitVec.ofNat 64 ct1.length) (ct1Cap.toNat - ct1.length) ∗
              A.live ct1Ptr ct1Cap.toNat 1) ∗ F)
          an an an halign an an an an
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (cs_step hcs hinv1) (by sep_ac_rfl) ?_
        intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hvm_mc
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
        have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs_mid.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 480#64)
        by_vm_steps (
          wp_steps
          exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
            (fun hvm2 hinv2 =>
              SepWPp.weaken_pre
                (by rw [← vecU8At_pack_slice A v curCap curPtr bs_mid ct1 hle hcap_lt hptr_ne hct1_ne_nil,
                      vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 hct1_ne_nil hct1_le]
                    exact Entails.of_eq (by sep_ac_rfl))
                (hnext _ an an an an (cs_step hcs1 hinv2) (hvm1.trans (hvm_mc.trans hvm2)))))))

private theorem step_ct1_ct1f_from_400_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_459 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_459 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_459 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr ct1Cap ct1Ptr sp : BitVec 64) (bs4 ct1 : List (BitVec 8)) (st_tag : M.σ)
    (hct1_ne : ct1.isEmpty = false) (hlt : bs4.length < curCap.toNat)
    (hfit : bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ curCap.toNat ∨
      bs4.length + (bytesFieldTagged 5#32 ct1).length + 10 < 2 ^ 62)
    (hfits_var : FitsEvents M lim st_tag
      (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v curCap curPtr (bs4 ++ [0x2a#8]))))
    (hfits_res : ∀ (cap_mid : BitVec 64),
      curCap.toNat ≤ cap_mid.toNat →
      (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat → cap_mid = curCap) →
      FitsEvents M lim
        (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v curCap curPtr (bs4 ++ [0x2a#8]))) st_tag)
        ((reserveStep cap_mid.toNat (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_459).base + 400#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs4.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ct1Ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗
      vecU8At A.repAlloc v curCap curPtr bs4 ∗ A.pool lim st_tag s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap_mid cap5 ptr5 : BitVec 64),
      sm.pc = (blkPl_459).base + 480#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap_mid.toNat →
      (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat → cap_mid = curCap) →
      cap_mid.toNat ≤ cap5.toNat →
      (bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ curCap.toNat → cap5 = curCap ∧ ptr5 = curPtr) →
      SepWPp (lsProg_459 H) ret sm
        ((vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗
          vecU8At A.repAlloc v cap5 ptr5 (bs4 ++ bytesFieldTagged 5#32 ct1) ∗
          A.pool lim
            (M.stepEvents
              ((reserveStep cap_mid.toNat (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2)
              (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v curCap curPtr (bs4 ++ [0x2a#8]))) st_tag))
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_459 H) ret s P Q Qp oom := by
  have hstep452 := step_ct1_ct1f_from_452_1_placed A.repAlloc H hmemcpy
  subst hP; have hct1_len := bytesField5_len_of_ne_empty hct1_ne
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs4 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 451)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        have hvarint_fit : (bs4 ++ [0x2a#8]).length + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat ∨
            (bs4 ++ [0x2a#8]).length + 10 < 2 ^ 62 := by
          rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
        refine step_unchunked_encode_varint_call_placed hres A lim henc
          (BitVec.ofNat 64 ct1.length) v curCap curPtr sp ((blkPl_459).base + 432#64)
          (bs4 ++ [0x2a#8]) st_tag hvarint_fit hfits_var
          (F := vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F)
          an an an halign an an an an (cs_step hcs hinv1)
          (by rw [← A.pool_of_vmPreserved hvm1, ← vecU8At_close_one A.repAlloc v curCap curPtr bs4 0x2a#8 hlt]; try sep_ac_rfl) ?_
        intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
        let bs_mid := (bs4 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 ct1.length)
        let st_mid := M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v curCap curPtr (bs4 ++ [0x2a#8]))) st_tag
        have hbs_mid_len : bs_mid.length + ct1.length = bs4.length + (bytesFieldTagged 5#32 ct1).length := by
          dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hct1_len]; omega
        have hcap_mid_pres : bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat → cap_mid = curCap := by
          intro h; apply (hpres_mid ?_).1; rw [List.length_append, List.length_singleton]; exact h
        have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
        have hx20_2 : s2.readReg64 .x20 = ct1Ptr := by rw [hcs12.2.1]; simp only [arm64_norm, *]
        have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
        refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap_mid) (ptr := ptr_mid) (bs := bs_mid)
          (F := A.pool lim st_mid s2 ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
            vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F)
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
              (reserveStep cap_mid.toNat (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2 := by
            have h1 := congrArg Prod.snd (reserveStep_of_need_doReserveEvents v cap_mid ptr_mid bs_mid ct1.length hneed')
            dsimp only at h1
            have hbs_eq : bs_mid.length = bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← h1, hbs_eq]
          have hfits_res_call : FitsEvents M lim st_mid (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid ct1.length)) := by
            rw [hev_res]; exact hfits_res cap_mid hge_mid hcap_mid_pres
          apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 => by
                refine step_unchunked_do_reserve2_call_placed hres A lim hdoReserve v cap_mid ptr_mid sp
                  ((blkPl_459).base + 744#64) bs_mid ct1.length st_mid hbound_ct1 hfits_res_call
                  (F := vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F)
                  an an an halign an an an
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
                  (cs_step hcs2 hinv2)
                  (by rw [← A.pool_of_vmPreserved hvm2]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
                intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
                let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length ct1.length)
                change (BitVec.ofNat 64 ct1.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
                have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
                have hx20_3 : s3.readReg64 .x20 = ct1Ptr := by rw [hcs23.2.1]; simp only [arm64_norm, *]
                have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
                rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_res ptr_res bs_mid, vecHeader]
                apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 452#64)
                by_vm_steps (
                  wp_steps
                  exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                    (fun hvm3 hinv3 =>
                      hstep452 msgA v cap_res ptr_res ct1Cap ct1Ptr sp bs_mid ct1 hct1_ne hle_res
                        (F := A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap_mid ptr_mid bs_mid ct1.length)) st_mid) s3 ∗
                          stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
                        an an an halign an an an an an (cs_step hcs3 hinv3)
                        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                        (fun sm hpcm hrunm hspm htrm hcsm hvm452 =>
                          SepWPp.weaken_pre
                            (by dsimp [bs_mid, st_mid]
                                rw [← A.pool_of_vmPreserved (hvm3.trans hvm452), hev_res,
                                  bs_append_bytesField5_of_ne_empty hct1_ne bs4]
                                exact Entails.of_eq (by sep_ac_rfl))
                            (hnext sm cap_mid cap_res ptr_res hpcm hrunm hspm htrm hcsm
                              hge_mid hcap_mid_pres hge_res (fun h => absurd h (by omega))))))))
        · have hle_fast : bs_mid.length + ct1.length ≤ cap_mid.toNat := by omega
          have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 ct1.length) = false :=
            Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hct1_lt63).mp h)
          have hpres_all : bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ curCap.toNat → cap_mid = curCap ∧ ptr_mid = curPtr := by
            intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
          have hev_res_nil :
              (reserveStep cap_mid.toNat (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2 = [] := by
            have hbs_eq : bs_mid.length = bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length := by
              dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton]
            rw [← hbs_eq, reserveStep_of_spare hle_fast]
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 452#64)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 =>
                hstep452 msgA v cap_mid ptr_mid ct1Cap ct1Ptr sp bs_mid ct1 hct1_ne hle_fast
                  (F := A.pool lim st_mid s2 ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
                  an an an halign an an an an an (cs_step hcs2 hinv2)
                  (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                  (fun sm hpcm hrunm hspm htrm hcsm hvm452 =>
                    SepWPp.weaken_pre
                      (by dsimp [bs_mid, st_mid]
                          rw [← A.pool_of_vmPreserved (hvm2.trans hvm452), hev_res_nil, M.stepEvents_nil,
                            bs_append_bytesField5_of_ne_empty hct1_ne bs4]
                          exact Entails.of_eq (by sep_ac_rfl))
                      (hnext sm cap_mid cap_mid ptr_mid hpcm hrunm hspm htrm hcsm
                        hge_mid hcap_mid_pres (Nat.le_refl _) hpres_all))))))

theorem step_ct1_ct1f_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_459 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_459 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_459 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (msgA v cap4 ptr4 ct1Cap ct1Ptr sp : BitVec 64) (bs4 ct1 : List (BitVec 8)) (curSt : M.σ)
    (hfit : bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ cap4.toNat ∨
      bs4.length + (bytesFieldTagged 5#32 ct1).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (optBytesField1ByteTagEnv cap4 bs4.length ct1))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_459).base + 372#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗
      vecU8At A.repAlloc v cap4 ptr4 bs4 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64) (evs₆ : List AllocEvent),
      sm.pc = (blkPl_459).base + 480#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap4.toNat ≤ cap5.toNat →
      (bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ cap4.toNat → cap5 = cap4 ∧ ptr5 = ptr4) →
      optBytesField1ByteTagEnv cap4 bs4.length ct1 evs₆ →
      SepWPp (lsProg_459 H) ret sm
        ((vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗
          vecU8At A.repAlloc v cap5 ptr5 (bs4 ++ bytesFieldTagged 5#32 ct1) ∗
          A.pool lim (M.stepEvents evs₆ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_459 H) ret s P Q Qp oom := by
  have hstep400 := step_ct1_ct1f_from_400_1_placed hres A lim H henc hdoReserve hmemcpy
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := msgA + 0x30#64) (cap := ct1Cap) (ptr := ct1Ptr) (bs := ct1)
    (F := vecU8At A.repAlloc v cap4 ptr4 bs4 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hct1_le hct1_cap_lt _ => ?_
  have ⟨hct1_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := ct1) (by omega)
  cases hct1 : ct1.isEmpty
  · have hct1_len := bytesField5_len_of_ne_empty hct1
    have hfits_tag := fitsEvents_optBytesTag_of_fitsEnv hct1 hfits
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap4) (ptr := ptr4) (bs := bs4)
      (F := vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ A.pool lim curSt s ∗
        stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun hcap4_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap4 ptr4 bs4, vecHeader,
      vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1, vecHeader]
    by_cases hcap4 : cap4 == BitVec.ofNat 64 bs4.length
    · have hcap_eq : cap4.toNat = bs4.length :=
        cap_toNat_eq_of_beq hcap4 (Nat.lt_of_le_of_lt hcap4_le (BitVec.isLt cap4))
      have hfit2 : bs4.length + (bytesFieldTagged 5#32 ct1).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      have hres_lt64 : reserveCap cap4.toNat bs4.length 1 < 2 ^ 64 := by omega
      apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 => by
            have hfits_res1 : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bs4 1)) := by
              have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
                (BitVec.ofNat 64 ct1.length) v cap4 ptr4 0#64 bs4 0x2a#8 hcap_eq hres_lt64
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).1
            refine step_unchunked_do_reserve2_call_placed hres A lim hdoReserve v cap4 ptr4 sp
              ((blkPl_459).base + 720#64) bs4 1 curSt hbound1 hfits_res1
              (F := vecU8At A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F)
              an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
              (by simp only [arm64_norm]) (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
            intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
            let newCap1 := BitVec.ofNat 64 (reserveCap cap4.toNat bs4.length 1)
            have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
              (BitVec.ofNat 64 ct1.length) v cap4 ptr4 newPtr1 bs4 0x2a#8 hcap_eq hres_lt64
            have hfits_var : FitsEvents M lim
                (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bs4 1)) curSt)
                (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v newCap1 newPtr1 (bs4 ++ [0x2a#8]))) := by
              rw [← hev_eq] at hfits_tag
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_tag).2
            have hfits_res2 : ∀ (cap_mid : BitVec 64),
                newCap1.toNat ≤ cap_mid.toNat →
                (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ newCap1.toNat → cap_mid = newCap1) →
                FitsEvents M lim
                  (M.stepEvents
                    (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v newCap1 newPtr1 (bs4 ++ [0x2a#8])))
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bs4 1)) curSt))
                  ((reserveStep cap_mid.toNat (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2) := by
              intro cap_mid hge_m _
              rw [← M.stepEvents_append, hev_eq]
              exact fitsEvents_optBytesReserve_of_fitsEnv hct1 hfits ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩
            have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
            rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs4, vecHeader]
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 400#64)
            by_vm_steps (
              wp_steps
              exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                (fun hvm1 hinv1 =>
                  hstep400 msgA v newCap1 newPtr1 ct1Cap ct1Ptr sp bs4 ct1
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bs4 1)) curSt)
                    hct1 hlt1 (Or.inr hfit2) hfits_var hfits_res2 (F := F)
                    an an an halign an an an
                    (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
                    (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
                    (cs_step hcs1 hinv1)
                    (by rw [← A.pool_of_vmPreserved hvm1]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                    (fun sm cap_mid cap5 ptr5 hpcm hrunm hspm htrm hcsm hge_m _ hge5 _ =>
                      SepWPp.weaken_pre
                        (by rw [← M.stepEvents_append, ← M.stepEvents_append, ← List.append_assoc]; dsimp only [newCap1]; rw [hev_eq]
                            exact Entails.of_eq (by sep_ac_rfl))
                        (hnext sm cap5 ptr5 _ hpcm hrunm hspm htrm hcsm
                          (Nat.le_trans hge1 (Nat.le_trans hge_m hge5))
                          (fun h => absurd h (by omega))
                          (optBytesField1ByteTagEnv_of_ne_empty hct1 ⟨Nat.le_trans hge1 hge_m, fun h => absurd h (by omega)⟩)))))))
    · have hcap4_f : (cap4 == BitVec.ofNat 64 bs4.length) = false := Bool.eq_false_iff.mpr hcap4
      have hlt4 : bs4.length < cap4.toNat :=
        lt_cap_toNat_of_beq_false hcap4_f hcap4_le (Nat.lt_of_le_of_lt hcap4_le (BitVec.isLt cap4))
      have hev_eq := encodeVarintEvents_after_tag_of_lt (BitVec.ofNat 64 ct1.length) v cap4 ptr4 bs4 0x2a#8 hlt4
      have hfits_var : FitsEvents M lim curSt
          (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v cap4 ptr4 (bs4 ++ [0x2a#8]))) := by
        rwa [hev_eq]
      have hfits_res2 : ∀ (cap_mid : BitVec 64),
          cap4.toNat ≤ cap_mid.toNat →
          (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ cap4.toNat → cap_mid = cap4) →
          FitsEvents M lim
            (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 ct1.length) v cap4 ptr4 (bs4 ++ [0x2a#8]))) curSt)
            ((reserveStep cap_mid.toNat (bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 ct1.length)).length) ct1.length).2) := by
        intro cap_mid hge_m hpres_m
        rw [hev_eq]; exact fitsEvents_optBytesReserve_of_fitsEnv hct1 hfits ⟨hge_m, fun h => hpres_m (by omega)⟩
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 400#64)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 =>
            hstep400 msgA v cap4 ptr4 ct1Cap ct1Ptr sp bs4 ct1 curSt hct1 hlt4 hfit hfits_var hfits_res2 (F := F)
              an an an halign an an an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0]; simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
              (fun sm cap_mid cap5 ptr5 hpcm hrunm hspm htrm hcsm hge_m hpres_m hge5 hpres5 =>
                SepWPp.weaken_pre
                  (by rw [hev_eq, ← M.stepEvents_append]; exact Entails.of_eq (by sep_ac_rfl))
                  (hnext sm cap5 ptr5 _ hpcm hrunm hspm htrm hcsm
                    (Nat.le_trans hge_m hge5) hpres5
                    (optBytesField1ByteTagEnv_of_ne_empty hct1 ⟨hge_m, fun h => hpres_m (by omega)⟩)))))
  · rw [vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_459).base + 480#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 =>
          SepWPp.weaken_pre
            (by rw [← A.pool_of_vmPreserved hvm0, ← M.stepEvents_nil curSt,
                  ← bs_append_bytesFieldTagged_of_empty 5#32 hct1 bs4,
                  vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x30#64) ct1Cap ct1Ptr ct1, vecHeader]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ cap4 ptr4 [] an an an an (cs_step hcs hinv0)
              (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (optBytesField1ByteTagEnv_of_empty hct1))))

/-! ## 7. Epilogue & General `SepWPp` Theorem for Block `459` -/

theorem step_ct1_epilogue_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (H : String → Option (State → State))
    (sp sv3 : BitVec 64) {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_459).base + 480#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp →
      sf.trace = s0.trace → CalleeSavedPreserved s0 sf → StepInv s0 sf → VmPreserved s sf →
      Q sf (stackAt sp (unchunkedMsgEncodeStackOf resStack) ∗ F)) :
    SepWPp (lsProg_459 H) (s0.readReg64 .lr) s P Q Qp oom := by
  subst hP
  have hsp_aligned := sp_sub_64_aligned halign
  apply sepWPp_of_sepWP_cs_vm_placed (mid := s0.readReg64 .lr)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm hinv => by
        have hcs' := cs_step hcs hinv
        refine SepWPp.weaken_pre ?_ (SepWPp.done an an (hnext _ an an an an
          ⟨an, an, an, an, an, hcs'.1, hcs'.2.1, hcs'.2.2.1, hcs'.2.2.2.1, hcs'.2.2.2.2.1, an, hcs'.2.2.2.2.2.1⟩
          hcs'.2.2.2.2.2.2.1 hvm))
        rw [stackAt_unchunkedMsgEncode hres sp]; refine sepConj_mono_left (sepConj_mono_right ?_)
        exact Entails.sepExists_right (s0.readReg64 .fp) (Entails.sepExists_right (s0.readReg64 .lr)
          (Entails.sepExists_right (s0.readReg64 .x23) (Entails.sepExists_right sv3
            (Entails.sepExists_right (s0.readReg64 .x22) (Entails.sepExists_right (s0.readReg64 .x21)
              (Entails.sepExists_right (s0.readReg64 .x20) (Entails.sepExists_right (s0.readReg64 .x19)
                (Entails.refl _))))))))))

/-- General budget-threaded `SepWPp` correctness for `Cli/SpqrV1` `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1SentEncode1_gen_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : Ct1SentEncodePinnedGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (lsProg_459 H) (lsmpl.base 487)
      (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A.repAlloc)))
    (henc : subroutine_ok (lsProg_459 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hauth : subroutine_ok (lsProg_459 H) (lsmpl.base 454)
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_459 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_459 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hpc : s0.pc = (blkPl_459).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (ct1SentEncodePinnedSpecOfS resStack A lim).pre (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true)
    {Qp : State → SepProp → Prop} {oom : State → SepProp} :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp (lsProg_459 H) (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) →
          (s'.mem ⊨ (ct1SentEncodePinnedSpecOfS resStack A lim).post (x, st) s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      Qp oom := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre
  dsimp only [ct1SentEncodePinnedSpecOfS, ct1SentEncodePinnedSpecOfEnv, ct1SentPinnedToUnpinned] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hfit, hfits⟩, hpre_mem⟩ := hpre_pure
  obtain ⟨hcap_le, hcap_lt, _⟩ :=
    vecU8At_bounds_of_satisfies (A := A.repAlloc) (v := x.v) (cap := x.cap) (ptr := x.ptr) (bs := x.bs)
      (F := ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗ A.pool lim st s0 ∗
        stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; sep_ac_rfl)
  have hpre_rewritten : s0.mem ⊨ ((ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s0 ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)) ∗ emp) ∗ R := by
    rw [sepConj_emp]; convert hpre_mem using 1
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodeCt1SentMsg_len_split x.m
  have hhdr_bds := msgHeaderBytes_len_bounds (ct1SentPBEncodedLen x.m)
  have hlen_eq_fields := ct1SentPBEncodedLen_eq_fields_len x.m
  have hlen_fit : ct1SentPBEncodedLen x.m < 2 ^ 64 := by rcases hfit with h | h <;> omega
  let innerLen := ct1SentPBEncodedLen x.m
  let l0 := x.bs.length
  let a1 := (msgHeaderBytes innerLen).length
  let l1 := l0 + a1
  let a2 := (u64Field1Bytes x.m.epoch).length
  let l2 := l1 + a2
  let a3 := (optAuthField2Bytes x.m.auth).length
  let l3 := l2 + a3
  let a4 := (bytesFieldTagged 3#32 x.m.hdr).length
  let l4 := l3 + a4
  let a5 := (bytesFieldTagged 4#32 x.m.es).length
  let l5 := l4 + a5
  have hK5 : ∀ c5, ∃ e, optBytesField1ByteTagEnv c5 l5 x.m.ct1 e :=
    fun c5 => optBytesField1ByteTagEnv_nonempty c5 l5 x.m.ct1
  have hK4 : ∀ c4, ∃ e, StageSeqEnv c4 l4 a5 (optBytesField1ByteTagEnv c4 l4 x.m.es)
      (fun c5 => optBytesField1ByteTagEnv c5 l5 x.m.ct1) e :=
    fun c4 => StageSeqEnv.nonempty (optBytesField1ByteTagEnv_nonempty c4 l4 x.m.es) (hK5 c4)
  have hK3 : ∀ c3, ∃ e, StageSeqEnv c3 l3 a4 (optBytesField1ByteTagEnv c3 l3 x.m.hdr)
      (fun c4 => StageSeqEnv c4 l4 a5 (optBytesField1ByteTagEnv c4 l4 x.m.es)
        (fun c5 => optBytesField1ByteTagEnv c5 l5 x.m.ct1)) e :=
    fun c3 => StageSeqEnv.nonempty (optBytesField1ByteTagEnv_nonempty c3 l3 x.m.hdr) (hK4 c3)
  have hK2 : ∀ c2, ∃ e, StageSeqEnv c2 l2 a3 (optAuthField2Env c2 l2 x.m.auth)
      (fun c3 => StageSeqEnv c3 l3 a4 (optBytesField1ByteTagEnv c3 l3 x.m.hdr)
        (fun c4 => StageSeqEnv c4 l4 a5 (optBytesField1ByteTagEnv c4 l4 x.m.es)
          (fun c5 => optBytesField1ByteTagEnv c5 l5 x.m.ct1))) e :=
    fun c2 => StageSeqEnv.nonempty (optAuthField2Env_nonempty c2 l2 x.m.auth) (hK3 c2)
  have hK1 : ∀ c1, ∃ e, StageSeqEnv c1 l1 a2 (u64Field1Env c1 l1 x.m.epoch)
      (fun c2 => StageSeqEnv c2 l2 a3 (optAuthField2Env c2 l2 x.m.auth)
        (fun c3 => StageSeqEnv c3 l3 a4 (optBytesField1ByteTagEnv c3 l3 x.m.hdr)
          (fun c4 => StageSeqEnv c4 l4 a5 (optBytesField1ByteTagEnv c4 l4 x.m.es)
            (fun c5 => optBytesField1ByteTagEnv c5 l5 x.m.ct1)))) e :=
    fun c1 => StageSeqEnv.nonempty (u64Field1Env_nonempty c1 l1 x.m.epoch) (hK2 c1)
  dsimp only [Ct1SentEncodeEnvS] at hfits
  have hfits1 : FitsEnv M lim st (hdrFieldEnv x.cap x.bs.length (ct1SentPBEncodedLen x.m)) :=
    FitsEnv.stageSeq_left hfits (hK1 x.cap)
  have hfit_hdr : x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length ≤ x.cap.toNat ∨
      x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_hdr_1_placed hres A lim H hencLen henc hdoReserve x.g x.msgA x.v x.cap x.ptr s0.sp x.bs x.m st
    hcap_le hlen_fit hfit_hdr hfits1 (F := emp) hpc hrun rfl halign rfl hx0 hx1
    (UnchunkedEncodeCalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 sv3 evs₁ hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hge1 hpres1 hev1
  let bs1 := x.bs ++ msgHeaderBytes (ct1SentPBEncodedLen x.m)
  let st1 := M.stepEvents evs₁ st
  let S := ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ sv3) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hbs1_len : bs1.length = l1 := List.length_append
  have hcap1 : CapAfter x.cap l0 a1 cap1 := ⟨hge1, fun h => (hpres1 h).1⟩
  have hfits_rem1 := FitsEnv.stageSeq_right hfits hev1 hcap1
  have hfits2 : FitsEnv M lim st1 (u64Field1Env cap1 bs1.length x.m.epoch) := by
    rw [hbs1_len]; exact FitsEnv.stageSeq_left hfits_rem1 (hK2 cap1)
  have hfit_ep : bs1.length + (u64Field1Bytes x.m.epoch).length ≤ cap1.toNat ∨
      bs1.length + (u64Field1Bytes x.m.epoch).length + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1] at hbs1_len
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_epoch_1_placed hres A lim H henc hdoReserve x.msgA x.v cap1 ptr1 x.m.epoch s0.sp bs1 st1
    hfit_ep hfits2 hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗
      vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗
      vecU8At A.repAlloc (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗
      optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x48#64) x.m.auth ∗ S ∗ emp)
    (by dsimp [bs1, st1, S, ct1SentPBPinnedAt, unchunked5PinnedAt]; sep_ac_rfl) ?_
  intro s2 cap2 ptr2 evs₂ hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2 hev2
  let bs2 := bs1 ++ u64Field1Bytes x.m.epoch
  let st2 := M.stepEvents evs₂ st1
  have hbs2_len : bs2.length = l2 := by dsimp [bs2, l2]; rw [List.length_append, hbs1_len]
  have hev2' : u64Field1Env cap1 l1 x.m.epoch evs₂ := by rwa [← hbs1_len]
  have hcap2 : CapAfter cap1 l1 a2 cap2 := ⟨hge2, fun h => (hpres2 (by rw [hbs1_len]; exact h)).1⟩
  have hfits_rem2 := FitsEnv.stageSeq_right hfits_rem1 hev2' hcap2
  have hfits3 : FitsEnv M lim st2 (optAuthField2Env cap2 bs2.length x.m.auth) := by
    rw [hbs2_len]; exact FitsEnv.stageSeq_left hfits_rem2 (hK3 cap2)
  have hfit_auth : bs2.length + (optAuthField2Bytes x.m.auth).length ≤ cap2.toNat ∨
      bs2.length + (optAuthField2Bytes x.m.auth).length + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1, a2, l2] at hbs2_len
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_auth_1_placed A lim H hauth x.g.auth x.msgA x.v cap2 ptr2 s0.sp bs2 x.m.auth st2
    hfit_auth hfits3 hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗ vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗
      vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗
      vecU8At A.repAlloc (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs2, st2]; sep_ac_rfl) ?_
  intro s3 cap3 ptr3 evs₃ hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hge3 hpres3 hev3
  let bs3 := bs2 ++ optAuthField2Bytes x.m.auth
  let st3 := M.stepEvents evs₃ st2
  have hbs3_len : bs3.length = l3 := by dsimp [bs3, l3]; rw [List.length_append, hbs2_len]
  have hev3' : optAuthField2Env cap2 l2 x.m.auth evs₃ := by rwa [← hbs2_len]
  have hcap3 : CapAfter cap2 l2 a3 cap3 := ⟨hge3, fun h => (hpres3 (by rw [hbs2_len]; exact h)).1⟩
  have hfits_rem3 := FitsEnv.stageSeq_right hfits_rem2 hev3' hcap3
  have hfits4 : FitsEnv M lim st3 (optBytesField1ByteTagEnv cap3 bs3.length x.m.hdr) := by
    rw [hbs3_len]; exact FitsEnv.stageSeq_left hfits_rem3 (hK4 cap3)
  have hfit_hdrf : bs3.length + (bytesFieldTagged 3#32 x.m.hdr).length ≤ cap3.toNat ∨
      bs3.length + (bytesFieldTagged 3#32 x.m.hdr).length + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1, a2, l2, a3, l3] at hbs3_len
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_hdrf_1_placed hres A lim H henc hdoReserve hmemcpy
    x.msgA x.v cap3 ptr3 x.g.f3.cap x.g.f3.ptr s0.sp bs3 x.m.hdr st3
    hfit_hdrf hfits4 hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x48#64) x.m.auth ∗
      ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗
      vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗
      vecU8At A.repAlloc (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs3, st3]; sep_ac_rfl) ?_
  intro s4 cap4 ptr4 evs₄ hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 hge4 hpres4 hev4
  let bs4 := bs3 ++ bytesFieldTagged 3#32 x.m.hdr
  let st4 := M.stepEvents evs₄ st3
  have hbs4_len : bs4.length = l4 := by dsimp [bs4, l4]; rw [List.length_append, hbs3_len]
  have hev4' : optBytesField1ByteTagEnv cap3 l3 x.m.hdr evs₄ := by rwa [← hbs3_len]
  have hcap4 : CapAfter cap3 l3 a4 cap4 := ⟨hge4, fun h => (hpres4 (by rw [hbs3_len]; exact h)).1⟩
  have hfits_rem4 := FitsEnv.stageSeq_right hfits_rem3 hev4' hcap4
  have hfits5 : FitsEnv M lim st4 (optBytesField1ByteTagEnv cap4 bs4.length x.m.es) := by
    rw [hbs4_len]; exact FitsEnv.stageSeq_left hfits_rem4 (hK5 cap4)
  have hfit_es : bs4.length + (bytesFieldTagged 4#32 x.m.es).length ≤ cap4.toNat ∨
      bs4.length + (bytesFieldTagged 4#32 x.m.es).length + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1, a2, l2, a3, l3, a4, l4] at hbs4_len
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_es_1_placed hres A lim H henc hdoReserve hmemcpy
    x.msgA x.v cap4 ptr4 x.g.f4.cap x.g.f4.ptr s0.sp bs4 x.m.es st4
    hfit_es hfits5 hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4
    (F := vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗
      optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x48#64) x.m.auth ∗
      ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗
      vecU8At A.repAlloc (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs4, st4]; sep_ac_rfl) ?_
  intro s5 cap5 ptr5 evs₅ hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5 hge5 hpres5 hev5
  let bs5 := bs4 ++ bytesFieldTagged 4#32 x.m.es
  let st5 := M.stepEvents evs₅ st4
  have hbs5_len : bs5.length = l5 := by dsimp [bs5, l5]; rw [List.length_append, hbs4_len]
  have hev5' : optBytesField1ByteTagEnv cap4 l4 x.m.es evs₅ := by rwa [← hbs4_len]
  have hcap5 : CapAfter cap4 l4 a5 cap5 := ⟨hge5, fun h => (hpres5 (by rw [hbs4_len]; exact h)).1⟩
  have hfits_rem5 := FitsEnv.stageSeq_right hfits_rem4 hev5' hcap5
  have hfits6 : FitsEnv M lim st5 (optBytesField1ByteTagEnv cap5 bs5.length x.m.ct1) := by
    rw [hbs5_len]; exact hfits_rem5
  have hfit_ct1f : bs5.length + (bytesFieldTagged 5#32 x.m.ct1).length ≤ cap5.toNat ∨
      bs5.length + (bytesFieldTagged 5#32 x.m.ct1).length + 10 < 2 ^ 62 := by
    dsimp only [innerLen, l0, a1, l1, a2, l2, a3, l3, a4, l4, a5, l5] at hbs5_len
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_ct1f_1_placed hres A lim H henc hdoReserve hmemcpy
    x.msgA x.v cap5 ptr5 x.g.f5.cap x.g.f5.ptr s0.sp bs5 x.m.ct1 st5
    hfit_ct1f hfits6 hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hcs5
    (F := vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗
      vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗
      optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x48#64) x.m.auth ∗
      ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗ S ∗ emp)
    (by dsimp [bs5, st5]; sep_ac_rfl) ?_
  intro s6 cap6 ptr6 evs₆ hpc6 hrun6 hsp6 htr6 hcs6 hge6 hpres6 hev6
  let st6 := M.stepEvents evs₆ st5
  have hev6' : optBytesField1ByteTagEnv cap5 l5 x.m.ct1 evs₆ := by rwa [← hbs5_len]
  refine step_ct1_epilogue_1_placed hres H s0.sp sv3
    (F := vecU8At A.repAlloc (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗
      vecU8At A.repAlloc x.v cap6 ptr6 (bs5 ++ bytesFieldTagged 5#32 x.m.ct1) ∗
      A.pool lim st6 s6 ∗ vecU8At A.repAlloc (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗
      vecU8At A.repAlloc x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗
      optAuthenticatorPBPinnedAt A.repAlloc x.g.auth (x.msgA + 0x48#64) x.m.auth ∗
      ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗ emp)
    hpc6 hrun6 hsp6 halign htr6 hcs6 (by dsimp [S]; sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hcc _ hvm_ep; refine ⟨fun hm => ?_, hspf, hcc⟩
  have hge_all : x.cap.toNat ≤ cap6.toNat :=
    Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 (Nat.le_trans hge4 (Nat.le_trans hge5 hge6))))
  have hpres_all : x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat → cap6 = x.cap ∧ ptr6 = x.ptr := by
    intro hfit_cap
    dsimp only [innerLen, l0, a1, l1, a2, l2, a3, l3, a4, l4, a5, l5]
      at hbs1_len hbs2_len hbs3_len hbs4_len hbs5_len
    obtain ⟨hc1, hp1⟩ := hpres1 (by omega); obtain ⟨hc2, hp2⟩ := hpres2 (by omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by omega); obtain ⟨hc4, hp4⟩ := hpres4 (by omega)
    obtain ⟨hc5, hp5⟩ := hpres5 (by omega); obtain ⟨hc6, hp6⟩ := hpres6 (by omega)
    exact ⟨hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))),
      hp6.trans (hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1))))⟩
  let evsAll := evs₁ ++ (evs₂ ++ (evs₃ ++ (evs₄ ++ (evs₅ ++ evs₆))))
  have hev_all : Ct1SentEncodeEnvS (ct1SentPinnedToUnpinned x) evsAll :=
    StageSeqEnv.intro hev1 hcap1
      (StageSeqEnv.intro hev2' hcap2
        (StageSeqEnv.intro hev3' hcap3
          (StageSeqEnv.intro hev4' hcap4
            (StageSeqEnv.intro hev5' hcap5 hev6'))))
  have hst_eq : M.stepEvents evsAll st = st6 := by
    dsimp only [evsAll, st6, st5, st4, st3, st2, st1]
    simp only [M.stepEvents_append]
  dsimp only [ct1SentEncodePinnedSpecOfS, ct1SentEncodePinnedSpecOfEnv]
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evsAll, cap6, ptr6, ?_⟩
  have hpure1 : (x.cap.toNat ≤ cap6.toNat ∧
      (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat → cap6 = x.cap ∧ ptr6 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  have hpure2 : Ct1SentEncodeEnvS (ct1SentPinnedToUnpinned x) evsAll = True := eq_true hev_all
  rw [hpure1, hpure2, pure_true, emp_sepConj, emp_sepConj, hst_eq, ct1SentPBPinnedAt, unchunked5PinnedAt,
    ← bs0_append_encodeCt1SentMsg x.bs x.m]
  dsimp only [bs5, bs4, bs3, bs2, bs1] at hm
  rw [← A.pool_of_vmPreserved hvm_ep, sepConj_emp] at hm
  convert hm using 1; sep_ac_rfl

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1PlacedBudget
