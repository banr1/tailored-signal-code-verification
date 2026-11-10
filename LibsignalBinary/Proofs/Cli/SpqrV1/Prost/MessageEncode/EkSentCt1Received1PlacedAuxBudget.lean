/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.ReprPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1PlacedAuxBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Stages 1–4 of `encode<EkSentCt1Received> [local#3]` (Block `458`)

Proves budget-threaded `SepWPp` lemmas for Stages 1–4 (outer header, `epoch`, `auth`, and `dk`) on
CLI Block `458` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1Received1PlacedAuxBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsMemcpySym lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB V1State)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost vecU8At_eq_header_sep_buf)
open CryptoVerification.SpqrV1.Varint
  (elem_len_after_reserve_not_ult elem_len_ult_spare_iff encodeVarint_length_bounds
   vecU8At_expose_slice vecU8At_pack_slice)
open CryptoVerification.SpqrV1.ProtoRepr
  (AuthenticatorPBGhost Unchunked4PBGhost authenticatorPBPinnedAt
   ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt optAuthenticatorPBPinnedAt)
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
   bs_append_bytesField3_of_ne_empty bs_append_bytesFieldTagged_of_empty
   bs_append_msgHeaderBytes bs_append_optAuthField2Bytes_none
   bs_append_optAuthField2Bytes_some bs_append_u64Field1Bytes_of_ne_zero
   bs_append_u64Field1Bytes_of_zero bytesField3_len_of_ne_empty bytesFieldTagged
   msgHeaderBytes msgHeaderBytes_len_bounds optAuthField2Bytes
   stackAt_unchunkedMsgEncode u64Field1Bytes u64Field1Bytes_len_of_ne_zero
   unchunkedMsgEncodeStackOf vecU8At_expose_src_of_ne_nil_placed
   withUnchunkedEncodeCSPlaced)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed
  (blkPl_458 blkPl_458_ρ lsProg_458)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents fitsEvents_append
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents pushBytesEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget (ekSentCt1ReceivedEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (AuthEncodeEnv authEncodePinnedSpecOf sepWPp_extract_vecU8At_bounds)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (pushBytesStep_snd_eq reserveStep reserveStep_of_need_doReserveEvents reserveStep_of_spare
   sepWP_done_tpidr_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget (u64Field1Step)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
  (fitsEvents_optBytesReserve_of_fitsEnv fitsEvents_optBytesTag_of_fitsEnv
   hdrFieldEnv optAuthField2Env optBytesField1ByteTagEnv
   optBytesField1ByteTagEnv_of_empty optBytesField1ByteTagEnv_of_ne_empty
   u64Field1Env)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
  (step_ekSentCt1Received_encoded_len_call_placed step_unchunked_auth_encode_call_placed
   step_unchunked_do_reserve2_call_placed step_unchunked_encode_varint_call_placed
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
  blkPl_458_ρ

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

/-! ## 1. Stage 1: Outer Header -/

private theorem step_ek_hdr_from_44_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (hencLen : subroutine_ok (lsProg_458 H) (lsmpl.base 499)
      (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A.repAlloc)))
    (henc : subroutine_ok (lsProg_458 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (g : Unchunked4PBGhost) (msgA v curCap curPtr sp : BitVec 64)
    (bs0 : List (BitVec 8)) (m : V1State.Unchunked.EkSentCt1Received) (curSt : M.σ)
    (hlt : bs0.length < curCap.toNat) (hlen_fit : ekSentCt1ReceivedPBEncodedLen m < 2 ^ 64)
    (hfit' : bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ curCap.toNat ∨
      bs0.length + 1 + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents
        (EncodeVarintGhost.mk (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))
          v curCap curPtr (bs0 ++ [0x0a#8]))))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_458).base + 44#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs0.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v curCap curPtr bs0 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_458).base + 80#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap1.toNat →
      (bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ curCap.toNat →
        cap1 = curCap ∧ ptr1 = curPtr) →
      SepWPp (lsProg_458 H) ret sm
        ((ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)) ∗
          A.pool lim
            (M.stepEvents
              (encodeVarintEvents
                (EncodeVarintGhost.mk (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))
                  v curCap curPtr (bs0 ++ [0x0a#8])))
              curSt)
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_458 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs0 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 499)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        refine step_ekSentCt1Received_encoded_len_call_placed hres A lim curSt hencLen g msgA
          sp ((blkPl_458).base + 72#64) m hlen_fit
          (F := vecU8At A.repAlloc v curCap curPtr (bs0 ++ [0x0a#8]) ∗ F)
          an an an halign an an an (cs_step hcs hinv1)
          (by rw [← A.pool_of_vmPreserved hvm1,
                ← vecU8At_close_one A.repAlloc v curCap curPtr bs0 0x0a#8 hlt]; try sep_ac_rfl) ?_
        intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs01 hcs1 _
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 451)
        by_vm_steps (
          wp_steps
          exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
            (fun hvm2 hinv2 => by
              have hhdr_eq :
                  (bs0 ++ [0x0a#8]).length +
                    (encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))).length =
                  bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length := by
                simp only [msgHeaderBytes, List.length_append, List.length_singleton]; omega
              have hvarint_fit :
                  (bs0 ++ [0x0a#8]).length +
                    (encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))).length ≤ curCap.toNat ∨
                  (bs0 ++ [0x0a#8]).length + 10 < 2 ^ 62 := by
                rw [hhdr_eq, List.length_append, List.length_singleton]; exact hfit'
              refine step_unchunked_encode_varint_call_placed hres A lim henc
                (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m)) v curCap curPtr sp
                ((blkPl_458).base + 80#64) (bs0 ++ [0x0a#8]) curSt hvarint_fit hfits
                (F := ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗ F)
                an an an halign an an an an (cs_step hcs1 hinv2)
                (by rw [← A.pool_of_vmPreserved hvm2]; try sep_ac_rfl) ?_
              intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge1 hpres1
              rw [hhdr_eq] at hpres1
              refine SepWPp.weaken_pre
                (by rw [bs_append_msgHeaderBytes bs0 (ekSentCt1ReceivedPBEncodedLen m)]
                    exact Entails.of_eq (by sep_ac_rfl))
                (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2
                  (by rw [hcs12.1]; simp only [arm64_norm, *])
                  (by rw [hcs12.2.1]; simp only [arm64_norm, *])
                  hcs2 hge1 hpres1)))))

theorem step_ek_hdr_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_458 H) (lsmpl.base 499)
      (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A.repAlloc)))
    (henc : subroutine_ok (lsProg_458 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_458 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (g : Unchunked4PBGhost) (msgA v cap0 ptr0 sp : BitVec 64)
    (bs0 : List (BitVec 8)) (m : V1State.Unchunked.EkSentCt1Received) (curSt : M.σ)
    (hcap_le : bs0.length ≤ cap0.toNat) (hlen_fit : ekSentCt1ReceivedPBEncodedLen m < 2 ^ 64)
    (hfit : bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ cap0.toNat ∨
      bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (hdrFieldEnv cap0 bs0.length (ekSentCt1ReceivedPBEncodedLen m)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_458).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = msgA) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ A.pool lim curSt s ∗
      stackAt sp (unchunkedMsgEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 sv3 : BitVec 64) (evs₁ : List AllocEvent),
      sm.pc = (blkPl_458).base + 80#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap0.toNat ≤ cap1.toNat →
      (bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ cap0.toNat →
        cap1 = cap0 ∧ ptr1 = ptr0) →
      hdrFieldEnv cap0 bs0.length (ekSentCt1ReceivedPBEncodedLen m) evs₁ →
      SepWPp (lsProg_458 H) ret sm
        ((ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)) ∗
          A.pool lim (M.stepEvents evs₁ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
          ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_458 H) ret s P Q Qp oom := by
  have hstep44 := step_ek_hdr_from_44_1_placed hres A lim H hencLen henc
  subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  have hhdr_bds := msgHeaderBytes_len_bounds (ekSentCt1ReceivedPBEncodedLen m)
  have hfits_hdr : FitsEvents M lim curSt
      (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))).length + 1)
        cap0.toNat bs0.length) := hfits _ rfl
  rw [stackAt_unchunkedMsgEncode hres sp, vecU8At_eq_header_sep_buf A.repAlloc v cap0 ptr0 bs0, vecHeader]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  let S := ((sp - 64#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s.readReg64 .lr) ∗
    ((sp - 48#64) ↦₆₄ s.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
    ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
    ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)
  by_cases hcap0 : cap0 == BitVec.ofNat 64 bs0.length
  · have hcap_eq : cap0.toNat = bs0.length :=
      cap_toNat_eq_of_beq hcap0 (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit2 : bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length + 10 < 2 ^ 62 := by
      rcases hfit with h | h <;> omega
    obtain ⟨hbound1, hlt1, hge0⟩ := reserveCap_one_bounds hcap_eq (by omega)
    have hres_lt64 : reserveCap cap0.toNat bs0.length 1 < 2 ^ 64 := by omega
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 => by
          have hfits_res : FitsEvents M lim curSt
              (doReserveEvents (DoReserveCall.mk v cap0 ptr0 bs0 1)) := by
            have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
              (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m)) v cap0 ptr0 0#64 bs0 0x0a#8 hcap_eq hres_lt64
            rw [← hev_eq] at hfits_hdr
            exact ((fitsEvents_append M lim _ _ curSt).mp hfits_hdr).1
          refine step_unchunked_do_reserve2_call_placed hres A lim hdoReserve v cap0 ptr0 sp
            ((blkPl_458).base + 404#64) bs0 1 curSt hbound1 hfits_res
            (F := ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗ S ∗ F)
            an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
            (by simp only [arm64_norm]) (cs_step hcs hinv0)
            (by dsimp [S]; rw [← A.pool_of_vmPreserved hvm0, vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
          intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
          let newCap1 := BitVec.ofNat 64 (reserveCap cap0.toNat bs0.length 1)
          have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
            (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m)) v cap0 ptr0 newPtr1 bs0 0x0a#8 hcap_eq hres_lt64
          have hfits_var : FitsEvents M lim
              (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap0 ptr0 bs0 1)) curSt)
              (encodeVarintEvents
                (EncodeVarintGhost.mk (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))
                  v newCap1 newPtr1 (bs0 ++ [0x0a#8]))) := by
            rw [← hev_eq] at hfits_hdr
            exact ((fitsEvents_append M lim _ _ curSt).mp hfits_hdr).2
          have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
          rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs0, vecHeader]
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 44#64)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm1 hinv1 =>
                hstep44 g msgA v newCap1 newPtr1 sp bs0 m
                  (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap0 ptr0 bs0 1)) curSt)
                  hlt1 hlen_fit (Or.inr (by omega)) hfits_var (F := S ∗ F)
                  an an an halign an an an
                  (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
                  (cs_step hcs1 hinv1)
                  (by rw [← A.pool_of_vmPreserved hvm1, vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                  (fun sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 _ =>
                    SepWPp.weaken_pre
                      (by dsimp [S]; rw [← M.stepEvents_append, hev_eq]; exact Entails.of_eq (by sep_ac_rfl))
                      (hnext sm cap1 ptr1 sv3
                        (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))).length + 1)
                          cap0.toNat bs0.length)
                        hpcm hrunm hspm htrm hx19m hx20m hcsm
                        (Nat.le_trans hge0 hge1) (fun h => absurd h (by omega)) rfl))))))
  · have hcap0_f : (cap0 == BitVec.ofNat 64 bs0.length) = false := Bool.eq_false_iff.mpr hcap0
    have hlt0 : bs0.length < cap0.toNat :=
      lt_cap_toNat_of_beq_false hcap0_f hcap_le (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit44 : bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ cap0.toNat ∨
        bs0.length + 1 + 10 < 2 ^ 62 := by
      rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
    have hev_eq := encodeVarintEvents_after_tag_of_lt
      (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m)) v cap0 ptr0 bs0 0x0a#8 hlt0
    have hfits_var : FitsEvents M lim curSt
        (encodeVarintEvents
          (EncodeVarintGhost.mk (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))
            v cap0 ptr0 (bs0 ++ [0x0a#8]))) := by
      rwa [hev_eq]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 44#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 =>
          hstep44 g msgA v cap0 ptr0 sp bs0 m curSt hlt0 hlen_fit hfit44 hfits_var (F := S ∗ F)
            an an an halign an an an an (cs_step hcs hinv0)
            (by dsimp [S]; rw [← A.pool_of_vmPreserved hvm0, vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
            (fun sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 hpres1 =>
              SepWPp.weaken_pre
                (by dsimp [S]; rw [hev_eq]; exact Entails.of_eq (by sep_ac_rfl))
                (hnext sm cap1 ptr1 sv3
                  (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))).length + 1)
                    cap0.toNat bs0.length)
                  hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 hpres1 rfl))))

/-! ## 2. Stage 2: Field 1 — `epoch: u64` -/

private theorem step_ek_epoch_from_104_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_458 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (msgA v curCap curPtr epoch sp : BitVec 64) (bs1 : List (BitVec 8)) (curSt : M.σ)
    (hep : (epoch == 0#64) = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (u64Field1Bytes epoch).length ≤ curCap.toNat ∨ bs1.length + 1 + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk epoch v curCap curPtr (bs1 ++ [0x08#8]))))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_458).base + 104#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = epoch)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs1 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_458).base + 132#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap2.toNat →
      (bs1.length + (u64Field1Bytes epoch).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp (lsProg_458 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ u64Field1Bytes epoch) ∗
          A.pool lim
            (M.stepEvents
              (encodeVarintEvents (EncodeVarintGhost.mk epoch v curCap curPtr (bs1 ++ [0x08#8])))
              curSt)
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_458 H) ret s P Q Qp oom := by
  subst hP
  have hep_ne : epoch ≠ 0#64 := beq_eq_false_iff_ne.mp hep
  have hep_len := u64Field1Bytes_len_of_ne_zero hep_ne
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs1 hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 451)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        have hlen_eq :
            (bs1 ++ [0x08#8]).length + (encodeVarint epoch).length =
            bs1.length + (u64Field1Bytes epoch).length := by
          rw [List.length_append, List.length_singleton, hep_len]; omega
        have hvarint_fit :
            (bs1 ++ [0x08#8]).length + (encodeVarint epoch).length ≤ curCap.toNat ∨
            (bs1 ++ [0x08#8]).length + 10 < 2 ^ 62 := by
          rw [hlen_eq, List.length_append, List.length_singleton]; exact hfit
        refine step_unchunked_encode_varint_call_placed hres A lim henc epoch v curCap curPtr sp
          ((blkPl_458).base + 132#64) (bs1 ++ [0x08#8]) curSt hvarint_fit hfits (F := F)
          an an an halign an an an an (cs_step hcs hinv1)
          (by rw [← A.pool_of_vmPreserved hvm1,
                ← vecU8At_close_one A.repAlloc v curCap curPtr bs1 0x08#8 hlt]; try sep_ac_rfl) ?_
        intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hge2 hpres2
        rw [hlen_eq] at hpres2
        refine SepWPp.weaken_pre
          (by rw [bs_append_u64Field1Bytes_of_ne_zero hep_ne bs1]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1
            (by rw [hcs01.1]; simp only [arm64_norm, *])
            (by rw [hcs01.2.1]; simp only [arm64_norm, *])
            hcs1 hge2 hpres2)))

theorem step_ek_epoch_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_458 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_458 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (msgA v cap1 ptr1 epoch sp : BitVec 64) (bs1 : List (BitVec 8)) (curSt : M.σ)
    (hfit : bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat ∨
      bs1.length + (u64Field1Bytes epoch).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (u64Field1Env cap1 bs1.length epoch))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_458).base + 80#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (((msgA + 0x60#64) ↦₆₄ epoch) ∗
      vecU8At A.repAlloc v cap1 ptr1 bs1 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs₂ : List AllocEvent),
      sm.pc = (blkPl_458).base + 132#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap1.toNat ≤ cap2.toNat →
      (bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      u64Field1Env cap1 bs1.length epoch evs₂ →
      SepWPp (lsProg_458 H) ret sm
        ((((msgA + 0x60#64) ↦₆₄ epoch) ∗
          vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ u64Field1Bytes epoch) ∗
          A.pool lim (M.stepEvents evs₂ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_458 H) ret s P Q Qp oom := by
  have hstep104 := step_ek_epoch_from_104_1_placed hres A lim H henc
  subst hP
  by_cases hep : epoch == 0#64
  · have hev0 : u64Field1Env cap1 bs1.length epoch [] := by
      simp only [u64Field1Env, u64Field1Step, hep, ↓reduceIte]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 132#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 =>
          SepWPp.weaken_pre
            (by rw [← A.pool_of_vmPreserved hvm0, ← M.stepEvents_nil curSt,
                  ← bs_append_u64Field1Bytes_of_zero (beq_iff_eq.mp hep) bs1]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ cap1 ptr1 [] an an an an an an (cs_step hcs hinv0)
              (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) hev0)))
  · have hep_f : (epoch == 0#64) = false := Bool.eq_false_iff.mpr hep
    have hep_len := u64Field1Bytes_len_of_ne_zero (beq_eq_false_iff_ne.mp hep_f)
    have hep_bds := encodeVarint_length_bounds epoch
    have hev_ep : u64Field1Env cap1 bs1.length epoch
        (pushBytesEvents ((encodeVarint epoch).length + 1) cap1.toNat bs1.length) := by
      simp only [u64Field1Env, u64Field1Step, hep_f, Bool.false_eq_true, ↓reduceIte, pushBytesStep_snd_eq]
    have hfits_ep : FitsEvents M lim curSt
        (pushBytesEvents ((encodeVarint epoch).length + 1) cap1.toNat bs1.length) :=
      hfits _ hev_ep
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := ((msgA + 0x60#64) ↦₆₄ epoch) ∗ A.pool lim curSt s ∗
        stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1, vecHeader]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · have hcap_eq : cap1.toNat = bs1.length :=
        cap_toNat_eq_of_beq hcap1 (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hfit2 : bs1.length + (u64Field1Bytes epoch).length + 10 < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      have hres_lt64 : reserveCap cap1.toNat bs1.length 1 < 2 ^ 64 := by omega
      apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 => by
            have hfits_res : FitsEvents M lim curSt
                (doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)) := by
              have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
                epoch v cap1 ptr1 0#64 bs1 0x08#8 hcap_eq hres_lt64
              rw [← hev_eq] at hfits_ep
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_ep).1
            refine step_unchunked_do_reserve2_call_placed hres A lim hdoReserve v cap1 ptr1 sp
              ((blkPl_458).base + 428#64) bs1 1 curSt hbound1 hfits_res
              (F := ((msgA + 0x60#64) ↦₆₄ epoch) ∗ F)
              an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
              (by simp only [arm64_norm]) (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0, vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
            intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
            let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
            have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
              epoch v cap1 ptr1 newPtr1 bs1 0x08#8 hcap_eq hres_lt64
            have hfits_var : FitsEvents M lim
                (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)) curSt)
                (encodeVarintEvents (EncodeVarintGhost.mk epoch v newCap1 newPtr1 (bs1 ++ [0x08#8]))) := by
              rw [← hev_eq] at hfits_ep
              exact ((fitsEvents_append M lim _ _ curSt).mp hfits_ep).2
            have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
            rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs1, vecHeader]
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 104#64)
            by_vm_steps (
              wp_steps
              exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                (fun hvm1 hinv1 =>
                  hstep104 msgA v newCap1 newPtr1 epoch sp bs1
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)) curSt)
                    hep_f hlt1 (Or.inr (by omega)) hfits_var
                    (F := ((msgA + 0x60#64) ↦₆₄ epoch) ∗ F)
                    an an an halign an
                    (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
                    an an
                    (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
                    (cs_step hcs1 hinv1)
                    (by rw [← A.pool_of_vmPreserved hvm1, vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
                    (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 _ =>
                      SepWPp.weaken_pre
                        (by rw [← M.stepEvents_append, hev_eq]; exact Entails.of_eq (by sep_ac_rfl))
                        (hnext sm cap2 ptr2
                          (pushBytesEvents ((encodeVarint epoch).length + 1) cap1.toNat bs1.length)
                          hpcm hrunm hspm htrm hx19m hx20m hcsm
                          (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)) hev_ep))))))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat :=
        lt_cap_toNat_of_beq_false hcap1_f hcap1_le (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hfit104 : bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat ∨
          bs1.length + 1 + 10 < 2 ^ 62 := by
        rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
      have hev_eq := encodeVarintEvents_after_tag_of_lt epoch v cap1 ptr1 bs1 0x08#8 hlt1
      have hfits_var : FitsEvents M lim curSt
          (encodeVarintEvents (EncodeVarintGhost.mk epoch v cap1 ptr1 (bs1 ++ [0x08#8]))) := by
        rwa [hev_eq]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 104#64)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 =>
            hstep104 msgA v cap1 ptr1 epoch sp bs1 curSt hep_f hlt1 hfit104 hfits_var
              (F := ((msgA + 0x60#64) ↦₆₄ epoch) ∗ F)
              an an an halign an an an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0, vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
              (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 hpres2 =>
                SepWPp.weaken_pre
                  (by rw [hev_eq]; exact Entails.of_eq (by sep_ac_rfl))
                  (hnext sm cap2 ptr2
                    (pushBytesEvents ((encodeVarint epoch).length + 1) cap1.toNat bs1.length)
                    hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 hpres2 hev_ep))))

/-! ## 3. Stage 3: Field 2 — `auth: Option<Authenticator>` -/

theorem step_ek_auth_1_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hauthEnc : subroutine_ok (lsProg_458 H) (lsmpl.base 454)
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A lim)))
    (gAuth : AuthenticatorPBGhost) (msgA v cap2 ptr2 sp : BitVec 64)
    (bs2 : List (BitVec 8)) (optAuth : Option AuthenticatorPB) (curSt : M.σ)
    (hfit : bs2.length + (optAuthField2Bytes optAuth).length ≤ cap2.toNat ∨
      bs2.length + (optAuthField2Bytes optAuth).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (optAuthField2Env cap2 bs2.length optAuth))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_458).base + 132#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (optAuthenticatorPBPinnedAt A.repAlloc gAuth (msgA + 0x30#64) optAuth ∗
      vecU8At A.repAlloc v cap2 ptr2 bs2 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs₃ : List AllocEvent),
      sm.pc = (blkPl_458).base + 156#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap2.toNat ≤ cap3.toNat →
      (bs2.length + (optAuthField2Bytes optAuth).length ≤ cap2.toNat → cap3 = cap2 ∧ ptr3 = ptr2) →
      optAuthField2Env cap2 bs2.length optAuth evs₃ →
      SepWPp (lsProg_458 H) ret sm
        ((optAuthenticatorPBPinnedAt A.repAlloc gAuth (msgA + 0x30#64) optAuth ∗
          vecU8At A.repAlloc v cap3 ptr3 (bs2 ++ optAuthField2Bytes optAuth) ∗
          A.pool lim (M.stepEvents evs₃ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_458 H) ret s P Q Qp oom := by
  subst hP
  cases optAuth with
  | none =>
    rw [optAuthenticatorPBPinnedAt]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 156#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 =>
          SepWPp.weaken_pre
            (by rw [← A.pool_of_vmPreserved hvm0, ← M.stepEvents_nil curSt,
                  optAuthenticatorPBPinnedAt, ← bs_append_optAuthField2Bytes_none bs2]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ cap2 ptr2 [] an an an an an an (cs_step hcs hinv0)
              (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) rfl)))
  | some auth =>
    have hfits_auth : FitsEnv M lim curSt
        (AuthEncodeEnv ⟨msgA + 0x30#64, auth, v, cap2, ptr2, bs2⟩) :=
      fun evs hev => hfits evs ⟨msgA + 0x30#64, v, ptr2, bs2, rfl, hev⟩
    rw [optAuthenticatorPBPinnedAt, authenticatorPBPinnedAt]
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := msgA + 0x30#64)
      (cap := gAuth.rootKey.cap) (ptr := gAuth.rootKey.ptr) (bs := auth.rootKey)
      (F := vecU8At A.repAlloc (msgA + 0x30#64 + 24#64) gAuth.macKey.cap gAuth.macKey.ptr auth.macKey ∗
        vecU8At A.repAlloc v cap2 ptr2 bs2 ∗ A.pool lim curSt s ∗
        stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun _ hrkCap_lt _ => ?_
    have hcap_beq := cap_add_one_beq_zero_false hrkCap_lt
    have hcap_bne := cap_add_one_bne_zero_true hrkCap_lt
    rw [vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x30#64) gAuth.rootKey.cap gAuth.rootKey.ptr auth.rootKey,
      vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 454)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 => by
          refine step_unchunked_auth_encode_call_placed A lim hauthEnc (msgA + 0x30#64)
            gAuth auth v cap2 ptr2 sp ((blkPl_458).base + 156#64) bs2 curSt
            hfit hfits_auth (F := F)
            an an an halign an an an an (cs_step hcs hinv0)
            (by rw [← A.pool_of_vmPreserved hvm0, authenticatorPBPinnedAt,
                  vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x30#64), vecHeader]; try sep_ac_rfl) ?_
          intro s1 cap3 ptr3 evs₃ hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hge3 hpres3 hev3
          refine SepWPp.weaken_pre
            (by rw [optAuthenticatorPBPinnedAt, bs_append_optAuthField2Bytes_some]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext s1 cap3 ptr3 evs₃ hpc1 hrun1 hsp1 htr1
              (by rw [hcs01.1]; simp only [arm64_norm, *])
              (by rw [hcs01.2.1]; simp only [arm64_norm, *])
              hcs1 hge3 hpres3 ⟨msgA + 0x30#64, v, ptr2, bs2, rfl, hev3⟩)))

/-! ## 4. Stage 4: Field 3 — `dk: Vec<u8>` -/

private theorem step_ek_dk_from_236_1_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_458 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs_mid dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hle : bs_mid.length + dk.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_458).base + 236#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length)
    (hx22 : s.readReg64 .x22 = dkPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_458).base + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_458 H) ret sm ((vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr (bs_mid ++ dk)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_458 H) ret s P Q Qp oom := by
  subst hP
  have hdk_ne_nil : dk ≠ [] := List.isEmpty_eq_false_iff.mp hdk_ne
  have hdk_pos : 0 < dk.length := List.length_pos_of_ne_nil hdk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A msgA dkCap dkPtr dk ∗ F) (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA) (cap := dkCap) (ptr := dkPtr) (bs := dk)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by sep_ac_rfl) fun hdk_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid dk.length hle hcap_lt hptr_ne hdk_pos,
    vecU8At_expose_src_of_ne_nil_placed A msgA dkCap dkPtr dk hdk_ne_nil hdk_le]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsρ lsMemcpySym)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        refine step_unchunked_memcpy_call_placed hmemcpy
          (curPtr + BitVec.ofNat 64 bs_mid.length) dkPtr sp ((blkPl_458).base + 256#64) dk
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
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 264#64)
        by_vm_steps (
          wp_steps
          exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
            (fun hvm2 hinv2 =>
              SepWPp.weaken_pre
                (by rw [← vecU8At_pack_slice A v curCap curPtr bs_mid dk hle hcap_lt hptr_ne hdk_ne_nil,
                      vecU8At_expose_src_of_ne_nil_placed A msgA dkCap dkPtr dk hdk_ne_nil hdk_le]
                    exact Entails.of_eq (by sep_ac_rfl))
                (hnext _ an an an an an an (cs_step hcs1 hinv2) (hvm1.trans (hvm_mc.trans hvm2)))))))

private theorem step_ek_dk_from_184_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_458 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_458 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_458 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
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
    (hpc : s.pc = (blkPl_458).base + 184#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs3.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length)
    (hx22 : s.readReg64 .x22 = dkPtr) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc msgA dkCap dkPtr dk ∗
      vecU8At A.repAlloc v curCap curPtr bs3 ∗ A.pool lim st_tag s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap_mid cap4 ptr4 : BitVec 64),
      sm.pc = (blkPl_458).base + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap_mid.toNat →
      (bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat →
        cap_mid = curCap) →
      cap_mid.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat →
        cap4 = curCap ∧ ptr4 = curPtr) →
      SepWPp (lsProg_458 H) ret sm
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
    SepWPp (lsProg_458 H) ret s P Q Qp oom := by
  have hstep236 := step_ek_dk_from_236_1_placed A.repAlloc H hmemcpy
  subst hP
  have hdk_len := bytesField3_len_of_ne_empty hdk_ne
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs3 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 451)
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
          (BitVec.ofNat 64 dk.length) v curCap curPtr sp ((blkPl_458).base + 216#64)
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
          apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
          by_vm_steps (
            wp_steps
            exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
              (fun hvm2 hinv2 => by
                refine step_unchunked_do_reserve2_call_placed hres A lim hdoReserve v cap_mid ptr_mid sp
                  ((blkPl_458).base + 476#64) bs_mid dk.length st_mid hbound_dk hfits_res_call
                  (F := vecU8At A.repAlloc msgA dkCap dkPtr dk ∗ F)
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
                have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 dk.length := by
                  rw [hcs23.2.2.1]; simp only [arm64_norm, *]
                have hx22_3 : s3.readReg64 .x22 = dkPtr := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
                rw [vecU8At_eq_header_sep_buf A.repAlloc v cap_res ptr_res bs_mid, vecHeader]
                apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 236#64)
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
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 236#64)
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

theorem step_ek_dk_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_458 H) (lsmpl.base 451)
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_458 H) (lsmpl.base 460)
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_458 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (msgA v cap3 ptr3 dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8)) (curSt : M.σ)
    (hfit : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ cap3.toNat ∨
      bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (optBytesField1ByteTagEnv cap3 bs3.length dk))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_458).base + 156#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc msgA dkCap dkPtr dk ∗
      vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64) (evs₄ : List AllocEvent),
      sm.pc = (blkPl_458).base + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap3.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 3#32 dk).length ≤ cap3.toNat → cap4 = cap3 ∧ ptr4 = ptr3) →
      optBytesField1ByteTagEnv cap3 bs3.length dk evs₄ →
      SepWPp (lsProg_458 H) ret sm
        ((vecU8At A.repAlloc msgA dkCap dkPtr dk ∗
          vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ bytesFieldTagged 3#32 dk) ∗
          A.pool lim (M.stepEvents evs₄ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_458 H) ret s P Q Qp oom := by
  have hstep184 := step_ek_dk_from_184_1_placed hres A lim H henc hdoReserve hmemcpy
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := msgA) (cap := dkCap)
    (ptr := dkPtr) (bs := dk)
    (F := vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hdk_le hdk_cap_lt _ => ?_
  have ⟨hdk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := dk) (by omega)
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
      apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
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
            refine step_unchunked_do_reserve2_call_placed hres A lim hdoReserve v cap3 ptr3 sp
              ((blkPl_458).base + 452#64) bs3 1 curSt hbound1 hfits_res1
              (F := vecU8At A.repAlloc msgA dkCap dkPtr dk ∗ F)
              an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
              (by simp only [arm64_norm]) (cs_step hcs hinv0)
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
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 184#64)
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
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 184#64)
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
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_458).base + 264#64)
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

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1Received1PlacedAuxBudget
