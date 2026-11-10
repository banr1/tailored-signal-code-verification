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
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Stages 1–3 of `unchunked::Ct1Sent::encode [local#2]` (`Block 319`)

Defines `IsCt1Enc2PlacedProg`, tag-push/varint event algebra helpers, and relocatable
`[LibsignalPlacement]` stage steppers on `lsProg_319` for Stage 1 (outer header), Stage 2
(`epoch: u64`), and Stage 3 (`auth: Option<Authenticator>`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlacedAuxBudget

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

/-- Relocatable `[LibsignalPlacement]` program descriptor for `Ct1Sent::encode [local#2]` (`lsProg_319`). -/
def IsCt1Enc2PlacedProg [LibsignalPlacement] (prog : Program)
    (entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64) : Prop :=
  ∃ (H : String → Option (State → State)),
    prog = lsProg_319 H ∧
    entry = (blkPl_319).base ∧
    encLen_pc = (blkPl_408).base ∧
    varint_pc = (blkPl_292).base ∧
    auth_pc = lsmpl.base 314 ∧
    reserve_pc = (blkPl_320).base ∧
    memcpy_pc = lsρ lsMemcpySym

/-! ## 0. Shared Tag-Push + Varint Event Algebra Helpers -/

theorem encodeVarintEvents_after_tag_of_lt (val v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (tag : BitVec 8) (hlt : bs.length < cap.toNat) :
    encodeVarintEvents (EncodeVarintGhost.mk val v cap ptr (bs ++ [tag])) =
      pushBytesEvents ((encodeVarint val).length + 1) cap.toNat bs.length := by
  dsimp only [encodeVarintEvents]
  rw [List.length_append, List.length_singleton]
  simp only [pushBytesEvents, pushByteStep, hlt, ↓reduceIte, List.nil_append]

theorem doReserveOne_append_encodeVarintEvents_of_eq (val v cap ptr newPtr1 : BitVec 64)
    (bs : List (BitVec 8)) (tag : BitVec 8) (hcap_eq : cap.toNat = bs.length)
    (hres_lt : reserveCap cap.toNat bs.length 1 < 2 ^ 64) :
    doReserveEvents (DoReserveCall.mk v cap ptr bs 1) ++
      encodeVarintEvents
        (EncodeVarintGhost.mk val v (BitVec.ofNat 64 (reserveCap cap.toNat bs.length 1))
          newPtr1 (bs ++ [tag])) =
      pushBytesEvents ((encodeVarint val).length + 1) cap.toNat bs.length := by
  have hneed : ¬ (bs.length + 1 ≤ cap.toNat) := by omega
  have hres_ev := congrArg Prod.snd (reserveStep_of_need_doReserveEvents v cap ptr bs 1 hneed)
  dsimp only at hres_ev
  have hres_one := reserveStep_one_eq_pushByteStep cap.toNat bs.length
  have hres_fst : (pushByteStep cap.toNat bs.length).1 = reserveCap cap.toNat bs.length 1 := by
    rw [← hres_one]; simp only [reserveStep, hneed, ↓reduceIte]
  have hres_snd : doReserveEvents (DoReserveCall.mk v cap ptr bs 1) =
      (pushByteStep cap.toNat bs.length).2 := by
    rw [← hres_ev, hres_one]
  dsimp only [encodeVarintEvents]
  rw [hres_snd, List.length_append, List.length_singleton,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hres_lt, ← hres_fst]
  rfl

/-! ## 1. Stage 1: Outer Header -/

private theorem step_hdr_from_44_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 : State}
    (hencLen : subroutine_ok prog encLen_pc
      (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A.repAlloc)))
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (g : Unchunked5PBGhost) (msgA v curCap curPtr sp : BitVec 64)
    (bs0 : List (BitVec 8)) (m : V1State.Unchunked.Ct1Sent) (curSt : M.σ)
    (hlt : bs0.length < curCap.toNat) (hlen_fit : ct1SentPBEncodedLen m < 2 ^ 64)
    (hfit' : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ curCap.toNat ∨
      bs0.length + 1 + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents
        (EncodeVarintGhost.mk (BitVec.ofNat 64 (ct1SentPBEncodedLen m))
          v curCap curPtr (bs0 ++ [0x0a#8]))))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 44#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs0.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (ct1SentPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v curCap curPtr bs0 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = entry + 80#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap1.toNat →
      (bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ curCap.toNat →
        cap1 = curCap ∧ ptr1 = curPtr) →
      SepWPp prog ret sm
        ((ct1SentPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ msgHeaderBytes (ct1SentPBEncodedLen m)) ∗
          A.pool lim
            (M.stepEvents
              (encodeVarintEvents
                (EncodeVarintGhost.mk (BitVec.ofNat 64 (ct1SentPBEncodedLen m))
                  v curCap curPtr (bs0 ++ [0x0a#8])))
              curSt)
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs0 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := encLen_pc)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
      (fun hvm1 hinv1 => by
        refine step_ct1Sent_encoded_len_call_placed hres A lim curSt hencLen g msgA
          sp ((blkPl_319).base + 72#64) m hlen_fit
          (F := vecU8At A.repAlloc v curCap curPtr (bs0 ++ [0x0a#8]) ∗ F)
          an an an halign an an an (cs_step hcs hinv1)
          (by rw [← A.pool_of_vmPreserved hvm1,
                ← vecU8At_close_one A.repAlloc v curCap curPtr bs0 0x0a#8 hlt]; try sep_ac_rfl) ?_
        intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs01 hcs1 _
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_292).base)
        by_vm_steps (
          wp_steps
          exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
            (fun hvm2 hinv2 => by
              have hhdr_eq :
                  (bs0 ++ [0x0a#8]).length +
                    (encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen m))).length =
                  bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length := by
                simp only [msgHeaderBytes, List.length_append, List.length_singleton]; omega
              have hvarint_fit :
                  (bs0 ++ [0x0a#8]).length +
                    (encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen m))).length ≤ curCap.toNat ∨
                  (bs0 ++ [0x0a#8]).length + 10 < 2 ^ 62 := by
                rw [hhdr_eq, List.length_append, List.length_singleton]; exact hfit'
              refine step_unchunked_encode_varint_call_placed hres A lim henc
                (BitVec.ofNat 64 (ct1SentPBEncodedLen m)) v curCap curPtr sp
                ((blkPl_319).base + 80#64) (bs0 ++ [0x0a#8]) curSt hvarint_fit hfits
                (F := ct1SentPBPinnedAt A.repAlloc g msgA m ∗ F)
                an an an halign an an an an (cs_step hcs1 hinv2)
                (by rw [← A.pool_of_vmPreserved hvm2]; try sep_ac_rfl) ?_
              intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge1 hpres1
              rw [hhdr_eq] at hpres1
              refine SepWPp.weaken_pre
                (by rw [bs_append_msgHeaderBytes bs0 (ct1SentPBEncodedLen m)]
                    exact Entails.of_eq (by sep_ac_rfl))
                (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2
                  (by rw [hcs12.1]; simp only [arm64_norm, *])
                  (by rw [hcs12.2.1]; simp only [arm64_norm, *])
                  hcs2 hge1 hpres1)))))

theorem step_ct1_hdr_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 s : State}
    (hencLen : subroutine_ok prog encLen_pc
      (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A.repAlloc)))
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (g : Unchunked5PBGhost) (msgA v cap0 ptr0 sp : BitVec 64)
    (bs0 : List (BitVec 8)) (m : V1State.Unchunked.Ct1Sent) (curSt : M.σ)
    (hcap_le : bs0.length ≤ cap0.toNat) (hlen_fit : ct1SentPBEncodedLen m < 2 ^ 64)
    (hfit : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ cap0.toNat ∨
      bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (hdrFieldEnv cap0 bs0.length (ct1SentPBEncodedLen m)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = msgA) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (ct1SentPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ A.pool lim curSt s ∗
      stackAt sp (unchunkedMsgEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 sv3 : BitVec 64) (evs₁ : List AllocEvent),
      sm.pc = entry + 80#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap0.toNat ≤ cap1.toNat →
      (bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ cap0.toNat →
        cap1 = cap0 ∧ ptr1 = ptr0) →
      hdrFieldEnv cap0 bs0.length (ct1SentPBEncodedLen m) evs₁ →
      SepWPp prog ret sm
        ((ct1SentPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ msgHeaderBytes (ct1SentPBEncodedLen m)) ∗
          A.pool lim (M.stepEvents evs₁ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
          ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hstep44 := step_hdr_from_44_2_placed hres A lim hfn hencLen henc
  subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  have hhdr_bds := msgHeaderBytes_len_bounds (ct1SentPBEncodedLen m)
  have hfits_hdr : FitsEvents M lim curSt
      (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen m))).length + 1)
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
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hcap0 : cap0 == BitVec.ofNat 64 bs0.length
  · have hcap_eq : cap0.toNat = bs0.length :=
      cap_toNat_eq_of_beq hcap0 (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit2 : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length + 10 < 2 ^ 62 := by
      rcases hfit with h | h <;> omega
    obtain ⟨hbound1, hlt1, hge0⟩ := reserveCap_one_bounds hcap_eq (by omega)
    have hres_lt64 : reserveCap cap0.toNat bs0.length 1 < 2 ^ 64 := by omega
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_320).base)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 => by
          have hfits_res : FitsEvents M lim curSt
              (doReserveEvents (DoReserveCall.mk v cap0 ptr0 bs0 1)) := by
            have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
              (BitVec.ofNat 64 (ct1SentPBEncodedLen m)) v cap0 ptr0 0#64 bs0 0x0a#8 hcap_eq hres_lt64
            rw [← hev_eq] at hfits_hdr
            exact ((fitsEvents_append M lim _ _ curSt).mp hfits_hdr).1
          refine step_unchunked_do_reserve7_call_placed hres A lim hdoReserve v cap0 ptr0 sp
            ((blkPl_319).base + 520#64) bs0 1 curSt hbound1 hfits_res
            (F := ct1SentPBPinnedAt A.repAlloc g msgA m ∗ S ∗ F)
            an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
            an an an (cs_step hcs hinv0)
            (by dsimp [S]; rw [← A.pool_of_vmPreserved hvm0, vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
          intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
          let newCap1 := BitVec.ofNat 64 (reserveCap cap0.toNat bs0.length 1)
          have hev_eq := doReserveOne_append_encodeVarintEvents_of_eq
            (BitVec.ofNat 64 (ct1SentPBEncodedLen m)) v cap0 ptr0 newPtr1 bs0 0x0a#8 hcap_eq hres_lt64
          have hfits_var : FitsEvents M lim
              (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap0 ptr0 bs0 1)) curSt)
              (encodeVarintEvents
                (EncodeVarintGhost.mk (BitVec.ofNat 64 (ct1SentPBEncodedLen m))
                  v newCap1 newPtr1 (bs0 ++ [0x0a#8]))) := by
            rw [← hev_eq] at hfits_hdr
            exact ((fitsEvents_append M lim _ _ curSt).mp hfits_hdr).2
          have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
          rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs0, vecHeader]
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 44#64)
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
                        (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen m))).length + 1)
                          cap0.toNat bs0.length)
                        hpcm hrunm hspm htrm hx19m hx20m hcsm
                        (Nat.le_trans hge0 hge1) (fun h => absurd h (by omega)) rfl))))))
  · have hcap0_f : (cap0 == BitVec.ofNat 64 bs0.length) = false := Bool.eq_false_iff.mpr hcap0
    have hlt0 : bs0.length < cap0.toNat :=
      lt_cap_toNat_of_beq_false hcap0_f hcap_le (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit44 : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ cap0.toNat ∨
        bs0.length + 1 + 10 < 2 ^ 62 := by
      rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
    have hev_eq := encodeVarintEvents_after_tag_of_lt
      (BitVec.ofNat 64 (ct1SentPBEncodedLen m)) v cap0 ptr0 bs0 0x0a#8 hlt0
    have hfits_var : FitsEvents M lim curSt
        (encodeVarintEvents
          (EncodeVarintGhost.mk (BitVec.ofNat 64 (ct1SentPBEncodedLen m))
            v cap0 ptr0 (bs0 ++ [0x0a#8]))) := by
      rwa [hev_eq]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 44#64)
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
                  (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen m))).length + 1)
                    cap0.toNat bs0.length)
                  hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 hpres1 rfl))))

/-! ## 2. Stage 2: Field 1 — `epoch: u64` -/

private theorem step_epoch_from_104_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 : State}
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (msgA v curCap curPtr epoch sp : BitVec 64) (bs1 : List (BitVec 8)) (curSt : M.σ)
    (hep : (epoch == 0#64) = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (u64Field1Bytes epoch).length ≤ curCap.toNat ∨
      bs1.length + 1 + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk epoch v curCap curPtr (bs1 ++ [0x08#8]))))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 104#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = epoch)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs1 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = entry + 132#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ cap2.toNat →
      (bs1.length + (u64Field1Bytes epoch).length ≤ curCap.toNat →
        cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ u64Field1Bytes epoch) ∗
          A.pool lim
            (M.stepEvents
              (encodeVarintEvents (EncodeVarintGhost.mk epoch v curCap curPtr (bs1 ++ [0x08#8])))
              curSt)
            sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  have hep_ne : epoch ≠ 0#64 := beq_eq_false_iff_ne.mp hep
  have hep_len := u64Field1Bytes_len_of_ne_zero hep_ne
  rw [vecU8At_open_one A.repAlloc v curCap curPtr bs1 hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
          ((blkPl_319).base + 132#64) (bs1 ++ [0x08#8]) curSt hvarint_fit hfits (F := F)
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

theorem step_ct1_epoch_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 s : State}
    (henc : subroutine_ok prog varint_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok prog reserve_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (msgA v cap1 ptr1 epoch sp : BitVec 64) (bs1 : List (BitVec 8)) (curSt : M.σ)
    (hfit : bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat ∨
      bs1.length + (u64Field1Bytes epoch).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (u64Field1Env cap1 bs1.length epoch))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 80#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (((msgA + 0x78#64) ↦₆₄ epoch) ∗
      vecU8At A.repAlloc v cap1 ptr1 bs1 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs₂ : List AllocEvent),
      sm.pc = entry + 132#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap1.toNat ≤ cap2.toNat →
      (bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat →
        cap2 = cap1 ∧ ptr2 = ptr1) →
      u64Field1Env cap1 bs1.length epoch evs₂ →
      SepWPp prog ret sm
        ((((msgA + 0x78#64) ↦₆₄ epoch) ∗
          vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ u64Field1Bytes epoch) ∗
          A.pool lim (M.stepEvents evs₂ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hstep104 := step_epoch_from_104_2_placed hres A lim hfn henc
  subst hP
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hep : epoch == 0#64
  · have hev0 : u64Field1Env cap1 bs1.length epoch [] := by
      simp only [u64Field1Env, u64Field1Step, hep, ↓reduceIte]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 132#64)
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
      simp only [u64Field1Env, u64Field1Step, hep_f, Bool.false_eq_true, ↓reduceIte,
        LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget.pushBytesStep_snd_eq]
    have hfits_ep : FitsEvents M lim curSt
        (pushBytesEvents ((encodeVarint epoch).length + 1) cap1.toNat bs1.length) :=
      hfits _ hev_ep
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := ((msgA + 0x78#64) ↦₆₄ epoch) ∗ A.pool lim curSt s ∗
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
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_320).base)
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
            refine step_unchunked_do_reserve7_call_placed hres A lim hdoReserve v cap1 ptr1 sp
              ((blkPl_319).base + 552#64) bs1 1 curSt hbound1 hfits_res
              (F := ((msgA + 0x78#64) ↦₆₄ epoch) ∗ F)
              an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
              an an an (cs_step hcs hinv0)
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
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 104#64)
            by_vm_steps (
              wp_steps
              exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
                (fun hvm1 hinv1 =>
                  hstep104 msgA v newCap1 newPtr1 epoch sp bs1
                    (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)) curSt)
                    hep_f hlt1 (Or.inr (by omega)) hfits_var
                    (F := ((msgA + 0x78#64) ↦₆₄ epoch) ∗ F)
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
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 104#64)
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
          (fun hvm0 hinv0 =>
            hstep104 msgA v cap1 ptr1 epoch sp bs1 curSt hep_f hlt1 hfit104 hfits_var
              (F := ((msgA + 0x78#64) ↦₆₄ epoch) ∗ F)
              an an an halign an an an an an (cs_step hcs hinv0)
              (by rw [← A.pool_of_vmPreserved hvm0, vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
              (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 hpres2 =>
                SepWPp.weaken_pre
                  (by rw [hev_eq]; exact Entails.of_eq (by sep_ac_rfl))
                  (hnext sm cap2 ptr2
                    (pushBytesEvents ((encodeVarint epoch).length + 1) cap1.toNat bs1.length)
                    hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 hpres2 hev_ep))))

/-! ## 3. Stage 3: Field 2 — `auth: Option<Authenticator>` -/

theorem step_ct1_auth_2_placed [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hfn : IsCt1Enc2PlacedProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {s0 s : State}
    (hauthEnc : subroutine_ok prog auth_pc
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A lim)))
    (gAuth : AuthenticatorPBGhost) (msgA v cap2 ptr2 sp : BitVec 64)
    (bs2 : List (BitVec 8)) (optAuth : Option AuthenticatorPB) (curSt : M.σ)
    (hfit : bs2.length + (optAuthField2Bytes optAuth).length ≤ cap2.toNat ∨
      bs2.length + (optAuthField2Bytes optAuth).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt (optAuthField2Env cap2 bs2.length optAuth))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 132#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (optAuthenticatorPBPinnedAt A.repAlloc gAuth (msgA + 0x48#64) optAuth ∗
      vecU8At A.repAlloc v cap2 ptr2 bs2 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs₃ : List AllocEvent),
      sm.pc = entry + 156#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      cap2.toNat ≤ cap3.toNat →
      (bs2.length + (optAuthField2Bytes optAuth).length ≤ cap2.toNat →
        cap3 = cap2 ∧ ptr3 = ptr2) →
      optAuthField2Env cap2 bs2.length optAuth evs₃ →
      SepWPp prog ret sm
        ((optAuthenticatorPBPinnedAt A.repAlloc gAuth (msgA + 0x48#64) optAuth ∗
          vecU8At A.repAlloc v cap3 ptr3 (bs2 ++ optAuthField2Bytes optAuth) ∗
          A.pool lim (M.stepEvents evs₃ curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  rcases hfn with ⟨H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases optAuth with
  | none =>
    rw [optAuthenticatorPBPinnedAt]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_319).base + 156#64)
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
        (LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget.AuthEncodeEnv
          ⟨msgA + 0x48#64, auth, v, cap2, ptr2, bs2⟩) :=
      fun evs hev => hfits evs ⟨msgA + 0x48#64, v, ptr2, bs2, rfl, hev⟩
    rw [optAuthenticatorPBPinnedAt, authenticatorPBPinnedAt]
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := msgA + 0x48#64)
      (cap := gAuth.rootKey.cap) (ptr := gAuth.rootKey.ptr) (bs := auth.rootKey)
      (F := vecU8At A.repAlloc (msgA + 0x48#64 + 24#64) gAuth.macKey.cap gAuth.macKey.ptr auth.macKey ∗
        vecU8At A.repAlloc v cap2 ptr2 bs2 ∗ A.pool lim curSt s ∗
        stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun _ hrkCap_lt _ => ?_
    have hcap_beq := cap_add_one_beq_zero_false hrkCap_lt
    have hcap_bne := cap_add_one_bne_zero_true hrkCap_lt
    rw [vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x48#64) gAuth.rootKey.cap gAuth.rootKey.ptr auth.rootKey,
      vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 314)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed an an (by simp only [wp_norm, arm64_norm, *])
        (fun hvm0 hinv0 => by
          refine step_unchunked_auth_encode_call_placed A lim hauthEnc (msgA + 0x48#64)
            gAuth auth v cap2 ptr2 sp ((blkPl_319).base + 156#64) bs2 curSt
            hfit hfits_auth (F := F)
            an an an halign an an an an (cs_step hcs hinv0)
            (by rw [← A.pool_of_vmPreserved hvm0, authenticatorPBPinnedAt,
                  vecU8At_eq_header_sep_buf A.repAlloc (msgA + 0x48#64), vecHeader]; try sep_ac_rfl) ?_
          intro s1 cap3 ptr3 evs₃ hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hge3 hpres3 hev3
          refine SepWPp.weaken_pre
            (by rw [optAuthenticatorPBPinnedAt, bs_append_optAuthField2Bytes_some]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext s1 cap3 ptr3 evs₃ hpc1 hrun1 hsp1 htr1
              (by rw [hcs01.1]; simp only [arm64_norm, *])
              (by rw [hcs01.2.1]; simp only [arm64_norm, *])
              hcs1 hge3 hpres3 ⟨msgA + 0x48#64, v, ptr2, bs2, rfl, hev3⟩)))

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlacedAuxBudget
