/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedAuxBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Proof of `encode<Authenticator> [local#2]` (Block 314)

Re-exports stages 1–2 from `EncodePlacedAuxBudget`, proves the `mac_key` stage
(`step_mk_2_placed`, `+256..+360`) and top-level `RustCliAllocBudget M` contracts for
block 314, and derives exact-capacity bridges for `PqRatchetState::encode_to_vec` (block 426).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPl_314
   extract_withLsCodeLoaded lsMemcpySym lsProg_314
   ls_subroutine_ok_of_block lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeBytesField encodeMessage)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack doReserveStackX reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost vecU8At_eq_header_sep_buf)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Varint
  (elem_len_after_reserve_not_ult elem_len_ult_spare_iff
   vecU8At_expose_slice vecU8At_pack_slice)
open CryptoVerification.SpqrV1.ProtoRepr
  (authenticatorPBEncodedLen authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ofNat_length_beq_zero_of_lt ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32)
open CryptoVerification.SpqrV1.Auth
  (AuthEncodePinnedGhost authEncodeStackOf authHeaderBytes authMacKeyBytes
   authMacKeyBytes_len_of_ne_empty authPBElemsAt authPBRestAt authRootKeyBytes
   authenticatorPBEncodedLen_eq_fields_len authenticatorPBPinnedAt_bounds_of_satisfies
   authenticatorPBPinnedAt_eq_elems bs0_append_encodeAuthMsg
   bs_append_authMacKeyBytes_of_empty bs_append_authMacKeyBytes_of_ne_empty
   cap_toNat_eq_of_beq encodeAuthMsg encodeAuthMsg_len_split
   lt_cap_toNat_of_beq_false reserveCap_one_bounds sp_sub_64_aligned
   vecU8At_bounds_of_satisfies)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (AuthEncodeCalleeSavedPlaced subroutine_ok_withAuthEncodeCSPlaced_placed_blk
   withAuthEncodeCSPlaced zext64_orr_1_32 zext64_trunc32_orr_1 zext64_trunc32_orr_100000001)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (blkPC_426 blkPl_426 encodeToVecCalleeStackOf stackAt_callee_eq_authEncode)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (pushByteStep_of_lt)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (do_reserve_7_placed_ok do_reserve_7_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget (encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
  (encode_varint4_det_placed_ok encode_varint4_det_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (AuthEncode2PinnedPlacedOkExt AuthEncode2PinnedPlacedOkX
   AuthEncode2PlacedOkExt AuthEncode2PlacedOkX AuthEncodeEnv
   authEncodeEnv_eq_nil_of_spare authEncodeEvents
   authEncodePinnedSpecOf authEncodePinnedSpecOfEnv authPinnedToUnpinned
   fitsEnv_authEncode_of_spare optBytesField1ByteTagStep pushBytesStep reserveStep
   reserveStep_of_need_doReserveEvents reserveStep_of_spare sepWPp_extract_vecU8At_bounds
   subroutine_ok_authEncodeExact_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Auth.Encode1Budget
  (authEncode_unpinned_of_pinned_placed fitsEnv_authEncode_iff fitsEvents_authEncode_iff
   fitsEvents_optBytesField1ByteTagStep_nonempty_iff fitsEvents_pushBytesStep_succ_iff
   optBytesField1ByteTagStep_of_isEmpty stepEvents_authEncode_eq
   stepEvents_optBytesField1ByteTagStep_nonempty stepEvents_pushBytesStep_succ)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1Budget
  (IsAuthEncodePlacedProg step_auth_epilogue_placed step_auth_push_mk_tag_placed)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedAuxBudget
  (encodeVarintEvents_snoc pushByteStep_of_eq pushBytesStep_det_snoc
   sepWP_done_tpidr_placed sepWPp_of_sepWP_cs_placed_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
  (step_ed_do_reserve7_call_placed step_ed_encode_varint_det_call_placed
   step_ed_memcpy_call_placed)

abbrev step_hdr_2_placed := @EncodePlacedAuxBudget.step_hdr_2_placed
abbrev step_rk_2_placed := @EncodePlacedAuxBudget.step_rk_2_placed

private theorem bv_sub_add_lit (x a b : BitVec 64) :
    x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

@[local arm64_norm] private theorem bv_pc_add_sub_cancel_2 (a b : BitVec 64) :
    a + (b - a) = b := by bv_omega

@[local arm64_norm] private theorem bv_bl_target_norm_2 (base off target : BitVec 64) :
    (base + off) + (target - base - off) = target := by bv_omega

@[local arm64_norm] private theorem bv_bl_entry_norm_2 (base target : BitVec 64) :
    base + (target - base - 0#64) = target := by bv_omega

/-! ## `mac_key` Stage (`+256..+360`) -/

private theorem step_mk_from_332_2_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_314 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64)
    (bs2 : List (BitVec 8)) (auth : AuthenticatorPB) (curSt : M.σ)
    (hmk_ne : auth.macKey.isEmpty = false) (hle : bs2.length + auth.macKey.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_314).base + 332#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length) (hx21 : s.readReg64 .x21 = mkPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs2.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs2 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool lim curSt s) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_314).base + 360#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_314 H) ret sm
        ((vecU8At A.repAlloc v curCap curPtr (bs2 ++ auth.macKey) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool lim curSt sm) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_314 H) ret s P Q Qp oom := by
  subst hP
  have hmk_ne_nil : auth.macKey ≠ [] := List.isEmpty_eq_false_iff.mp hmk_ne
  have hmk_pos : 0 < auth.macKey.length := List.length_pos_of_ne_nil hmk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs2)
    (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool lim curSt s ∗ F) (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A.repAlloc v curCap curPtr bs2 auth.macKey.length hle hcap_lt hptr_ne hmk_pos, authPBElemsAt]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := lsρ lsMemcpySym)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm1 hinv1
    rw [← A.pool_of_vmPreserved hvm1]
    refine step_ed_memcpy_call_placed hmemcpy
      (curPtr + BitVec.ofNat 64 bs2.length) mkPtr sp ((blkPl_314).base + 352#64) auth.macKey
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.repAlloc.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
        memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 auth.macKey.length)
          (curCap.toNat - bs2.length - auth.macKey.length) ∗
        ((authA + 8#64) ↦₆₄ rkPtr) ∗ ((authA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (rkPtr ↦ₛ auth.rootKey) ∗ ((authA + 32#64) ↦₆₄ mkPtr) ∗
        ((authA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ A.pool lim curSt _ ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by sep_ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hvm_mc
    rw [← A.pool_of_vmPreserved hvm_mc]
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs2.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 360#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm2 hinv2
      rw [← A.pool_of_vmPreserved hvm2]
      refine SepWPp.weaken_pre ?_
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2))
      rw [← vecU8At_pack_slice A.repAlloc v curCap curPtr bs2 auth.macKey hle hcap_lt hptr_ne hmk_ne_nil, authPBElemsAt]
      exact Entails.of_eq (by sep_ac_rfl)))

private theorem step_mk_from_280_2_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_314 H) (lsmpl.base 292)
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_314 H) (lsmpl.base 320)
      (withAuthEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_314 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64)
    (bs1 : List (BitVec 8)) (auth : AuthenticatorPB) (curSt : M.σ)
    (hmk_ne : auth.macKey.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (authMacKeyBytes auth).length ≤ curCap.toNat ∨
      bs1.length + (authMacKeyBytes auth).length + 10 < 2 ^ 62)
    (hfits_v : FitsEvents M lim curSt
      (pushBytesEvents (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length
        curCap.toNat (bs1.length + 1)))
    (hfits_r : FitsEvents M lim
      (M.stepEvents
        (pushBytesEvents (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length
          curCap.toNat (bs1.length + 1)) curSt)
      (reserveStep
        (pushBytesStep (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length
          curCap.toNat (bs1.length + 1)).1
        (bs1.length + 1 + (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length)
        auth.macKey.length).2)
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_314).base + 280#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = mkPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs1 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_314).base + 360#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap3.toNat →
      (bs1.length + (authMacKeyBytes auth).length ≤ curCap.toNat → cap3 = curCap ∧ ptr3 = curPtr) →
      cap3.toNat =
        (reserveStep
          (pushBytesStep (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length
            curCap.toNat (bs1.length + 1)).1
          (bs1.length + 1 + (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length)
          auth.macKey.length).1 →
      SepWPp (lsProg_314 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3 (bs1 ++ authMacKeyBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗
          A.pool lim
            (M.stepEvents
              (reserveStep
                (pushBytesStep (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length
                  curCap.toNat (bs1.length + 1)).1
                (bs1.length + 1 + (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length)
                auth.macKey.length).2
              (M.stepEvents
                (pushBytesEvents (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length
                  curCap.toNat (bs1.length + 1)) curSt)) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_314 H) ret s P Q Qp oom := by
  have hstep332 := step_mk_from_332_2_placed A lim H hmemcpy
  have hfn2 : IsAuthEncodePlacedProg (lsProg_314 H) blkPl_314 := Or.inr ⟨H, rfl, rfl⟩
  have hmk_len := authMacKeyBytes_len_of_ne_empty auth hmk_ne
  let mkVlen := (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length
  refine step_auth_push_mk_tag_placed A.repAlloc hfn2 v curCap curPtr mkPtr sp bs1 auth hlt
    (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1 hvm01
  rw [← A.pool_of_vmPreserved hvm01]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 292)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm12 hinv1
    rw [← A.pool_of_vmPreserved hvm12]
    have hvarint_fit : (bs1 ++ [0x12#8]).length + mkVlen ≤ curCap.toNat ∨
        (bs1 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
    have hfits_ev : FitsEvents M lim curSt
        (encodeVarintEvents
          (EncodeVarintGhost.mk (BitVec.ofNat 64 auth.macKey.length)
            v curCap curPtr (bs1 ++ [0x12#8]))) := by
      rw [encodeVarintEvents_snoc]; exact hfits_v
    refine step_ed_encode_varint_det_call_placed A lim henc
      (BitVec.ofNat 64 auth.macKey.length) v curCap curPtr sp ((blkPl_314).base + 312#64)
      (bs1 ++ [0x12#8]) curSt hvarint_fit hfits_ev (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by sep_ac_rfl) ?_
    intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2 hdet2
    rw [pushBytesStep_det_snoc] at hdet2
    rw [encodeVarintEvents_snoc]
    let bs2 := (bs1 ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 auth.macKey.length)
    let st_v := M.stepEvents (pushBytesEvents mkVlen curCap.toNat (bs1.length + 1)) curSt
    have hbs2_len_eq : bs1.length + 1 + mkVlen = bs2.length := by
      dsimp [bs2, mkVlen]; rw [List.length_append, List.length_append, List.length_singleton]
    have hbs2_tot : bs2.length + auth.macKey.length = bs1.length + (authMacKeyBytes auth).length := by
      rw [← hbs2_len_eq, hmk_len]; omega
    have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs12.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = mkPtr := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := A.pool lim st_v s2 ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ authPBElemsAt authA rkPtr mkPtr auth ∗ F)
      (by dsimp [bs2, st_v, mkVlen]; sep_ac_rfl) fun hle2 hcap2_lt _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap2 ptr2 bs2, vecHeader]
    have hmk_lt63 : auth.macKey.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
    by_cases hneed : cap2.toNat < bs2.length + auth.macKey.length
    · have hfit_mk : bs2.length + auth.macKey.length < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 auth.macKey.length) = true :=
        (elem_len_ult_spare_iff hle2 hcap2_lt hmk_lt63).mpr hneed
      obtain ⟨hnot_ult, hle3, hge3, hbound_mk⟩ := elem_len_after_reserve_not_ult hfit_mk hneed
      have hrs_eq := reserveStep_of_need_doReserveEvents v cap2 ptr2 bs2 auth.macKey.length (by omega)
      have hfits_doRes : FitsEvents M lim st_v
          (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 auth.macKey.length)) := by
        have h' := hfits_r
        rw [← hdet2, hbs2_len_eq, hrs_eq] at h'
        exact h'
      apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm2 hinv2
        rw [← A.pool_of_vmPreserved hvm2]
        refine step_ed_do_reserve7_call_placed hres A lim hdoReserve v cap2 ptr2 sp
          ((blkPl_314).base + 592#64) bs2 auth.macKey.length st_v hbound_mk hfits_doRes
          (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
        intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
        let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length auth.macKey.length)
        change (BitVec.ofNat 64 auth.macKey.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true at hnot_ult
        have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
        have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs23.2.1]; simp only [arm64_norm, *]
        have hx21_3 : s3.readReg64 .x21 = mkPtr := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v cap3 ptr3 bs2, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 332#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hvm3 hinv3
          rw [← A.pool_of_vmPreserved hvm3]
          refine hstep332 v cap3 ptr3 authA rkPtr mkPtr sp bs2 auth _ hmk_ne hle3
            (F := stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
          intro sm hpcm hrunm hspm htrm hcsm
          have hcap3_det : cap3.toNat =
              (reserveStep (pushBytesStep mkVlen curCap.toNat (bs1.length + 1)).1
                (bs1.length + 1 + mkVlen) auth.macKey.length).1 := by
            rw [← hdet2, hbs2_len_eq, hrs_eq]
            dsimp [cap3]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hst_det :
              M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 auth.macKey.length)) st_v =
              M.stepEvents
                (reserveStep (pushBytesStep mkVlen curCap.toNat (bs1.length + 1)).1
                  (bs1.length + 1 + mkVlen) auth.macKey.length).2 st_v := by
            rw [← hdet2, hbs2_len_eq, hrs_eq]
          refine SepWPp.weaken_pre
            (by dsimp [bs2, st_v, mkVlen] at hst_det ⊢
                rw [bs_append_authMacKeyBytes_of_ne_empty bs1 auth hmk_ne, hst_det]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
              (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega)) hcap3_det)))
    · have hle_fast : bs2.length + auth.macKey.length ≤ cap2.toNat := by omega
      have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 auth.macKey.length) = false :=
        Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hmk_lt63).mp h)
      have hrs_eq : reserveStep (pushBytesStep mkVlen curCap.toNat (bs1.length + 1)).1
          (bs1.length + 1 + mkVlen) auth.macKey.length = (cap2.toNat, []) := by
        rw [← hdet2, hbs2_len_eq]; exact reserveStep_of_spare hle_fast
      have hpres_all : bs1.length + (authMacKeyBytes auth).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 332#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm2 hinv2
        rw [← A.pool_of_vmPreserved hvm2]
        refine hstep332 v cap2 ptr2 authA rkPtr mkPtr sp bs2 auth st_v hmk_ne hle_fast
          (F := stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hcsm
        refine SepWPp.weaken_pre
          (by dsimp [bs2, st_v, mkVlen] at hrs_eq ⊢
              rw [bs_append_authMacKeyBytes_of_ne_empty bs1 auth hmk_ne, hrs_eq]
              simp only [AllocCostModel.stepEvents_nil]
              exact Entails.of_eq (by sep_ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hcsm hge2 hpres_all
            (by rw [hrs_eq]))))

/-- `mac_key` field stage (`+256..+360`) on block 314. -/
theorem step_mk_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_314 H) (lsmpl.base 292)
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_314 H) (lsmpl.base 320)
      (withAuthEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_314 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v cap2 ptr2 authA rkPtr mkPtr sp : BitVec 64)
    (bs2 : List (BitVec 8)) (auth : AuthenticatorPB) (st2 : M.σ)
    (hmk_lt : auth.macKey.length < 2 ^ 63)
    (hfit : bs2.length + (authMacKeyBytes auth).length ≤ cap2.toNat ∨
      bs2.length + (authMacKeyBytes auth).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim st2 (optBytesField1ByteTagStep cap2.toNat bs2.length auth.macKey).2)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_314).base + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = authA) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v cap2 ptr2 bs2 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool lim st2 s ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_314).base + 360#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm → cap2.toNat ≤ cap3.toNat →
      (bs2.length + (authMacKeyBytes auth).length ≤ cap2.toNat → cap3 = cap2 ∧ ptr3 = ptr2) →
      cap3.toNat = (optBytesField1ByteTagStep cap2.toNat bs2.length auth.macKey).1 →
      SepWPp (lsProg_314 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3 (bs2 ++ authMacKeyBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗
          A.pool lim (M.stepEvents (optBytesField1ByteTagStep cap2.toNat bs2.length auth.macKey).2 st2) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_314 H) ret s P Q Qp oom := by
  have hstep280 := step_mk_from_280_2_placed hres A lim H henc hdoReserve hmemcpy
  subst hP
  have ⟨hmk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := auth.macKey) (by omega)
  cases hmk : auth.macKey.isEmpty
  · have hmk_len := authMacKeyBytes_len_of_ne_empty auth hmk
    let mkVlen := (encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length
    obtain ⟨hfits_s1, hfits_s2⟩ :=
      (fitsEvents_optBytesField1ByteTagStep_nonempty_iff (M := M) (lim := lim) (st := st2) hmk).mp hfits
    obtain ⟨hfits_b1, hfits_v⟩ :=
      (fitsEvents_pushBytesStep_succ_iff mkVlen cap2.toNat bs2.length).mp hfits_s1
    have hst_opt := stepEvents_optBytesField1ByteTagStep_nonempty (M := M) st2
      (cap := cap2.toNat) (len := bs2.length) hmk
    have hst_s1 := stepEvents_pushBytesStep_succ st2 mkVlen cap2.toNat bs2.length
    have hopt_fst : (optBytesField1ByteTagStep cap2.toNat bs2.length auth.macKey).1 =
        (reserveStep (pushBytesStep (mkVlen + 1) cap2.toNat bs2.length).1
          (bs2.length + 1 + mkVlen) auth.macKey.length).1 := by
      simp only [optBytesField1ByteTagStep, hmk, Bool.false_eq_true, ↓reduceIte, mkVlen]
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool lim st2 s ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by sep_ac_rfl) fun hcap2_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap2 ptr2 bs2, vecHeader, authPBElemsAt]
    by_cases hcap2 : cap2 == BitVec.ofNat 64 bs2.length
    · have hcap_eq : cap2.toNat = bs2.length :=
        cap_toNat_eq_of_beq hcap2 (Nat.lt_of_le_of_lt hcap2_le (BitVec.isLt cap2))
      have hfit2 : bs2.length + (authMacKeyBytes auth).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      have hpb := pushByteStep_of_eq v cap2 ptr2 bs2 hcap_eq
      have hfits_res : FitsEvents M lim st2 (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)) := by
        simpa [hpb] using hfits_b1
      apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm0 hinv0
        rw [← A.pool_of_vmPreserved hvm0]
        refine step_ed_do_reserve7_call_placed hres A lim hdoReserve v cap2 ptr2 sp
          ((blkPl_314).base + 560#64) bs2 1 st2 hbound1 hfits_res
          (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader, authPBElemsAt]; sep_ac_rfl) ?_
        intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
        let newCap1 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length 1)
        have hnewCap1_toNat : newCap1.toNat = (pushByteStep cap2.toNat bs2.length).1 := by
          dsimp [newCap1]; rw [hpb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hfits_v' : FitsEvents M lim
            (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)) st2)
            (pushBytesEvents mkVlen newCap1.toNat (bs2.length + 1)) := by
          rw [hnewCap1_toNat]; simpa [hpb] using hfits_v
        have hfits_r' : FitsEvents M lim
            (M.stepEvents (pushBytesEvents mkVlen newCap1.toNat (bs2.length + 1))
              (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)) st2))
            (reserveStep (pushBytesStep mkVlen newCap1.toNat (bs2.length + 1)).1
              (bs2.length + 1 + mkVlen) auth.macKey.length).2 := by
          have h' := hfits_s2
          rw [hst_s1] at h'
          simpa [pushBytesStep, hnewCap1_toNat, hpb, mkVlen] using h'
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs2, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 280#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hvm1 hinv1
          rw [← A.pool_of_vmPreserved hvm1]
          refine hstep280 v newCap1 newPtr1 authA rkPtr mkPtr sp bs2 auth _ hmk hlt1
            (Or.inr hfit2) hfits_v' hfits_r' (F := F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
          intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm hge2 _ hdet2
          have hdet_all : cap3.toNat = (optBytesField1ByteTagStep cap2.toNat bs2.length auth.macKey).1 := by
            rw [hopt_fst]; simpa [pushBytesStep, hnewCap1_toNat, mkVlen] using hdet2
          have hst_all :
              M.stepEvents
                (reserveStep (pushBytesStep mkVlen newCap1.toNat (bs2.length + 1)).1
                  (bs2.length + 1 + mkVlen) auth.macKey.length).2
                (M.stepEvents (pushBytesEvents mkVlen newCap1.toNat (bs2.length + 1))
                  (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)) st2)) =
              M.stepEvents (optBytesField1ByteTagStep cap2.toNat bs2.length auth.macKey).2 st2 := by
            rw [hst_opt]; dsimp only
            rw [hst_s1]; simp only [pushBytesStep, hnewCap1_toNat, hpb, mkVlen]
          refine SepWPp.weaken_pre (by rw [hst_all]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
              (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)) hdet_all)))
    · have hlt1 : bs2.length < cap2.toNat :=
        lt_cap_toNat_of_beq_false (Bool.eq_false_iff.mpr hcap2) hcap2_le
          (Nat.lt_of_le_of_lt hcap2_le (BitVec.isLt cap2))
      have hpb := pushByteStep_of_lt hlt1
      have hfits_v' : FitsEvents M lim st2 (pushBytesEvents mkVlen cap2.toNat (bs2.length + 1)) := by
        simpa [hpb] using hfits_v
      have hfits_r' : FitsEvents M lim
          (M.stepEvents (pushBytesEvents mkVlen cap2.toNat (bs2.length + 1)) st2)
          (reserveStep (pushBytesStep mkVlen cap2.toNat (bs2.length + 1)).1
            (bs2.length + 1 + mkVlen) auth.macKey.length).2 := by
        have h' := hfits_s2
        rw [hst_s1] at h'
        simpa [pushBytesStep, hpb, mkVlen] using h'
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 280#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm0 hinv0
        rw [← A.pool_of_vmPreserved hvm0]
        refine hstep280 v cap2 ptr2 authA rkPtr mkPtr sp bs2 auth st2 hmk hlt1 hfit
          hfits_v' hfits_r' (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader, authPBElemsAt]; try sep_ac_rfl) ?_
        intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm hge2 hpres2 hdet2
        have hdet_all : cap3.toNat = (optBytesField1ByteTagStep cap2.toNat bs2.length auth.macKey).1 := by
          rw [hopt_fst]; simpa [pushBytesStep, hpb, mkVlen] using hdet2
        have hst_all :
            M.stepEvents
              (reserveStep (pushBytesStep mkVlen cap2.toNat (bs2.length + 1)).1
                (bs2.length + 1 + mkVlen) auth.macKey.length).2
              (M.stepEvents (pushBytesEvents mkVlen cap2.toNat (bs2.length + 1)) st2) =
            M.stepEvents (optBytesField1ByteTagStep cap2.toNat bs2.length auth.macKey).2 st2 := by
          rw [hst_opt]; dsimp only
          rw [hst_s1]; simp only [pushBytesStep, hpb, AllocCostModel.stepEvents_nil, mkVlen]
        refine SepWPp.weaken_pre (by rw [hst_all]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm hge2 hpres2 hdet_all))
  · have hopt_emp := optBytesField1ByteTagStep_of_isEmpty (cap := cap2.toNat) (len := bs2.length) hmk
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 360#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      refine SepWPp.weaken_pre
        (by rw [bs_append_authMacKeyBytes_of_empty bs2 auth hmk, hopt_emp]
            simp only [AllocCostModel.stepEvents_nil]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hopt_emp])))

/-! ## Top-Level Contracts (Block 314) -/

/-- `SepWPp` correctness for placed `encode<Authenticator> [local#2]` (block 314). -/
theorem authEncode2_gen_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {x : AuthEncodePinnedGhost} {st0 : M.σ}
    {R : SepProp} {s0 : State} {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (henc : subroutine_ok (lsProg_314 H) (lsmpl.base 292)
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_314 H) (lsmpl.base 320)
      (withAuthEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_314 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hpc : s0.pc = (blkPl_314).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (authEncodePinnedSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp (lsProg_314 H) (s0.readReg64 .lr) s0 P
      (fun s' Q =>
        ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (authEncodePinnedSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      Qp oom := by
  have hfn2 : IsAuthEncodePlacedProg (lsProg_314 H) blkPl_314 := Or.inr ⟨H, rfl, rfl⟩
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre
  dsimp only [authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hlen_fit, hfits_env⟩, hpre_mem⟩ := hpre_pure
  have hfits_all := (fitsEvents_authEncode_iff (authPinnedToUnpinned x)).mp
    ((fitsEnv_authEncode_iff (authPinnedToUnpinned x)).mp hfits_env)
  dsimp only [authPinnedToUnpinned] at hfits_all
  obtain ⟨hfits1, hfits2, hfits3⟩ := hfits_all
  have hst_all := stepEvents_authEncode_eq st0 (authPinnedToUnpinned x)
  dsimp only [authPinnedToUnpinned] at hst_all
  obtain ⟨hrk_lt, hmk_lt, hrk_cap0, hmk_cap0⟩ :=
    authenticatorPBPinnedAt_bounds_of_satisfies (A := A.repAlloc) (g := x.g) (authA := x.authA) (auth := x.auth)
      (F := vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s0 ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; sep_ac_rfl)
  obtain ⟨hcap_le, hcap_lt, _⟩ :=
    vecU8At_bounds_of_satisfies (A := A.repAlloc) (v := x.v) (cap := x.cap) (ptr := x.ptr) (bs := x.bs)
      (F := authenticatorPBPinnedAt A.repAlloc x.g x.authA x.auth ∗ A.pool lim st0 s0 ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; sep_ac_rfl)
  have hpre_rewritten : s0.mem ⊨ ((vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      authPBElemsAt x.authA x.g.rootKey.ptr x.g.macKey.ptr x.auth ∗
      A.pool lim st0 s0 ∗ stackAt s0.sp (authEncodeStackOf resStack)) ∗
      authPBRestAt A.repAlloc x.g x.authA x.auth) ∗ R := by
    rw [authenticatorPBPinnedAt_eq_elems A.repAlloc x.g x.authA x.auth hrk_cap0 hmk_cap0] at hpre_mem
    convert hpre_mem using 1; sep_ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have htot_split := encodeAuthMsg_len_split x.auth
  have htot_len := authenticatorPBEncodedLen_eq_fields_len x.auth
  have hlen_pb_lt : authenticatorPBEncodedLen x.auth < 2 ^ 64 := by
    rw [htot_len]; change (authRootKeyBytes x.auth).length + (authMacKeyBytes x.auth).length < 2 ^ 64
    rcases hlen_fit with h | h <;> omega
  have hfit_hdr : x.bs.length + (authHeaderBytes x.auth).length ≤ x.cap.toNat ∨
      x.bs.length + (authHeaderBytes x.auth).length + 10 < 2 ^ 62 := by
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  let Ssaved := ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    authPBRestAt A.repAlloc x.g x.authA x.auth
  refine step_hdr_2_placed hres A lim H henc hdoReserve x.v x.cap x.ptr x.authA x.g.rootKey.ptr x.g.macKey.ptr
    s0.sp x.bs x.auth st0 hcap_le hrk_lt hmk_lt hlen_pb_lt hfit_hdr hfits1
    (F := authPBRestAt A.repAlloc x.g x.authA x.auth)
    hpc hrun rfl halign rfl hx0 hx1 (AuthEncodeCalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hge1 hpres1 hdet1
  let hdrVlen := (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen x.auth))).length
  have hbs1_len : (x.bs ++ authHeaderBytes x.auth).length = x.bs.length + 1 + hdrVlen := by
    simp only [authHeaderBytes, List.length_append, List.length_singleton, hdrVlen]; omega
  have hfit_rk : (x.bs ++ authHeaderBytes x.auth).length + (authRootKeyBytes x.auth).length ≤ cap1.toNat ∨
      (x.bs ++ authHeaderBytes x.auth).length + (authRootKeyBytes x.auth).length + 10 < 2 ^ 62 := by
    rw [List.length_append]; rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  have hfits2' : FitsEvents M lim
      (M.stepEvents (pushBytesStep (hdrVlen + 1) x.cap.toNat x.bs.length).2 st0)
      (optBytesField1ByteTagStep cap1.toNat (x.bs ++ authHeaderBytes x.auth).length x.auth.rootKey).2 := by
    rw [hdet1, hbs1_len]; exact hfits2
  refine step_rk_2_placed hres A lim H henc hdoReserve hmemcpy x.v cap1 ptr1 x.authA x.g.rootKey.ptr x.g.macKey.ptr
    s0.sp (x.bs ++ authHeaderBytes x.auth) x.auth _ hrk_lt hfit_rk hfits2' (F := Ssaved)
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 (by dsimp [Ssaved]; sep_ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hcs2 hge2 hpres2 hdet2
  have hbs2_len : ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth).length =
      x.bs.length + 1 + hdrVlen + (encodeBytesField 1#32 x.auth.rootKey).length := by
    rw [List.length_append, hbs1_len]; rfl
  have hfit_mk : ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth).length +
      (authMacKeyBytes x.auth).length ≤ cap2.toNat ∨
      ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth).length +
        (authMacKeyBytes x.auth).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_append]; rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  have hfits3' : FitsEvents M lim
      (M.stepEvents (optBytesField1ByteTagStep cap1.toNat (x.bs ++ authHeaderBytes x.auth).length x.auth.rootKey).2
        (M.stepEvents (pushBytesStep (hdrVlen + 1) x.cap.toNat x.bs.length).2 st0))
      (optBytesField1ByteTagStep cap2.toNat ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth).length x.auth.macKey).2 := by
    rw [hdet2, hdet1, hbs1_len, hbs2_len]; exact hfits3
  refine step_mk_2_placed hres A lim H henc hdoReserve hmemcpy x.v cap2 ptr2 x.authA x.g.rootKey.ptr x.g.macKey.ptr
    s0.sp ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth) x.auth _ hmk_lt hfit_mk hfits3' (F := Ssaved)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hcs2 (by sep_ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hcs3 hge3 hpres3 _
  refine step_auth_epilogue_placed hres hfn2 s0.sp
    (F := vecU8At A.repAlloc x.v cap3 ptr3 (((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth) ++ authMacKeyBytes x.auth) ∗
      authPBElemsAt x.authA x.g.rootKey.ptr x.g.macKey.ptr x.auth ∗
      A.pool lim _ s3 ∗ authPBRestAt A.repAlloc x.g x.authA x.auth)
    hpc3 hrun3 hsp3 halign htr3 hcs3 (by dsimp [Ssaved]; sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hcc _ hvm_ep
  refine ⟨fun hm => ?_, hspf, hcc⟩
  have hge_all : x.cap.toNat ≤ cap3.toNat := Nat.le_trans hge1 (Nat.le_trans hge2 hge3)
  have hpres_all : x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat → cap3 = x.cap ∧ ptr3 = x.ptr := by
    intro hfit_cap; obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
    obtain ⟨hc2, hp2⟩ := hpres2 (by rw [hc1, List.length_append]; omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by rw [hc2, hc1, List.length_append, List.length_append]; omega)
    exact ⟨hc3.trans (hc2.trans hc1), hp3.trans (hp2.trans hp1)⟩
  have hst_final :
      M.stepEvents (optBytesField1ByteTagStep cap2.toNat ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth).length x.auth.macKey).2
        (M.stepEvents (optBytesField1ByteTagStep cap1.toNat (x.bs ++ authHeaderBytes x.auth).length x.auth.rootKey).2
          (M.stepEvents (pushBytesStep (hdrVlen + 1) x.cap.toNat x.bs.length).2 st0)) =
      M.stepEvents (authEncodeEvents (authPinnedToUnpinned x)) st0 := by
    rw [hdet2, hdet1, hbs1_len, hbs2_len]; exact hst_all.symm
  dsimp only [authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv]
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨authEncodeEvents (authPinnedToUnpinned x), cap3, ptr3, ?_⟩
  have hpure1 : (x.cap.toNat ≤ cap3.toNat ∧
      (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat → cap3 = x.cap ∧ ptr3 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  have hpure2 : AuthEncodeEnv (authPinnedToUnpinned x) (authEncodeEvents (authPinnedToUnpinned x)) = True :=
    eq_true rfl
  rw [hpure1, hpure2, pure_true, emp_sepConj,
    authenticatorPBPinnedAt_eq_elems A.repAlloc x.g x.authA x.auth hrk_cap0 hmk_cap0,
    ← bs0_append_encodeAuthMsg x.bs x.auth]
  rw [hst_final, ← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents (authEncodeEvents (authPinnedToUnpinned x)) st0) hvm_ep] at hm
  convert hm using 1; sep_ac_rfl

theorem auth_encode_2_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    AuthEncode2PinnedPlacedOkExt A lim H := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := authEncode2_gen_placed_ok (by decide)
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk (callerProg := lsProg_314 H) s0 hcl0
      (encode_varint4_det_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk (callerProg := lsProg_314 H) s0 hcl0
      (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem auth_encode_2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    AuthEncode2PlacedOkExt A lim H :=
  authEncode_unpinned_of_pinned_placed
    (auth_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem auth_encode_2_pinned_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    AuthEncode2PinnedPlacedOkX A lim H := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := authEncode2_gen_placed_ok (by decide)
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk (callerProg := lsProg_314 H) s0 hcl0
      (encode_varint4_det_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk (callerProg := lsProg_314 H) s0 hcl0
      (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem auth_encode_2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    AuthEncode2PlacedOkX A lim H :=
  authEncode_unpinned_of_pinned_placed
    (auth_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

/-! ## Exact-Capacity Callee Bridges for `EncodeToVec` (Block 426) -/

section EncodeToVecBridge

open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget (authEncodeExactSpecOf)

theorem etv_authEncode_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} {call_pc : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hauth_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [authEncodeExactSpecOf] at hpre
  rw [stackAt_callee_eq_authEncode hres s.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfit⟩, hm⟩
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 64
  let xg : AuthEncodePinnedGhost := ⟨x.authA, x.g, x.auth, x.v, x.cap, x.ptr, x.bs⟩
  have hfit_xg : xg.bs.length + (encodeAuthMsg xg.auth).length ≤ xg.cap.toNat := hfit
  have hfit_unpinned : (authPinnedToUnpinned xg).bs.length +
      (encodeAuthMsg (authPinnedToUnpinned xg).auth).length ≤
      (authPinnedToUnpinned xg).cap.toNat := hfit
  have hfits_env : FitsEnv M lim st (AuthEncodeEnv (authPinnedToUnpinned xg)) :=
    fitsEnv_authEncode_of_spare hfit_unpinned
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf resStack A lim)).pre
      (xg, st) s ∗ (F_rem ∗ R) := by
    dsimp only [withLsCodeLoaded, authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv, encodeAuthMsg, xg]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inl hfit, hfits_env⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; sep_ac_rfl)) hm
  refine (hauth_ok.to_outcome (xg, st) (F_rem ∗ R) s hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv] at hpost
    dsimp only [withLsCodeLoaded, authEncodeExactSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨htrf, hpost⟩ := hpost
    refine ⟨htrf, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, cap', ptr', hpost⟩
    have hq' : sf.mem ⊨ ⌜xg.cap.toNat ≤ cap'.toNat ∧
        (xg.bs.length + (encodeAuthMsg xg.auth).length ≤ xg.cap.toNat →
          cap' = xg.cap ∧ ptr' = xg.ptr)⌝ ∗
        (⌜AuthEncodeEnv (authPinnedToUnpinned xg) evs⌝ ∗
          (authenticatorPBPinnedAt A.repAlloc xg.g xg.authA xg.auth ∗
            vecU8At A.repAlloc xg.v cap' ptr' (xg.bs ++ encodeAuthMsg xg.auth) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp (authEncodeStackOf resStack) ∗ F_rem ∗ R)) := by
      convert hpost using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hq'
    obtain ⟨⟨_, hpres⟩, hev, hmem'⟩ := hq'
    obtain ⟨hcap_eq, hptr_eq⟩ := hpres hfit_xg
    have hevs_nil := authEncodeEnv_eq_nil_of_spare hfit_unpinned hev
    subst hevs_nil
    dsimp only [xg, encodeAuthMsg] at hcap_eq hptr_eq hmem'
    subst hcap_eq hptr_eq
    simp only [AllocCostModel.stepEvents_nil] at hmem'
    rw [stackAt_callee_eq_authEncode hres s.sp]
    convert hmem' using 1; dsimp only [F_rem, authEncodeStackOf]; sep_ac_rfl
  · dsimp only [withLsCodeLoaded, authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeLoaded, authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeLoaded, authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem etv_authEncode_exact_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStack A lim)) :=
  etv_authEncode_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block (auth_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc))

theorem etv_authEncode_exact_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStackX A lim)) :=
  etv_authEncode_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block (auth_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc))

end EncodeToVecBridge

end LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedBudget
