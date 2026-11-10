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
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Stages 1–2 of `encode<Authenticator> [local#2]` (Block 314)

Proves the `[LibsignalPlacement]` header (`step_hdr_2_placed`, `+0..+152`) and
`root_key` (`step_rk_2_placed`, `+152..+256`) stage lemmas for `encode<Authenticator> [local#2]`
(block 314), consumed by `EncodePlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedAuxBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl lsρ lsMemcpySym blkPl_314 lsProg_314)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost StepInvPlaced vecU8At_eq_header_sep_buf)
open CryptoVerification.SpqrV1.Varint
  (elem_len_after_reserve_not_ult elem_len_ult_spare_iff
   vecU8At_expose_slice vecU8At_pack_slice)
open CryptoVerification.SpqrV1.ProtoRepr (authenticatorPBEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ofNat_length_beq_zero_of_lt ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32)
open CryptoVerification.SpqrV1.Auth
  (authEncodeStackOf authHeaderBytes authHeaderBytes_len_bounds authPBElemsAt
   authRootKeyBytes authRootKeyBytes_len_of_ne_empty
   bs0_append_authHeaderBytes bs_append_authRootKeyBytes_of_empty
   bs_append_authRootKeyBytes_of_ne_empty
   cap_toNat_eq_of_beq lt_cap_toNat_of_beq_false reserveCap_one_bounds
   sp_sub_64_aligned stackAt_authEncode)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (AuthEncodeCalleeSavedPlaced withAuthEncodeCSPlaced
   zext64_orr_1_32 zext64_trunc32_orr_1 zext64_trunc32_orr_100000001)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (pushByteStep_of_lt)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget (encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (optBytesField1ByteTagStep pushBytesStep reserveStep
   reserveStep_of_need_doReserveEvents reserveStep_of_spare
   reserveStep_one_eq_pushByteStep sepWPp_extract_vecU8At_bounds)
open LibsignalBinary.Proofs.SpqrV1.Auth.Encode1Budget
  (fitsEvents_optBytesField1ByteTagStep_nonempty_iff fitsEvents_pushBytesStep_succ_iff
   optBytesField1ByteTagStep_of_isEmpty
   stepEvents_optBytesField1ByteTagStep_nonempty stepEvents_pushBytesStep_succ)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1Budget
  (IsAuthEncodePlacedProg auth_pushBytesStep_eq_base
   step_auth_len_placed step_auth_push_hdr_placed step_auth_push_rk_tag_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
  (step_ed_do_reserve7_call_placed step_ed_encode_varint_det_call_placed
   step_ed_memcpy_call_placed)

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

theorem sepWPp_of_sepWP_cs_placed_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext hvmp (StepInvPlaced.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem sepWP_done_tpidr_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨htp, hpost⟩

theorem encodeVarintEvents_snoc (val v cap ptr : BitVec 64) (bs : List (BitVec 8)) (b : BitVec 8) :
    encodeVarintEvents (EncodeVarintGhost.mk val v cap ptr (bs ++ [b])) =
      pushBytesEvents (encodeVarint val).length cap.toNat (bs.length + 1) := by
  simp only [encodeVarintEvents, List.length_append, List.length_singleton]

theorem pushBytesStep_det_snoc (val : BitVec 64) (cap : Nat) (bs : List (BitVec 8)) (b : BitVec 8) :
    (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget.pushBytesStep
      (encodeVarint val).length cap (bs ++ [b]).length).1 =
    (pushBytesStep (encodeVarint val).length cap (bs.length + 1)).1 := by
  rw [← auth_pushBytesStep_eq_base, List.length_append, List.length_singleton]

theorem pushByteStep_of_eq (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (heq : cap.toNat = bs.length) :
    pushByteStep cap.toNat bs.length =
      (reserveCap cap.toNat bs.length 1, doReserveEvents (DoReserveCall.mk v cap ptr bs 1)) := by
  rw [← reserveStep_one_eq_pushByteStep, reserveStep_of_need_doReserveEvents v cap ptr bs 1 (by omega)]

/-! ## Header Stage (`+0..+152`) -/

private theorem step_hdr_from_44_2_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_314 H) (lsmpl.base 292)
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64)
    (bs0 : List (BitVec 8)) (auth : AuthenticatorPB) (curSt : M.σ)
    (hlt : bs0.length < curCap.toNat) (hrk_lt : auth.rootKey.length < 2 ^ 63)
    (hmk_lt : auth.macKey.length < 2 ^ 63) (hlen_fit : authenticatorPBEncodedLen auth < 2 ^ 64)
    (hfit : bs0.length + (authHeaderBytes auth).length ≤ curCap.toNat ∨ bs0.length + 1 + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (pushBytesEvents (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length
        curCap.toNat (bs0.length + 1)))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_314).base + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs0.length)
    (hx19 : s.readReg64 .x19 = v) (hx21 : s.readReg64 .x21 = authA)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs0 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_314).base + 152#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap1.toNat →
      (bs0.length + (authHeaderBytes auth).length ≤ curCap.toNat → cap1 = curCap ∧ ptr1 = curPtr) →
      cap1.toNat =
        (pushBytesStep (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length
          curCap.toNat (bs0.length + 1)).1 →
      SepWPp (lsProg_314 H) ret sm
        ((vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ authHeaderBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗
          A.pool lim
            (M.stepEvents
              (pushBytesEvents (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length
                curCap.toNat (bs0.length + 1)) curSt) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_314 H) ret s P Q Qp oom := by
  have hfn2 : IsAuthEncodePlacedProg (lsProg_314 H) blkPl_314 := Or.inr ⟨H, rfl, rfl⟩
  refine step_auth_push_hdr_placed A.repAlloc hfn2 v curCap curPtr authA rkPtr mkPtr sp bs0 auth hlt
    (F := A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx21 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hvm01
  refine step_auth_len_placed hfn2 v authA sp auth hrk_lt hmk_lt hlen_fit
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hvm12
  rw [← A.pool_of_vmPreserved (hvm01.trans hvm12)]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 292)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm23 hinv2
    rw [← A.pool_of_vmPreserved hvm23]
    have hhdr_eq : (bs0 ++ [0x12#8]).length +
        (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length =
        bs0.length + (authHeaderBytes auth).length := by
      simp only [authHeaderBytes, List.length_append, List.length_singleton]; omega
    have hvarint_fit : (bs0 ++ [0x12#8]).length +
        (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length ≤ curCap.toNat ∨
        (bs0 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
      rw [hhdr_eq, List.length_append, List.length_singleton]; exact hfit
    have hfits_ev : FitsEvents M lim curSt
        (encodeVarintEvents
          (EncodeVarintGhost.mk (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))
            v curCap curPtr (bs0 ++ [0x12#8]))) := by
      rw [encodeVarintEvents_snoc]; exact hfits
    refine step_ed_encode_varint_det_call_placed A lim henc
      (BitVec.ofNat 64 (authenticatorPBEncodedLen auth)) v curCap curPtr sp ((blkPl_314).base + 152#64)
      (bs0 ++ [0x12#8]) curSt hvarint_fit hfits_ev (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2) (by sep_ac_rfl) ?_
    intro s3 cap1 ptr1 hpc3 hrun3 hsp3 htr3 hcs23 hcs3 hge1 hpres1 hdet1
    rw [hhdr_eq] at hpres1
    rw [pushBytesStep_det_snoc] at hdet1
    refine SepWPp.weaken_pre ?_
      (hnext s3 cap1 ptr1 hpc3 hrun3 hsp3 htr3
        (by rw [hcs23.1]; simp only [arm64_norm, *]) (by rw [hcs23.2.1]; simp only [arm64_norm, *])
        (by rw [hcs23.2.2.1]; simp only [arm64_norm, *]) (by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *])
        hcs3 hge1 hpres1 hdet1)
    rw [bs0_append_authHeaderBytes bs0 auth, encodeVarintEvents_snoc]
    exact Entails.of_eq (by sep_ac_rfl))

/-- Header-encoding stage (`+0..+152`) on block 314. -/
theorem step_hdr_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_314 H) (lsmpl.base 292)
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_314 H) (lsmpl.base 320)
      (withAuthEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (v cap0 ptr0 authA rkPtr mkPtr sp : BitVec 64)
    (bs0 : List (BitVec 8)) (auth : AuthenticatorPB) (st0 : M.σ)
    (hcap_le : bs0.length ≤ cap0.toNat) (hrk_lt : auth.rootKey.length < 2 ^ 63)
    (hmk_lt : auth.macKey.length < 2 ^ 63) (hlen_fit : authenticatorPBEncodedLen auth < 2 ^ 64)
    (hfit : bs0.length + (authHeaderBytes auth).length ≤ cap0.toNat ∨
      bs0.length + (authHeaderBytes auth).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim st0
      (pushBytesStep ((encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length + 1)
        cap0.toNat bs0.length).2)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_314).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = authA) (hx1 : s.readReg64 .x1 = v)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool lim st0 s ∗ stackAt sp (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_314).base + 152#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      AuthEncodeCalleeSavedPlaced s0 sm → cap0.toNat ≤ cap1.toNat →
      (bs0.length + (authHeaderBytes auth).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      cap1.toNat =
        (pushBytesStep ((encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length + 1)
          cap0.toNat bs0.length).1 →
      SepWPp (lsProg_314 H) ret sm
        ((vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ authHeaderBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗
          A.pool lim
            (M.stepEvents
              (pushBytesStep ((encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length + 1)
                cap0.toNat bs0.length).2 st0) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack) ∗
          ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_314 H) ret s P Q Qp oom := by
  have hstep44 := step_hdr_from_44_2_placed A lim H henc
  subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  have hhdr_bds := authHeaderBytes_len_bounds auth
  let hdrVlen := (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length
  obtain ⟨hfits_b1, hfits_rest⟩ :=
    (fitsEvents_pushBytesStep_succ_iff hdrVlen cap0.toNat bs0.length).mp hfits
  have hst_succ := stepEvents_pushBytesStep_succ st0 hdrVlen cap0.toNat bs0.length
  let S := ((sp - 64#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s.readReg64 .lr) ∗
    ((sp - 48#64) ↦₆₄ s.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s.readReg64 .x23) ∗
    ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
    ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)
  rw [stackAt_authEncode hres sp, vecU8At_eq_header_sep_buf A.repAlloc v cap0 ptr0 bs0, vecHeader]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  by_cases hcap0 : cap0 == BitVec.ofNat 64 bs0.length
  · have hcap_eq : cap0.toNat = bs0.length :=
      cap_toNat_eq_of_beq hcap0 (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit2 : bs0.length + (authHeaderBytes auth).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
    obtain ⟨hbound1, hlt1, hge0⟩ := reserveCap_one_bounds hcap_eq (by omega)
    have hpb := pushByteStep_of_eq v cap0 ptr0 bs0 hcap_eq
    have hfits_res : FitsEvents M lim st0 (doReserveEvents (DoReserveCall.mk v cap0 ptr0 bs0 1)) := by
      simpa [hpb] using hfits_b1
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      refine step_ed_do_reserve7_call_placed hres A lim hdoReserve v cap0 ptr0 sp
        ((blkPl_314).base + 428#64) bs0 1 st0 hbound1 hfits_res
        (F := authPBElemsAt authA rkPtr mkPtr auth ∗ S ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by dsimp [S]; rw [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap0.toNat bs0.length 1)
      have hnewCap1_toNat : newCap1.toNat = (pushByteStep cap0.toNat bs0.length).1 := by
        dsimp [newCap1]; rw [hpb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hfits_rest' : FitsEvents M lim
          (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap0 ptr0 bs0 1)) st0)
          (pushBytesEvents hdrVlen newCap1.toNat (bs0.length + 1)) := by
        rw [hnewCap1_toNat]; simpa [hpb] using hfits_rest
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs0, vecHeader]
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 44#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm1 hinv1
        rw [← A.pool_of_vmPreserved hvm1]
        refine hstep44 v newCap1 newPtr1 authA rkPtr mkPtr sp bs0 auth _
          hlt1 hrk_lt hmk_lt hlen_fit (Or.inr (by omega)) hfits_rest' (F := S ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
          (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
          (by rw [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
        intro sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm hge1 _ hdet1
        have hdet_all : cap1.toNat = (pushBytesStep (hdrVlen + 1) cap0.toNat bs0.length).1 := by
          rw [hdet1, hnewCap1_toNat]; rfl
        have hst_all :
            M.stepEvents (pushBytesEvents hdrVlen newCap1.toNat (bs0.length + 1))
              (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap0 ptr0 bs0 1)) st0) =
            M.stepEvents (pushBytesStep (hdrVlen + 1) cap0.toNat bs0.length).2 st0 := by
          rw [hst_succ, hnewCap1_toNat, hpb]
        refine SepWPp.weaken_pre (by rw [hst_all]; dsimp [S]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm
            (Nat.le_trans hge0 hge1) (fun h => absurd h (by omega)) hdet_all)))
  · have hcap0_f : (cap0 == BitVec.ofNat 64 bs0.length) = false := Bool.eq_false_iff.mpr hcap0
    have hlt0 : bs0.length < cap0.toNat :=
      lt_cap_toNat_of_beq_false hcap0_f hcap_le (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hpb := pushByteStep_of_lt hlt0
    have hfits_rest' : FitsEvents M lim st0 (pushBytesEvents hdrVlen cap0.toNat (bs0.length + 1)) := by
      simpa [hpb] using hfits_rest
    have hfit44 : bs0.length + (authHeaderBytes auth).length ≤ cap0.toNat ∨ bs0.length + 1 + 10 < 2 ^ 62 := by
      rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 44#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      refine hstep44 v cap0 ptr0 authA rkPtr mkPtr sp bs0 auth st0
        hlt0 hrk_lt hmk_lt hlen_fit hfit44 hfits_rest' (F := S ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by dsimp [S]; rw [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
      intro sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm hge1 hpres1 hdet1
      have hdet_all : cap1.toNat = (pushBytesStep (hdrVlen + 1) cap0.toNat bs0.length).1 := by
        simpa [pushBytesStep, hpb] using hdet1
      have hst_all :
          M.stepEvents (pushBytesEvents hdrVlen cap0.toNat (bs0.length + 1)) st0 =
          M.stepEvents (pushBytesStep (hdrVlen + 1) cap0.toNat bs0.length).2 st0 := by
        rw [hst_succ, hpb]; rfl
      refine SepWPp.weaken_pre (by rw [hst_all]; dsimp [S]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm hge1 hpres1 hdet_all))

/-! ## `root_key` Stage (`+152..+256`) -/

private theorem step_rk_from_228_2_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_314 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64)
    (bs2 : List (BitVec 8)) (auth : AuthenticatorPB) (curSt : M.σ)
    (hrk_ne : auth.rootKey.isEmpty = false) (hle : bs2.length + auth.rootKey.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_314).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length) (hx21 : s.readReg64 .x21 = authA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length) (hx23 : s.readReg64 .x23 = rkPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bs2.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs2 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool lim curSt s) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_314).base + 256#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_314 H) ret sm
        ((vecU8At A.repAlloc v curCap curPtr (bs2 ++ auth.rootKey) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool lim curSt sm) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_314 H) ret s P Q Qp oom := by
  subst hP
  have hrk_ne_nil : auth.rootKey ≠ [] := List.isEmpty_eq_false_iff.mp hrk_ne
  have hrk_pos : 0 < auth.rootKey.length := List.length_pos_of_ne_nil hrk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs2)
    (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool lim curSt s ∗ F) (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A.repAlloc v curCap curPtr bs2 auth.rootKey.length hle hcap_lt hptr_ne hrk_pos, authPBElemsAt]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := lsρ lsMemcpySym)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm1 hinv1
    rw [← A.pool_of_vmPreserved hvm1]
    refine step_ed_memcpy_call_placed hmemcpy
      (curPtr + BitVec.ofNat 64 bs2.length) rkPtr sp ((blkPl_314).base + 248#64) auth.rootKey
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.repAlloc.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
        memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 auth.rootKey.length)
          (curCap.toNat - bs2.length - auth.rootKey.length) ∗
        ((authA + 8#64) ↦₆₄ rkPtr) ∗ ((authA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((authA + 32#64) ↦₆₄ mkPtr) ∗ ((authA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        (mkPtr ↦ₛ auth.macKey) ∗ A.pool lim curSt _ ∗ F)
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
    have hx21_1 : s1.readReg64 .x21 = authA := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
    have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
    have hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 bs2.length := by rw [hcs01.2.2.2.2.2.1]; simp only [arm64_norm, *]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 256#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm2 hinv2
      rw [← A.pool_of_vmPreserved hvm2]
      refine SepWPp.weaken_pre ?_
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2))
      rw [← vecU8At_pack_slice A.repAlloc v curCap curPtr bs2 auth.rootKey hle hcap_lt hptr_ne hrk_ne_nil, authPBElemsAt]
      exact Entails.of_eq (by sep_ac_rfl)))

private theorem step_rk_from_176_2_placed [LibsignalPlacement] {resStack : Nat}
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
    (hrk_ne : auth.rootKey.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (authRootKeyBytes auth).length ≤ curCap.toNat ∨
      bs1.length + (authRootKeyBytes auth).length + 10 < 2 ^ 62)
    (hfits_v : FitsEvents M lim curSt
      (pushBytesEvents (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length
        curCap.toNat (bs1.length + 1)))
    (hfits_r : FitsEvents M lim
      (M.stepEvents
        (pushBytesEvents (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length
          curCap.toNat (bs1.length + 1)) curSt)
      (reserveStep
        (pushBytesStep (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length
          curCap.toNat (bs1.length + 1)).1
        (bs1.length + 1 + (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length)
        auth.rootKey.length).2)
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_314).base + 176#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = authA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = rkPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs1 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_314).base + 256#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (authRootKeyBytes auth).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      cap2.toNat =
        (reserveStep
          (pushBytesStep (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length
            curCap.toNat (bs1.length + 1)).1
          (bs1.length + 1 + (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length)
          auth.rootKey.length).1 →
      SepWPp (lsProg_314 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ authRootKeyBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗
          A.pool lim
            (M.stepEvents
              (reserveStep
                (pushBytesStep (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length
                  curCap.toNat (bs1.length + 1)).1
                (bs1.length + 1 + (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length)
                auth.rootKey.length).2
              (M.stepEvents
                (pushBytesEvents (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length
                  curCap.toNat (bs1.length + 1)) curSt)) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_314 H) ret s P Q Qp oom := by
  have hstep228 := step_rk_from_228_2_placed A lim H hmemcpy
  have hfn2 : IsAuthEncodePlacedProg (lsProg_314 H) blkPl_314 := Or.inr ⟨H, rfl, rfl⟩
  have hrk_len := authRootKeyBytes_len_of_ne_empty auth hrk_ne
  let rkVlen := (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length
  refine step_auth_push_rk_tag_placed A.repAlloc hfn2 v curCap curPtr authA rkPtr sp bs1 auth hlt
    (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 hvm01
  rw [← A.pool_of_vmPreserved hvm01]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 292)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm12 hinv1
    rw [← A.pool_of_vmPreserved hvm12]
    have hvarint_fit : (bs1 ++ [0x0a#8]).length + rkVlen ≤ curCap.toNat ∨
        (bs1 ++ [0x0a#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
    have hfits_ev : FitsEvents M lim curSt
        (encodeVarintEvents
          (EncodeVarintGhost.mk (BitVec.ofNat 64 auth.rootKey.length)
            v curCap curPtr (bs1 ++ [0x0a#8]))) := by
      rw [encodeVarintEvents_snoc]; exact hfits_v
    refine step_ed_encode_varint_det_call_placed A lim henc
      (BitVec.ofNat 64 auth.rootKey.length) v curCap curPtr sp ((blkPl_314).base + 208#64)
      (bs1 ++ [0x0a#8]) curSt hvarint_fit hfits_ev (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by sep_ac_rfl) ?_
    intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2 hdet2
    rw [pushBytesStep_det_snoc] at hdet2
    rw [encodeVarintEvents_snoc]
    let bs2 := (bs1 ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 auth.rootKey.length)
    let st_v := M.stepEvents (pushBytesEvents rkVlen curCap.toNat (bs1.length + 1)) curSt
    have hbs2_len_eq : bs1.length + 1 + rkVlen = bs2.length := by
      dsimp [bs2, rkVlen]; rw [List.length_append, List.length_append, List.length_singleton]
    have hbs2_tot : bs2.length + auth.rootKey.length = bs1.length + (authRootKeyBytes auth).length := by
      rw [← hbs2_len_eq, hrk_len]; omega
    have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs12.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = authA := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
    have hx23_2 : s2.readReg64 .x23 = rkPtr := by rw [hcs12.2.2.2.2.1]; simp only [arm64_norm, *]
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := A.pool lim st_v s2 ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ authPBElemsAt authA rkPtr mkPtr auth ∗ F)
      (by dsimp [bs2, st_v, rkVlen]; sep_ac_rfl) fun hle2 hcap2_lt _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap2 ptr2 bs2, vecHeader]
    have hrk_lt63 : auth.rootKey.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
    by_cases hneed : cap2.toNat < bs2.length + auth.rootKey.length
    · have hfit_rk : bs2.length + auth.rootKey.length < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 auth.rootKey.length) = true :=
        (elem_len_ult_spare_iff hle2 hcap2_lt hrk_lt63).mpr hneed
      obtain ⟨hnot_ult, hle3, hge3, hbound_rk⟩ := elem_len_after_reserve_not_ult hfit_rk hneed
      have hrs_eq := reserveStep_of_need_doReserveEvents v cap2 ptr2 bs2 auth.rootKey.length (by omega)
      have hfits_doRes : FitsEvents M lim st_v
          (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 auth.rootKey.length)) := by
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
          ((blkPl_314).base + 488#64) bs2 auth.rootKey.length st_v hbound_rk hfits_doRes
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
        let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length auth.rootKey.length)
        change (BitVec.ofNat 64 auth.rootKey.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true at hnot_ult
        have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
        have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs23.2.1]; simp only [arm64_norm, *]
        have hx21_3 : s3.readReg64 .x21 = authA := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
        have hx22_3 : s3.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
        have hx23_3 : s3.readReg64 .x23 = rkPtr := by rw [hcs23.2.2.2.2.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v cap3 ptr3 bs2, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 228#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hvm3 hinv3
          rw [← A.pool_of_vmPreserved hvm3]
          refine hstep228 v cap3 ptr3 authA rkPtr mkPtr sp bs2 auth _ hrk_ne hle3
            (F := stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
          intro sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
          have hcap3_det : cap3.toNat =
              (reserveStep (pushBytesStep rkVlen curCap.toNat (bs1.length + 1)).1
                (bs1.length + 1 + rkVlen) auth.rootKey.length).1 := by
            rw [← hdet2, hbs2_len_eq, hrs_eq]
            dsimp [cap3]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hst_det :
              M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 auth.rootKey.length)) st_v =
              M.stepEvents
                (reserveStep (pushBytesStep rkVlen curCap.toNat (bs1.length + 1)).1
                  (bs1.length + 1 + rkVlen) auth.rootKey.length).2 st_v := by
            rw [← hdet2, hbs2_len_eq, hrs_eq]
          refine SepWPp.weaken_pre
            (by dsimp [bs2, st_v, rkVlen] at hst_det ⊢
                rw [bs_append_authRootKeyBytes_of_ne_empty bs1 auth hrk_ne, hst_det]
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
              (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega)) hcap3_det)))
    · have hle_fast : bs2.length + auth.rootKey.length ≤ cap2.toNat := by omega
      have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 auth.rootKey.length) = false :=
        Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hrk_lt63).mp h)
      have hrs_eq : reserveStep (pushBytesStep rkVlen curCap.toNat (bs1.length + 1)).1
          (bs1.length + 1 + rkVlen) auth.rootKey.length = (cap2.toNat, []) := by
        rw [← hdet2, hbs2_len_eq]; exact reserveStep_of_spare hle_fast
      have hpres_all : bs1.length + (authRootKeyBytes auth).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 228#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm2 hinv2
        rw [← A.pool_of_vmPreserved hvm2]
        refine hstep228 v cap2 ptr2 authA rkPtr mkPtr sp bs2 auth st_v hrk_ne hle_fast
          (F := stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
        refine SepWPp.weaken_pre
          (by dsimp [bs2, st_v, rkVlen] at hrs_eq ⊢
              rw [bs_append_authRootKeyBytes_of_ne_empty bs1 auth hrk_ne, hrs_eq]
              simp only [AllocCostModel.stepEvents_nil]
              exact Entails.of_eq (by sep_ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 hpres_all
            (by rw [hrs_eq]))))

/-- `root_key` field stage (`+152..+256`) on block 314. -/
theorem step_rk_2_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_314 H) (lsmpl.base 292)
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_314 H) (lsmpl.base 320)
      (withAuthEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_314 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v cap1 ptr1 authA rkPtr mkPtr sp : BitVec 64)
    (bs1 : List (BitVec 8)) (auth : AuthenticatorPB) (st1 : M.σ)
    (hrk_lt : auth.rootKey.length < 2 ^ 63)
    (hfit : bs1.length + (authRootKeyBytes auth).length ≤ cap1.toNat ∨
      bs1.length + (authRootKeyBytes auth).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim st1 (optBytesField1ByteTagStep cap1.toNat bs1.length auth.rootKey).2)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_314).base + 152#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length) (hx21 : s.readReg64 .x21 = authA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v cap1 ptr1 bs1 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool lim st1 s ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_314).base + 256#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → AuthEncodeCalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (authRootKeyBytes auth).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      cap2.toNat = (optBytesField1ByteTagStep cap1.toNat bs1.length auth.rootKey).1 →
      SepWPp (lsProg_314 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ authRootKeyBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗
          A.pool lim (M.stepEvents (optBytesField1ByteTagStep cap1.toNat bs1.length auth.rootKey).2 st1) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_314 H) ret s P Q Qp oom := by
  have hstep176 := step_rk_from_176_2_placed hres A lim H henc hdoReserve hmemcpy
  subst hP
  have ⟨hrk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := auth.rootKey) (by omega)
  cases hrk : auth.rootKey.isEmpty
  · have hrk_len := authRootKeyBytes_len_of_ne_empty auth hrk
    let rkVlen := (encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length
    obtain ⟨hfits_s1, hfits_s2⟩ :=
      (fitsEvents_optBytesField1ByteTagStep_nonempty_iff (M := M) (lim := lim) (st := st1) hrk).mp hfits
    obtain ⟨hfits_b1, hfits_v⟩ :=
      (fitsEvents_pushBytesStep_succ_iff rkVlen cap1.toNat bs1.length).mp hfits_s1
    have hst_opt := stepEvents_optBytesField1ByteTagStep_nonempty (M := M) st1
      (cap := cap1.toNat) (len := bs1.length) hrk
    have hst_s1 := stepEvents_pushBytesStep_succ st1 rkVlen cap1.toNat bs1.length
    have hopt_fst : (optBytesField1ByteTagStep cap1.toNat bs1.length auth.rootKey).1 =
        (reserveStep (pushBytesStep (rkVlen + 1) cap1.toNat bs1.length).1
          (bs1.length + 1 + rkVlen) auth.rootKey.length).1 := by
      simp only [optBytesField1ByteTagStep, hrk, Bool.false_eq_true, ↓reduceIte, rkVlen]
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool lim st1 s ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by sep_ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1, vecHeader, authPBElemsAt]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · have hcap_eq : cap1.toNat = bs1.length :=
        cap_toNat_eq_of_beq hcap1 (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hfit2 : bs1.length + (authRootKeyBytes auth).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      have hpb := pushByteStep_of_eq v cap1 ptr1 bs1 hcap_eq
      have hfits_res : FitsEvents M lim st1 (doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)) := by
        simpa [hpb] using hfits_b1
      apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm0 hinv0
        rw [← A.pool_of_vmPreserved hvm0]
        refine step_ed_do_reserve7_call_placed hres A lim hdoReserve v cap1 ptr1 sp
          ((blkPl_314).base + 456#64) bs1 1 st1 hbound1 hfits_res
          (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader, authPBElemsAt]; sep_ac_rfl) ?_
        intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
        let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
        have hnewCap1_toNat : newCap1.toNat = (pushByteStep cap1.toNat bs1.length).1 := by
          dsimp [newCap1]; rw [hpb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hfits_v' : FitsEvents M lim
            (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)) st1)
            (pushBytesEvents rkVlen newCap1.toNat (bs1.length + 1)) := by
          rw [hnewCap1_toNat]; simpa [hpb] using hfits_v
        have hfits_r' : FitsEvents M lim
            (M.stepEvents (pushBytesEvents rkVlen newCap1.toNat (bs1.length + 1))
              (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)) st1))
            (reserveStep (pushBytesStep rkVlen newCap1.toNat (bs1.length + 1)).1
              (bs1.length + 1 + rkVlen) auth.rootKey.length).2 := by
          have h' := hfits_s2
          rw [hst_s1] at h'
          simpa [pushBytesStep, hnewCap1_toNat, hpb, rkVlen] using h'
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs1, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 176#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hvm1 hinv1
          rw [← A.pool_of_vmPreserved hvm1]
          refine hstep176 v newCap1 newPtr1 authA rkPtr mkPtr sp bs1 auth _ hrk hlt1
            (Or.inr hfit2) hfits_v' hfits_r' (F := F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; sep_ac_rfl) ?_
          intro sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 _ hdet2
          have hdet_all : cap2.toNat = (optBytesField1ByteTagStep cap1.toNat bs1.length auth.rootKey).1 := by
            rw [hopt_fst]; simpa [pushBytesStep, hnewCap1_toNat, rkVlen] using hdet2
          have hst_all :
              M.stepEvents
                (reserveStep (pushBytesStep rkVlen newCap1.toNat (bs1.length + 1)).1
                  (bs1.length + 1 + rkVlen) auth.rootKey.length).2
                (M.stepEvents (pushBytesEvents rkVlen newCap1.toNat (bs1.length + 1))
                  (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)) st1)) =
              M.stepEvents (optBytesField1ByteTagStep cap1.toNat bs1.length auth.rootKey).2 st1 := by
            rw [hst_opt]; dsimp only
            rw [hst_s1]; simp only [pushBytesStep, hnewCap1_toNat, hpb, rkVlen]
          refine SepWPp.weaken_pre (by rw [hst_all]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
              (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)) hdet_all)))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat :=
        lt_cap_toNat_of_beq_false hcap1_f hcap1_le (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hpb := pushByteStep_of_lt hlt1
      have hfits_v' : FitsEvents M lim st1 (pushBytesEvents rkVlen cap1.toNat (bs1.length + 1)) := by
        simpa [hpb] using hfits_v
      have hfits_r' : FitsEvents M lim
          (M.stepEvents (pushBytesEvents rkVlen cap1.toNat (bs1.length + 1)) st1)
          (reserveStep (pushBytesStep rkVlen cap1.toNat (bs1.length + 1)).1
            (bs1.length + 1 + rkVlen) auth.rootKey.length).2 := by
        have h' := hfits_s2
        rw [hst_s1] at h'
        simpa [pushBytesStep, hpb, rkVlen] using h'
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 176#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm0 hinv0
        rw [← A.pool_of_vmPreserved hvm0]
        refine hstep176 v cap1 ptr1 authA rkPtr mkPtr sp bs1 auth st1 hrk hlt1 hfit
          hfits_v' hfits_r' (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader, authPBElemsAt]; try sep_ac_rfl) ?_
        intro sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 hpres2 hdet2
        have hdet_all : cap2.toNat = (optBytesField1ByteTagStep cap1.toNat bs1.length auth.rootKey).1 := by
          rw [hopt_fst]; simpa [pushBytesStep, hpb, rkVlen] using hdet2
        have hst_all :
            M.stepEvents
              (reserveStep (pushBytesStep rkVlen cap1.toNat (bs1.length + 1)).1
                (bs1.length + 1 + rkVlen) auth.rootKey.length).2
              (M.stepEvents (pushBytesEvents rkVlen cap1.toNat (bs1.length + 1)) st1) =
            M.stepEvents (optBytesField1ByteTagStep cap1.toNat bs1.length auth.rootKey).2 st1 := by
          rw [hst_opt]; dsimp only
          rw [hst_s1]; simp only [pushBytesStep, hpb, AllocCostModel.stepEvents_nil, rkVlen]
        refine SepWPp.weaken_pre (by rw [hst_all]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 hpres2 hdet_all))
  · have hopt_emp := optBytesField1ByteTagStep_of_isEmpty (cap := cap1.toNat) (len := bs1.length) hrk
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_314).base + 256#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      refine SepWPp.weaken_pre
        (by rw [bs_append_authRootKeyBytes_of_empty bs1 auth hrk, hopt_emp]
            simp only [AllocCostModel.stepEvents_nil]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hopt_emp])))

end LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlacedAuxBudget
