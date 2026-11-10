/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `TripleRatchet::from_session_state`

Relocatable `RustCliAllocBudget`-threaded verification of
`<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state` (block 57, `FreeOnlyEvs`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.MainBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (SenderChain)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkLib_57 blkLib_eq_57 blkPC_201 blkPC_57 blkPl_201 blkPl_57
  lsLogFilterAddr lsRustDeallocSym ls_hook_ok_of_mem lscall_blk
  lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc vecAt)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex (deserializePlacedSpec)
open CryptoVerification.LibsignalSessionRepr (chainAt optSenderChainBytes)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost noneCap optSenderChainAt sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet (TrFromGhost trFromStack trResultAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  blkPC_2 blkPC_29 blkPC_5 blkPl_2 blkPl_29 blkPl_5
)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (
  keyToBytes32_length sepWP_seq_lscl_ro withLsRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom (
  SepWP.mono_pre SepWP.with_post afterTrFrom_decRel
  exists_chainKey_split_of_length_32 exists_privKey_split
  exists_pubKey_split_of_length_32 exists_rootKey_split_of_length_32
  memRegion_33_to_tag_and_32 optSenderChainAt_some_expose_from
  optSenderChainAt_some_reassemble_from pubKey_unpack_sp_455
  scRawCells_none_entails scRawCells_some_entails senderChainFromFrame
  sessionAfter208Frame sessionFromBase sessionFromFrame_expose_remoteIk
  sessionStateAt_expose_from stackAt_trFrom stack_184_24_fold_some
  stack_184_24_split_some stack_256_96_split stack_456_160_fold_some
  stack_456_160_split_deser trFromSavedRegs vecAt_nil_chains_0_8 vecU8Rest
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropSpeSpec dropVecChainSpec remoteIdentityKeyPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget (
  deserializePlacedBudgetSpec deserialize_vm_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget (
  trFrom10cTailPlaced trFromPlacedSpec trFromRawPlacedSpec
  trFrom_step_10c_to_244_placed trFrom_step_244_to_ret_placed
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

private theorem checkBlockNoSvc0_57 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_57.text = true := by
  decide +kernel

theorem trFrom_step_ac_to_244_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (A : RustAlloc) (x : TrFromGhost) (sg : SenderChainGhost) (sc : SenderChain)
    (s0 s : State) (F_tail : SepProp) (post : State → SepProp → Prop)
    (w_208 : BitVec 64) (b_200 : BitVec 8)
    (d_192 : BitVec 32) (h_188 : BitVec 16)
    (u_296 : BitVec 64) (u_288 u_284 : BitVec 32)
    {rk_b0 rk_b1 rk_b2 rk_b3 rk_b4 rk_b5 rk_b6 : BitVec 8}
    {rk_w7 rk_w15 rk_w23 : BitVec 64} {rk_b31 : BitVec 8}
    (hrk : ∀ a : BitVec 64,
      (a ↦ₛ keyToBytes32 x.st.rootKey) =
        ((a ↦₈ rk_b0) ∗ ((a + 1#64) ↦₈ rk_b1) ∗ ((a + 2#64) ↦₈ rk_b2) ∗ ((a + 3#64) ↦₈ rk_b3) ∗
         ((a + 4#64) ↦₈ rk_b4) ∗ ((a + 5#64) ↦₈ rk_b5) ∗ ((a + 6#64) ↦₈ rk_b6) ∗
         ((a + 7#64) ↦₆₄ rk_w7) ∗ ((a + 15#64) ↦₆₄ rk_w15) ∗ ((a + 23#64) ↦₆₄ rk_w23) ∗
         ((a + 31#64) ↦₈ rk_b31)))
    (hsender_opt : x.G.sender = some sg)
    (hsc_opt : x.st.senderChain = some sc)
    (hclamp_sc : clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hsrk_cmn : (sg.srk.cap + 1#64 == 0#64) = false)
    (hck_cmn : (sg.ck.cap + 1#64 == 0#64) = false)
    (hcmn_chains : (x.G.chainsCap + 1#64 == 0#64) = false)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_57).base + 172#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 0xf#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = s0.sp - 456#64)
    (hx21 : s.readReg64 .x21 = rk_w15)
    (hx22 : s.readReg64 .x22 = rk_w7)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = 0#64)
    (hx26 : s.readReg64 .x26 = x.ss)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ s_244, VmPreserved s s_244 →
      LibsignalCodeLoaded lsmpl s_244.mem → LibsignalRoLoaded lsmpl s_244.mem →
      s_244.pc = (blkPl_57).base + 580#64 →
      s_244.status = .Running → s_244.trace = s0.trace →
      s_244.readReg64 .x0 = x.G.localIk.ptr →
      s_244.readReg64 .x1 = BitVec.ofNat 64 x.G.localIk.bytes.length →
      s_244.readReg64 .x8 = s0.sp - 160#64 →
      s_244.readReg64 .x19 = x.ret →
      s_244.readReg64 .x20 = x.G.pq.cap →
      s_244.readReg64 .x21 = x.G.pq.ptr →
      s_244.readReg64 .x22 = x.ss →
      s_244.readReg64 .x23 = 0x8000000000000014#64 →
      s_244.readReg64 .x24 = s0.sp - 184#64 →
      s_244.readReg64 .x25 = BitVec.ofNat 64 x.st.pqRatchetState.length →
      s_244.readReg64 .x29 = s0.sp - 96#64 →
      s_244.sp = s0.sp - 496#64 →
      calleeSavedVRegs s_244 = calleeSavedVRegs s →
      SepWP ((blkPC_57).rebase (blkPl_57).base H) (s0.readReg64 .lr) s_244
        (((s0.sp - 456#64) ↦₆₄ x.G.chainsCap) ∗
         ((s0.sp - 448#64) ↦₆₄ x.G.chainsPtr) ∗
         ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
         ((s0.sp - 432#64) ↦ₛ optSenderChainBytes x.st.senderChain (List.replicate 100 0#8)) ∗
         ((s0.sp - 328#64) ↦ₛ keyToBytes32 x.st.rootKey) ∗
         ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
         ((s0.sp - 288#64) ↦₃₂ x.st.previousCounter) ∗
         ((s0.sp - 284#64) ↦₃₂ u_284) ∗
         memRegion (s0.sp - 280#64) 184 ∗
         sessionAfter208Frame A x.ss x.G x.st ∗
         F_tail)
        post) :
    SepWP ((blkPC_57).rebase (blkPl_57).base H) (s0.readReg64 .lr) s
      (memRegion (s0.sp - 184#64) 24 ∗
       ((s0.sp - 456#64) ↦₈ 0#8) ∗
       ((s0.sp - 455#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       memRegion (s0.sp - 423#64) 127 ∗
       ((s0.sp - 296#64) ↦₆₄ u_296) ∗
       ((s0.sp - 288#64) ↦₃₂ u_288) ∗
       ((s0.sp - 284#64) ↦₃₂ u_284) ∗
       memRegion (s0.sp - 280#64) 24 ∗
       memRegion (s0.sp - 256#64) 24 ∗
       ((s0.sp - 232#64) ↦₆₄ rk_w23) ∗
       ((s0.sp - 224#64) ↦₈ rk_b31) ∗ memRegion (s0.sp - 223#64) 7 ∗
       ((s0.sp - 216#64) ↦₈ rk_b0) ∗ ((s0.sp - 215#64) ↦₈ rk_b1) ∗
       ((s0.sp - 214#64) ↦₈ rk_b2) ∗ ((s0.sp - 213#64) ↦₈ rk_b3) ∗
       ((s0.sp - 212#64) ↦₈ rk_b4) ∗ ((s0.sp - 211#64) ↦₈ rk_b5) ∗
       ((s0.sp - 210#64) ↦₈ rk_b6) ∗ memRegion (s0.sp - 209#64) 1 ∗
       ((s0.sp - 208#64) ↦₆₄ w_208) ∗
       ((s0.sp - 200#64) ↦₈ b_200) ∗ memRegion (s0.sp - 199#64) 7 ∗
       ((s0.sp - 192#64) ↦₃₂ d_192) ∗ ((s0.sp - 188#64) ↦₁₆ h_188) ∗ memRegion (s0.sp - 186#64) 2 ∗
       ((s0.sp - 160#64) ↦₆₄ x.G.chainsCap) ∗
       ((s0.sp - 152#64) ↦₆₄ x.G.chainsPtr) ∗
       ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
       memRegion (s0.sp - 136#64) 16 ∗
       memRegion (s0.sp - 120#64) 24 ∗
       sessionFromBase A x.ss x.G x.st ∗
       (x.ss ↦₆₄ x.G.localIk.cap) ∗ ((x.ss + 8#64) ↦₆₄ x.G.localIk.ptr) ∗
       ((x.ss + 16#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
       vecU8Rest A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
       ((x.ss + 48#64) ↦₆₄ x.G.root.cap) ∗ ((x.ss + 56#64) ↦₆₄ x.G.root.ptr) ∗
       ((x.ss + 64#64) ↦₆₄ 32#64) ∗
       (x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
       ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
       ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
       ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
       ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
       ((x.G.root.ptr + 31#64) ↦₈ rk_b31) ∗
       vecU8Rest A x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 72#64) 0#64 8#64 [] ∗
       ((x.ss + 120#64) ↦₆₄ x.G.pq.cap) ∗ ((x.ss + 128#64) ↦₆₄ x.G.pq.ptr) ∗
       ((x.ss + 136#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length) ∗
       senderChainFromFrame A x.ss sg sc ∗
       ((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index) ∗
       ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
       F_tail)
      post := by
  have hstep10c := @trFrom_step_10c_to_244_placed _ H
  have _ := hsrk_cmn; have _ := hck_cmn
  obtain ⟨pk_b0, pk_b1, pk_b2, pk_b3, pk_b4, pk_b5, pk_b6, pk_b7,
          pk_b8, pk_b9, pk_b10, pk_b11, pk_b12, pk_b13, pk_b14, pk_b15,
          pk_b16, pk_b17, pk_b18, pk_b19, pk_b20, pk_b21, pk_b22, pk_b23,
          pk_b24, pk_b25, pk_b26, pk_b27, pk_d28, hpk1, hpk2⟩ :=
    exists_pubKey_split_of_length_32 sc.ratchetKey.publicKey.bytes.toList_length
  obtain ⟨sk_b0, sk_d1, sk_h5, sk_w7, sk_w15, sk_w23, sk_b31, hc0, hc31, hsk⟩ :=
    exists_privKey_split sc.ratchetKey.privateKey.bytes hclamp_sc
  obtain ⟨ck_d0, ck_b4, ck_b5, ck_b6, ck_b7, ck_b8, ck_b9, ck_b10, ck_b11,
          ck_b12, ck_b13, ck_b14, ck_b15, ck_b16, ck_b17, ck_b18, ck_b19,
          ck_b20, ck_b21, ck_b22, ck_w23, ck_b31, hck1, hck2⟩ :=
    exists_chainKey_split_of_length_32 (keyToBytes32_length sc.chainKey.key)
  apply sepWP_seq_lscl_ro hcl hro (mid := (blkPl_57).base + 268#64)
  rw [stack_184_24_split_some s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun t_162 => SepWP.exists_elim fun t_164 => ?_
  refine SepWP.exists_elim fun t_166 => SepWP.exists_elim fun t_167 => ?_
  refine SepWP.exists_elim fun t_168 => SepWP.exists_elim fun t_169 => ?_
  refine SepWP.exists_elim fun t_170 => SepWP.exists_elim fun t_171 => ?_
  refine SepWP.exists_elim fun t_172 => SepWP.exists_elim fun t_173 => ?_
  refine SepWP.exists_elim fun t_174 => SepWP.exists_elim fun t_175 => ?_
  refine SepWP.exists_elim fun t_176 => SepWP.exists_elim fun t_177 => ?_
  refine SepWP.exists_elim fun t_178 => SepWP.exists_elim fun t_179 => ?_
  refine SepWP.exists_elim fun t_180 => SepWP.exists_elim fun t_181 => ?_
  refine SepWP.exists_elim fun t_182 => SepWP.exists_elim fun t_183 => ?_
  refine SepWP.exists_elim fun t_184 => ?_
  refine SepWP.fold (Entails.refl
      (((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index))) (by sep_focus) ?_
  rw [pubKey_unpack_sp_455 s0.sp hpk1, hsk sg.priv.ptr, hck1 sg.ck.ptr]
  simp only [sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := (blkPC_57).rebase (blkPl_57).base (hooksException H))
    blkLib_eq_57 checkBlockNoSvc0_57 (mid := (blkPl_57).base + 268#64); intro _m_strip
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    fun _m_real _hnsp => ?_
  have hvm_10c : VmPreserved s _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvm_10c ⊢
  refine SepWP.fold (stack_456_160_fold_some s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (stack_184_24_fold_some s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  have hsk_fold :
      ((sg.priv.ptr ↦₈ sk_b0) ∗ ((sg.priv.ptr + 1#64) ↦₃₂ sk_d1) ∗
       ((sg.priv.ptr + 5#64) ↦₁₆ sk_h5) ∗ ((sg.priv.ptr + 7#64) ↦₆₄ sk_w7) ∗
       ((sg.priv.ptr + 15#64) ↦₆₄ sk_w15) ∗ ((sg.priv.ptr + 23#64) ↦₆₄ sk_w23) ∗
       ((sg.priv.ptr + 31#64) ↦₈ sk_b31)) ⊢
      (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) := by
    rw [hsk sg.priv.ptr]; exact Entails.refl _
  refine SepWP.fold hsk_fold (by sep_focus) ?_
  have hck_fold :
      ((sg.ck.ptr ↦₃₂ ck_d0) ∗
       ((sg.ck.ptr + 4#64) ↦₁₆ (ck_b5 ++ ck_b4)) ∗
       ((sg.ck.ptr + 6#64) ↦₈ ck_b6) ∗
       ((sg.ck.ptr + 7#64) ↦₆₄ (ck_b14 ++ ck_b13 ++ ck_b12 ++ ck_b11 ++ ck_b10 ++ ck_b9 ++ ck_b8 ++ ck_b7)) ∗
       ((sg.ck.ptr + 15#64) ↦₆₄ (ck_b22 ++ ck_b21 ++ ck_b20 ++ ck_b19 ++ ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15)) ∗
       ((sg.ck.ptr + 23#64) ↦₆₄ ck_w23) ∗
       ((sg.ck.ptr + 31#64) ↦₈ ck_b31)) ⊢
      (sg.ck.ptr ↦ₛ keyToBytes32 sc.chainKey.key) := by
    rw [hck1 sg.ck.ptr]; exact Entails.refl _
  refine SepWP.fold hck_fold (by sep_focus) ?_
  have hsc_some_fold :
      (senderChainFromFrame A x.ss sg sc ∗
       ((x.ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((x.ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((x.ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
       ((x.ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((x.ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((x.ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((x.ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((x.ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ keyToBytes32 sc.chainKey.key) ∗
       ((x.ss + 240#64) ↦₃₂ sc.chainKey.index)) ⊢
      optSenderChainAt A (x.ss + 144#64) x.G.sender x.st.senderChain := by
    rw [hsender_opt, hsc_opt]
    exact optSenderChainAt_some_reassemble_from A x.ss sg sc
  refine SepWP.fold hsc_some_fold (by sep_focus) ?_
  have hrk_fold :
      ((x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
       ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
       ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
       ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
       ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
       ((x.G.root.ptr + 31#64) ↦₈ rk_b31)) ⊢
      (x.G.root.ptr ↦ₛ keyToBytes32 x.st.rootKey) := by
    rw [hrk x.G.root.ptr]; exact Entails.refl _
  refine SepWP.fold hrk_fold (by sep_focus) ?_
  clear t_162 t_164 t_166 t_167 t_168 t_169 t_170 t_171 t_172 t_173 t_174 t_175
        t_176 t_177 t_178 t_179 t_180 t_181 t_182 t_183 t_184
        hpk1 hck1 hsk_fold hck_fold hsc_some_fold hrk_fold
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  intro hcl_10c hro_10c
  refine SepWP.mono_pre (Entails.of_eq (by sep_ac_rfl))
    (hstep10c
      (rx2 := pk_b27 ++ pk_b26 ++ pk_b25 ++ pk_b24 ++ pk_b23 ++ pk_b22 ++ pk_b21 ++ pk_b20)
      (rx3 := sk_b0.zeroExtend 64)
      (rx14 := sk_b31.zeroExtend 64)
      A x.ret x.ss x.G x.st s0 _ (s0.readReg64 .lr) F_tail post
      ck_w23 ck_b31 sk_d1 sk_h5 u_296 u_288 u_284
      hrk hcmn_chains hcl_10c hro_10c
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) halign
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]; bv_kernel) (by simp only [arm64_norm]; revert hc0; bv_kernel)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; revert hc31; bv_kernel)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx29]) (by simp only [arm64_norm, hsp]) ?_)
  intro s_244 hvm_244 hcl_244 hro_244 hpc_244 hrun_244 htr_244
    hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
  refine SepWP.fold
    (scRawCells_some_entails s0.sp sc (List.replicate 100 0#8) hpk2 hsk hck2)
    (by sep_focus) ?_
  rw [← hsc_opt]
  refine SepWP.mono_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont s_244 (hvm_10c.trans hvm_244) hcl_244 hro_244 hpc_244 hrun_244 htr_244
      hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
      (by simp only [arm64_norm, *]))

theorem trFrom_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hDeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base deserializePlacedBudgetSpec)
    (hRemoteIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A.repAlloc)))
    (hDropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec M A lim)))
    (hDropVecChain : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec M A lim))) :
    subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (blkPl_57).base (trFromPlacedSpec M A lim) := by
  simp only [trFromPlacedSpec, withLsCodeLoaded, trFromRawPlacedSpec]
  wp_init a s0
  rcases a with ⟨x, stB⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hro0 : LibsignalRoLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 .x0 = x.ss := by assumption
  have hw1 : (s0.readReg64 .x1).setWidth 32 = 0#32 := by assumption
  have hx8 : s0.readReg64 .x8 = x.ret := by assumption
  apply SepWP.with_post; intro post_ok hpost_ok
  have hstep10c := @trFrom_step_10c_to_244_placed _ H
  have hstepac := @trFrom_step_ac_to_244_placed _ H
  have hstep244 := @trFrom_step_244_to_ret_placed _ M A lim H hdealloc hRemoteIk hDropSpe hDropVecChain
  have halign0 : (s0.sp &&& 0xf#64 == 0#64) = true := by
    simpa only [State.spAligned] using hsp_align
  refine SepWP.mono_pre (sepConj_mono (sessionStateAt_expose_from A.repAlloc x.ss x.G x.st) (Entails.refl _)) ?_
  simp only [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hlik, hlik_toNat, hchains, hcmn_chains, _, hpq_ne, hsc_some⟩ => ?_
  refine SepWP.mono_pre (sepConj_mono (sessionFromFrame_expose_remoteIk A.repAlloc x.ss x.G x.st) (Entails.refl _)) ?_
  simp only [sepConj_assoc]
  refine SepWP.pure_elim fun hrik => ?_
  obtain ⟨rk_b0, rk_b1, rk_b2, rk_b3, rk_b4, rk_b5, rk_b6, rk_w7, rk_w15, rk_w23, rk_b31, hrk⟩ :=
    exists_rootKey_split_of_length_32 (keyToBytes32_length x.st.rootKey)
  refine SepWP.fold (Entails.of_eq (stackAt_trFrom s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun r11 => SepWP.exists_elim fun r10 => ?_
  refine SepWP.exists_elim fun r9 => SepWP.exists_elim fun r8 => ?_
  refine SepWP.exists_elim fun r7 => SepWP.exists_elim fun r6 => ?_
  refine SepWP.exists_elim fun r5 => SepWP.exists_elim fun r4 => ?_
  refine SepWP.exists_elim fun r3 => SepWP.exists_elim fun r2 => ?_
  refine SepWP.exists_elim fun r1 => SepWP.exists_elim fun r0 => ?_
  refine SepWP.exists_elim fun u_144 => SepWP.exists_elim fun u_152 => ?_
  refine SepWP.exists_elim fun u_160 => SepWP.exists_elim fun u_284 => ?_
  refine SepWP.exists_elim fun u_288 => SepWP.exists_elim fun u_296 => ?_
  refine SepWP.fold (Entails.of_eq (stack_256_96_split s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun h_188 => SepWP.exists_elim fun d_192 => ?_
  refine SepWP.exists_elim fun b_200 => SepWP.exists_elim fun w_208 => ?_
  refine SepWP.exists_elim fun b_210 => SepWP.exists_elim fun b_211 => ?_
  refine SepWP.exists_elim fun b_212 => SepWP.exists_elim fun b_213 => ?_
  refine SepWP.exists_elim fun b_214 => SepWP.exists_elim fun b_215 => ?_
  refine SepWP.exists_elim fun b_216 => SepWP.exists_elim fun b_224 => ?_
  refine SepWP.exists_elim fun w_232 => ?_
  rw [hrk x.G.root.ptr]
  apply sepWP_seq_lscl_ro hcl0 hro0 (mid := (blkPl_57).base + 92#64)
  apply sepWP_seg_ls_vm (Q := (blkPC_57).rebase (blkPl_57).base (hooksException H))
    blkLib_eq_57 checkBlockNoSvc0_57 (mid := (blkPl_57).base + 92#64); intro _m_strip0
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.fold (vecAt_nil_chains_0_8 A.repAlloc (x.ss + 72#64)) (by sep_focus) ?_
  have hsaved_fold :
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      trFromSavedRegs s0.sp s0 := Entails.refl _
  refine SepWP.fold hsaved_fold (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl_5c hro_5c
  cases hsc_opt : x.st.senderChain with
  | none =>
    cases hsender_opt : x.G.sender with
    | some _ => simp [hsender_opt, hsc_opt] at hsc_some
    | none =>
      have hclamp_none : ∀ sc, x.st.senderChain = some sc →
          clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
        intro _ h; rw [hsc_opt] at h; cases h
      have hsc_none_unfold :
          optSenderChainAt A.repAlloc (x.ss + 144#64) none none =
            (((x.ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.ss + 152#64) 96) := by
        dsimp only [optSenderChainAt, noneCap]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have hsc_none_fold :
          (((x.ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.ss + 152#64) 96) ⊢
            optSenderChainAt A.repAlloc (x.ss + 144#64) x.G.sender x.st.senderChain := by
        rw [hsender_opt, hsc_opt, hsc_none_unfold]; exact Entails.refl _
      apply sepWP_seq_lscl_ro hcl_5c hro_5c (mid := (blkPl_57).base + 268#64)
      refine SepWP.fold (Entails.of_eq hsc_none_unfold) (by sep_focus) ?_
      apply sepWP_seg_ls_vm (Q := (blkPC_57).rebase (blkPl_57).base (hooksException H))
        blkLib_eq_57 checkBlockNoSvc0_57 (mid := (blkPl_57).base + 268#64); intro _m_strip1
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        fun _m_real1 _hnsp1 => ?_
      refine SepWP.transport_budgetPool
        (_hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      simp only [State.setMem_setMem]
      refine SepWP.fold hsc_none_fold (by sep_focus) ?_
      have hrk_fold :
          ((x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
           ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
           ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
           ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
           ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
           ((x.G.root.ptr + 31#64) ↦₈ rk_b31)) ⊢
          (x.G.root.ptr ↦ₛ keyToBytes32 x.st.rootKey) := by
        rw [hrk x.G.root.ptr]; exact Entails.refl _
      refine SepWP.fold hrk_fold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_10c hro_10c
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTailPlaced; sep_ac_rfl))
        (hstep10c A.repAlloc x.ret x.ss x.G x.st s0 _ (s0.readReg64 .lr)
          (trFrom10cTailPlaced A lim x stB s0 _) post_ok
          w_208 b_200 d_192 h_188 u_296 u_288 u_284
          hrk hcmn_chains hcl_10c hro_10c
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign0
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
      intro s_244 hvm_244 hcl_244 hro_244 hpc_244 hrun_244 htr_244
        hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
      refine SepWP.fold (scRawCells_none_entails s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWP.exists_elim fun senderPad => ?_
      refine SepWP.pure_elim fun hpad => ?_
      rw [← hsc_opt, show trFrom10cTailPlaced A lim x stB s0 _ = trFrom10cTailPlaced A lim x stB s0 s_244 by
        unfold trFrom10cTailPlaced; rw [A.pool_of_vmPreserved hvm_244]]
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTailPlaced; sep_ac_rfl))
        (hstep244
          x senderPad stB s0 s_244 post_ok u_284 hpad hclamp_none hchains hpq_ne hlik hlik_toNat hrik
          hcl_244 hro_244 hpc_244 hrun_244 halign0 htr_244
          hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
          (by simp only [arm64_norm, *])
          ?_)
      intro sf evs hfree hpc_ret hrun_ret htr_ret hsp_ret hcs_ret _ _
      subst hpost_ok
      apply SepWP.done hpc_ret hrun_ret
      refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfree, afterTrFrom_decRel x.G, htr_ret⟩, by simpa only [sepConj_assoc] using hm⟩
  | some sc =>
    cases hsender_opt : x.G.sender with
    | none => simp [hsender_opt, hsc_opt] at hsc_some
    | some sg =>
      apply sepWP_seq_lscl_ro hcl_5c hro_5c (mid := (blkPl_57).base + 172#64)
      apply sepWP_seq_lscl_ro hcl_5c hro_5c (mid := lsmpl.base 201)
      refine SepWP.fold (optSenderChainAt_some_expose_from A.repAlloc x.ss sg sc) (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨hsrk, hsrk_lt, hsrk_toNat, hclamp_sc, hsrk_cmn, hck_cmn⟩ => ?_
      have hclamp_some : ∀ sc', x.st.senderChain = some sc' →
          clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
        intro sc' h; rw [hsc_opt] at h; cases h; exact hclamp_sc
      rw [stack_456_160_split_deser s0.sp]
      refine SepWP.fold (memRegion_33_to_tag_and_32 (s0.sp - 456#64)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWP.exists_elim fun tag0 => SepWP.exists_elim fun out32 => ?_
      refine SepWP.pure_elim fun hout32_len => ?_
      apply sepWP_seg_ls_vm (Q := (blkPC_57).rebase (blkPl_57).base (hooksException H))
        blkLib_eq_57 checkBlockNoSvc0_57 (mid := lsmpl.base 201); intro _m_strip2
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        fun _m_real2 _hnsp2 => ?_
      refine SepWP.transport_budgetPool
        (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      simp only [State.setMem_setMem]
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_deser _hro_deser
      have hdeser_call :=
        lscall_blk (callerProg := (blkPC_57).rebase (blkPl_57).base H) hDeser hcl_deser
      simp only [deserializePlacedBudgetSpec, withVmPreserved, deserializePlacedSpec, sepConj_assoc] at hdeser_call
      wp_call hdeser_call
        (sg.srk.ptr, sg.srk.bytes, sc.ratchetKey.publicKey,
         s0.sp - 456#64, tag0, out32)
      refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_ac hro_ac
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTailPlaced; sep_ac_rfl))
        (hstepac A.repAlloc x sg sc s0 _ (trFrom10cTailPlaced A lim x stB s0 _) post_ok
          w_208 b_200 d_192 h_188 u_296 u_288 u_284
          hrk hsender_opt hsc_opt hclamp_sc hsrk_cmn hck_cmn hcmn_chains hcl_ac hro_ac
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign0
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) ?_)
      intro s_244 hvm_244 hcl_244 hro_244 hpc_244 hrun_244 htr_244
        hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
      have hpad : (List.replicate 100 0#8).length = 100 := by simp
      rw [show trFrom10cTailPlaced A lim x stB s0 _ = trFrom10cTailPlaced A lim x stB s0 s_244 by
        unfold trFrom10cTailPlaced; rw [A.pool_of_vmPreserved hvm_244]]
      refine SepWP.mono_pre (Entails.of_eq (by unfold trFrom10cTailPlaced; sep_ac_rfl))
        (hstep244
          x (List.replicate 100 0#8) stB s0 s_244 post_ok u_284 hpad hclamp_some hchains hpq_ne hlik hlik_toNat hrik
          hcl_244 hro_244 hpc_244 hrun_244 halign0 htr_244
          hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
          (by simp only [arm64_norm, *])
          ?_)
      intro sf evs hfree hpc_ret hrun_ret htr_ret hsp_ret hcs_ret _ _
      subst hpost_ok
      apply SepWP.done hpc_ret hrun_ret
      refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfree, afterTrFrom_decRel x.G, htr_ret⟩, by simpa only [sepConj_assoc] using hm⟩

theorem trFrom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hRemoteIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A.repAlloc)))
    (hDropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec M A lim)))
    (hDropVecChain : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec M A lim))) :
    subroutine_ok ((blkPC_57).rebase (blkPl_57).base H)
      (blkPl_57).base (trFromPlacedSpec M A lim) :=
  trFrom_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_dealloc)
    (deserialize_vm_placed_ok H)
    hRemoteIk
    hDropSpe
    hDropVecChain

end LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.MainBudget
