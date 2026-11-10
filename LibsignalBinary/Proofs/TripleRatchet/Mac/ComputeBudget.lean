/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux -- shake: keep
import LibsignalBinary.Proofs.Hmac.MD
import LibsignalBinary.Proofs.Hmac.OuterAux
import LibsignalBinary.Proofs.AesCbc.Bytes -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `<SignalMessage>::compute_mac`

Proves `[LibsignalPlacement]` `RustCliAllocBudget` contracts (`computeMacSpecAt`,
`computeMacSpec`, and `computeMacSpecX`) for `<SignalMessage>::compute_mac`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (chunks64 keyToBytes32 sha256IV sha256Pad)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey computeMac)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkLib_eq_60 blkPC_60 blkPl_60 lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalHmac.OuterAux (chunks64_of_length_64)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded LsClInv LsSymState RegsSaved
  bhi_7_false cells_192_8_eq cells_352_18_eq cells_496_18_eq computeMacFramePad
  fold_18_words_496 fold_18_words_496_cells fold_19_words_352 fold_8_words_192
  fold_at_1d408 fold_at_1d434 fold_blk2 fold_blk3 fold_epilogue_post
  fold_long_post fold_long_pre_62 fold_pad_ge_378 fold_pad_lt_378
  fold_post_blk2 fold_post_blk3 fold_post_copy_352 fold_post_memset_352
  fold_pre_compress7 fold_pre_compress8 fold_pre_memcpy_31
  fold_rejoin_31 fold_rejoin_msg_long fold_short_post fold_short_pre fold_stk_192_64
  hmacInnerInit hmacOuterInit hmacStateAt hmacWords64At
  innerHash_len keyToBytes32_length_le_64
  lsMacCompress256Sym lsMacMemcpySym lsMacMemsetSym lsMacRustDeallocSym
  mac_ls_hook_ok_of_mem memRegion_352_152_eq memRegion_352_64_pre_outer_eq
  mkMacEnv mkMacEnv_hState_full mkMacEnv_hState_three mkMacEnv_hState_two
  mkMacEnv_innerB_eq mkMacEnv_innerPadded_drop_eq mkMacEnv_innerPos_eq
  mkMacEnv_innerTail_length mkMacEnv_innerTail_length_lt mkMacEnv_oState1
  ofNat64_xor_63 pointsToBytes_64_352_eq pointsToBytes_shaStateBytes_248_eq
  pointsToBytes_shaStateBytes_288_eq publicKeySerializeStack publicKeySerializeStackX
  spAligned_of_sub_496 stackAt_computeMacAt_eq
  sub62_and_63 sub62_and_mask64 sub62_ushiftRight_6 withLsCodeRoLoaded
  word7_296_eq words7At352 zext64_ofNat8_eq
)
open CryptoVerification.LibsignalTripleRatchet.ComputeMacTactics (clearDepsTac)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec publicKeySerializeEvents
  publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustDeallocExternSpecWithStack rustDeallocExternWithStack_of_rustDealloc
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (
  computeMacEvents computeMacSpec computeMacSpecAt computeMacSpecWithStack computeMacSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux (
  call_pk_serialize_placed_budget_at compress256BudgetSpec compress256_pkStack_placed_budget_ok
  dealloc_pkStack_placed_budget_ok fitsComputeMac_parts
  framelessMemcpyBudget_of_sessionMemcpyRegionBudget hmacCoreAt_nil_eq_words64_aux
  hmacStateAt_eq_words64_sub_aux keyToBytes32_length_aux memcpy_pkStack_placed_budget_ok
  memset_pkStack_placed_budget_ok newFromSliceBudgetSpec newFromSlicePkStackBudgetSpecAt
  newFromSlice_placed_budget_ok newFromSlice_placed_budget_ok_x
  newFromSlice_placed_cro_budget_ok of_sepWP_lscl publicKeySerializeBudgetSpecAt
  rewrap_compress256_lscl rewrap_memset_lscl
  rustDeallocPkStackBudgetSpecAt sepWPp_with_join_state seq_lscl_compute
  session2Compress256BudgetSpec session2Compress256Budget_of_compress256Budget
  session2Compress256PkStackBudgetSpecAt session2MemcpyPkStackBudgetSpecAt
  session2MemsetBudget_of_sessionMemsetRegionBudget session2MemsetPkStackBudgetSpecAt
  subroutine_ok_lscl_of_withLsClState subroutine_ok_lscro_of_withLsClState
  subroutine_ok_withLsClState_of_lscl subroutine_ok_withLsClState_of_lscro
  subroutine_ok_withLsClState_of_plain toBEBytes_len_aux
)

local macro "wp_sync_pool " mid:term : tactic =>
  `(tactic| (
    wp_steps_sync_pool $mid
    try conv => arg 3; simp only [State.setMem_setMem]
    try conv => arg 4; pattern (RustCliAllocBudget.pool _ _ _ _); simp only [State.setMem_setMem]))

local macro "wp_steps_lscl_pool " mid:term : tactic =>
  `(tactic| (
    refine seq_lscl_compute $mid ‹_› ‹_› ?_
    wp_sync_pool $mid
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_step hsym_step))

/-! ## Relocatable `[LibsignalPlacement]` Budget Proof of `<SignalMessage>::compute_mac` -/

set_option maxHeartbeats 1600000 in
private theorem computeMac_join952_placed_budget [LibsignalPlacement]
    {LsClState : State → Prop} [LsClInv LsClState]
    (pkStack : Nat) (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (s0 : State) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcompress : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacCompress256Sym)
      ((session2Compress256PkStackBudgetSpecAt C.F pkStack (s0.sp - 496#64)).withLsClState
        (LsClState := LsClState)))
    (ret senderA : BitVec 64) (sender : IdentityKey) (receiverA : BitVec 64) (receiver : IdentityKey)
    (keyA : BitVec 64) (macKey : BitVec 256) (msgA : BitVec 64) (message : List (BitVec 8)) (st : M.σ)
    {Q Qp : State → SepProp → Prop}
    (hret : ∀ sf,
      sf.pc = s0.readReg64 Reg.lr → sf.status = ExecStatus.Running →
      sf.sp = s0.sp → sf.trace = s0.trace → CalleeSavedPreserved s0 sf →
      SepWPp ((blkPC_60).rebase (blkPl_60).base H) (s0.readReg64 Reg.lr) sf
        ((ret ↦₆₄ okTagVec) ∗
         ((ret + 8#64) ↦ₛ computeMac C.F sender receiver macKey message) ∗
         memRegion (s0.sp - 352#64) 0x98 ∗ memRegion (s0.sp - 192#64) 24 ∗
         memRegion (s0.sp - 160#64) 24 ∗ (∃∗ v, (s0.sp - 168#64) ↦₆₄ v) ∗
         (∃∗ v, (s0.sp - 136#64) ↦₆₄ v) ∗
         (∃∗ s0' : BitVec 64, ∃∗ s1' : BitVec 64, ∃∗ s2' : BitVec 64, ∃∗ s3' : BitVec 64,
          ∃∗ s4' : BitVec 64, ∃∗ s5' : BitVec 64, ∃∗ s6' : BitVec 64, ∃∗ s7' : BitVec 64,
          ∃∗ s8' : BitVec 64, ∃∗ s9' : BitVec 64, ∃∗ s10' : BitVec 64, ∃∗ s11' : BitVec 64,
           ((s0.sp - 96#64) ↦₆₄ s0') ∗ ((s0.sp - 88#64) ↦₆₄ s1') ∗
           ((s0.sp - 80#64) ↦₆₄ s2') ∗ ((s0.sp - 72#64) ↦₆₄ s3') ∗
           ((s0.sp - 64#64) ↦₆₄ s4') ∗ ((s0.sp - 56#64) ↦₆₄ s5') ∗
           ((s0.sp - 48#64) ↦₆₄ s6') ∗ ((s0.sp - 40#64) ↦₆₄ s7') ∗
           ((s0.sp - 32#64) ↦₆₄ s8') ∗ ((s0.sp - 24#64) ↦₆₄ s9') ∗
           ((s0.sp - 16#64) ↦₆₄ s10') ∗ ((s0.sp - 8#64) ↦₆₄ s11')) ∗
         cells (s0.sp - 496#64) 18 ∗ msgA ↦ₛ message ∗
         A.pool lim (M.stepEvents computeMacEvents st) sf ∗
         stackAt (s0.sp - 496#64) pkStack ∗
         receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
         senderA ↦ₛ sender.publicKey.bytes.toList ∗
         keyA ↦ₛ keyToBytes32 macKey ∗ computeMacFramePad s0.sp) Q Qp)
    (sm952 : State)
    (hinv952 :
      LsClState sm952 ∧ True ∧ sm952.pc = (blkPl_60).base + 952#64 ∧
      sm952.status = ExecStatus.Running ∧ sm952.sp = s0.sp - 496#64 ∧ sm952.trace = s0.trace ∧
      sm952.readReg64 (Reg.gpr 19#5) = ret ∧ sm952.readReg64 (Reg.gpr 20#5) = s0.sp - 352#64 ∧
      sm952.readReg64 (Reg.gpr 22#5) = 0x80#64 ∧
      sm952.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos ∧
      sm952.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB ∧
      sm952.readReg64 (Reg.gpr 27#5) = s0.sp - 352#64 ∧
      sm952.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 ∧ calleeSavedVRegs sm952 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_60).rebase (blkPl_60).base H) (s0.readReg64 Reg.lr) sm952
      (words7At352 s0.sp (((mkMacEnv sender receiver macKey message).innerPadded.drop
        ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).take 56) ∗
       (∃∗ w7 : BitVec 64, (s0.sp - 296#64) ↦₆₄ w7) ∗ memRegion (s0.sp - 192#64) 64 ∗
       ((s0.sp - 288#64) ↦ₛ shaStateBytes
         ((chunks64 ((mkMacEnv sender receiver macKey message).innerPadded.take
           ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))).foldl C.F sha256IV)) ∗
       ((s0.sp - 256#64) ↦₆₄ BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB) ∗
       ((s0.sp - 248#64) ↦ₛ shaStateBytes ((mkMacEnv sender receiver macKey message).oState1 C.F)) ∗
       ((s0.sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (s0.sp - 208#64) 8 ∗ cells (s0.sp - 496#64) 18 ∗
       msgA ↦ₛ message ∗ A.pool lim (M.stepEvents computeMacEvents st) sm952 ∗
       stackAt (s0.sp - 496#64) pkStack ∗ receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
       senderA ↦ₛ sender.publicKey.bytes.toList ∗ keyA ↦ₛ keyToBytes32 macKey ∗
       memRegion ret 16 ∗ computeMacFramePad s0.sp ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) Q Qp := by
  rcases hinv952 with ⟨hF952, hsym952, hpc952, hrun952, hsp952, htr952, h952_19, h952_20, h952_22,
    h952_23, h952_24, h952_27, h952_29, hv952⟩
  have hk_len := keyToBytes32_length_aux macKey
  have hbitlen :
      (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB <<< 9) |||
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos <<< 3) =
        BitVec.ofNat 64 (8 * (mkMacEnv sender receiver macKey message).innerMsg.length) :=
    CryptoVerification.LibsignalHmac.MD.bitlen (mkMacEnv sender receiver macKey message) hk_len
  have hlast_blk_len64 :
      ((mkMacEnv sender receiver macKey message).innerPadded.drop
        ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).length = 64 := by
    obtain ⟨hdrop_eq, h56_len⟩ := mkMacEnv_innerPadded_drop_eq sender receiver macKey message
    rw [hdrop_eq, List.length_append, h56_len, toBEBytes_len_aux]
  have hlast_blk_len :
      ((mkMacEnv sender receiver macKey message).innerPadded.drop
        ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).length = 64 * 1 :=
    hlast_blk_len64
  have houter_blk_len64 :
      ((sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64).length = 64 := by
    rw [CryptoVerification.LibsignalHmac.MD.outer_block
      (mkMacEnv sender receiver macKey message) C.F hk_len]
    simp [innerHash_len, toBEBytes_len_aux]
  have houter_blk_len :
      ((sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64).length = 64 * 1 :=
    houter_blk_len64
  have hlast_blk_len_sub :
      (mkMacEnv sender receiver macKey message).innerPadded.length -
        ((mkMacEnv sender receiver macKey message).innerPadded.length - 64) = 64 := by
    simpa only [List.length_drop] using hlast_blk_len64
  have houter_blk_len_sub :
      (sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).length - 64 = 64 := by
    simpa only [List.length_drop] using houter_blk_len64
  conv =>
    arg 4
    rw [cells_192_8_eq s0.sp]
    dsimp only [words7At352]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w7_pad =>
    SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
    SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
    SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
    SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
  refine of_sepWP_lscl ((blkPl_60).base + 996#64) hF952 hsym952 ?_
  wp_sync_pool ((blkPl_60).base + 996#64)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF952a hsym952a
  clear w7_pad b0 b1 b2 b3 b4 b5 b6 b7
  refine SepWPp.fold (fold_pre_compress7 s0.sp sender receiver macKey message _ ?_)
    (by sep_focus) ?_
  · simp only [wp_norm, arm64_norm, *]
  refine of_sepWP_lscl ((blkPl_60).base + 1000#64) hF952a hsym952a ?_
  wp_steps_lscl_pool (lsρ lsMacCompress256Sym)
  wp_call hcompress (s0.sp - 288#64,
    (chunks64 ((mkMacEnv sender receiver macKey message).innerPadded.take
      ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))).foldl C.F sha256IV,
    s0.sp - 192#64,
    (mkMacEnv sender receiver macKey message).innerPadded.drop
      ((mkMacEnv sender receiver macKey message).innerPadded.length - 64),
    1)
  sync_call_pool
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF952b hsym952b
  conv =>
    arg 4
    rw [chunks64_of_length_64 hlast_blk_len64, List.foldl_cons, List.foldl_nil,
      pointsToBytes_shaStateBytes_288_eq s0.sp, memRegion_352_64_pre_outer_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u7 => SepWPp.exists_elim fun u6 =>
    SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 =>
    SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u0 =>
    SepWPp.exists_elim fun b320 => SepWPp.exists_elim fun z319 =>
    SepWPp.exists_elim fun z311 => ?_
  refine of_sepWP_lscl ((blkPl_60).base + 1096#64) hF952b hsym952b ?_
  wp_sync_pool ((blkPl_60).base + 1096#64)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF952c hsym952c
  clear u7 u6 u5 u4 u3 u2 u1 u0 b320 z319 z311
  apply SepWPp.fold (fold_at_1d408 C.F s0.sp sender receiver macKey message _ rfl)
  · sep_focus
  conv =>
    arg 4
    rw [cells_192_8_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w6 => SepWPp.exists_elim fun w7 =>
    SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
    SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
    SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
    SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
  refine of_sepWP_lscl ((blkPl_60).base + 1124#64) hF952c hsym952c ?_
  wp_sync_pool ((blkPl_60).base + 1124#64)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF952d hsym952d
  clear w6 w7 b0 b1 b2 b3 b4 b5 b6 b7
  refine SepWPp.fold (fold_pre_compress8 C.F s0.sp sender receiver macKey message _ ?_)
    (by sep_focus) ?_
  · simp only [wp_norm, arm64_norm, *]
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b_cf => ?_
  refine of_sepWP_lscl ((blkPl_60).base + 1128#64) hF952d hsym952d ?_
  wp_steps_lscl_pool (lsρ lsMacCompress256Sym)
  wp_call hcompress (s0.sp - 248#64,
    (mkMacEnv sender receiver macKey message).oState1 C.F,
    s0.sp - 192#64,
    (sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64,
    1)
  sync_call_pool
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF952e hsym952e
  conv =>
    arg 4
    rw [chunks64_of_length_64 houter_blk_len64, List.foldl_cons, List.foldl_nil,
      pointsToBytes_shaStateBytes_248_eq s0.sp]
    simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := (blkPl_60).base + 1140#64)
  wp_sync_pool ((blkPl_60).base + 1140#64)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  apply SepWPp.fold (fold_at_1d434 s0.sp ret _ _ _ houter_blk_len64)
  · sep_focus
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
    SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
    SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
    SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 =>
    SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 => ?_
  apply SepWPp.of_sepWP (mid := s0.readReg64 Reg.lr)
  wp_sync_pool (s0.readReg64 Reg.lr)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  clear c0 c1 c2 c3 c4 c5 c6 c7 b0 b1 b2 b3 b4 b5 b6 b7 r0 r1
  refine SepWPp.fold (fold_epilogue_post C.F s0.sp ret sender receiver macKey message _ rfl _
    ?_ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  · simp only [wp_norm, arm64_norm, *]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hret _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *]))

set_option maxHeartbeats 3200000 in
private theorem computeMac_join808_placed_budget [LibsignalPlacement]
    {LsClState : State → Prop} [LsClInv LsClState]
    (pkStack : Nat) (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (s0 : State) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcompress : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacCompress256Sym)
      ((session2Compress256PkStackBudgetSpecAt C.F pkStack (s0.sp - 496#64)).withLsClState
        (LsClState := LsClState)))
    (hmemset : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemsetSym)
      ((session2MemsetPkStackBudgetSpecAt pkStack (s0.sp - 496#64)).withLsClState
        (LsClState := LsClState)))
    (ret senderA : BitVec 64) (sender : IdentityKey) (receiverA : BitVec 64) (receiver : IdentityKey)
    (keyA : BitVec 64) (macKey : BitVec 256) (msgA : BitVec 64) (message : List (BitVec 8)) (st : M.σ)
    {Q Qp : State → SepProp → Prop}
    (hret : ∀ sf,
      sf.pc = s0.readReg64 Reg.lr → sf.status = ExecStatus.Running →
      sf.sp = s0.sp → sf.trace = s0.trace → CalleeSavedPreserved s0 sf →
      SepWPp ((blkPC_60).rebase (blkPl_60).base H) (s0.readReg64 Reg.lr) sf
        ((ret ↦₆₄ okTagVec) ∗
         ((ret + 8#64) ↦ₛ computeMac C.F sender receiver macKey message) ∗
         memRegion (s0.sp - 352#64) 0x98 ∗ memRegion (s0.sp - 192#64) 24 ∗
         memRegion (s0.sp - 160#64) 24 ∗ (∃∗ v, (s0.sp - 168#64) ↦₆₄ v) ∗
         (∃∗ v, (s0.sp - 136#64) ↦₆₄ v) ∗
         (∃∗ s0' : BitVec 64, ∃∗ s1' : BitVec 64, ∃∗ s2' : BitVec 64, ∃∗ s3' : BitVec 64,
          ∃∗ s4' : BitVec 64, ∃∗ s5' : BitVec 64, ∃∗ s6' : BitVec 64, ∃∗ s7' : BitVec 64,
          ∃∗ s8' : BitVec 64, ∃∗ s9' : BitVec 64, ∃∗ s10' : BitVec 64, ∃∗ s11' : BitVec 64,
           ((s0.sp - 96#64) ↦₆₄ s0') ∗ ((s0.sp - 88#64) ↦₆₄ s1') ∗
           ((s0.sp - 80#64) ↦₆₄ s2') ∗ ((s0.sp - 72#64) ↦₆₄ s3') ∗
           ((s0.sp - 64#64) ↦₆₄ s4') ∗ ((s0.sp - 56#64) ↦₆₄ s5') ∗
           ((s0.sp - 48#64) ↦₆₄ s6') ∗ ((s0.sp - 40#64) ↦₆₄ s7') ∗
           ((s0.sp - 32#64) ↦₆₄ s8') ∗ ((s0.sp - 24#64) ↦₆₄ s9') ∗
           ((s0.sp - 16#64) ↦₆₄ s10') ∗ ((s0.sp - 8#64) ↦₆₄ s11')) ∗
         cells (s0.sp - 496#64) 18 ∗ msgA ↦ₛ message ∗
         A.pool lim (M.stepEvents computeMacEvents st) sf ∗
         stackAt (s0.sp - 496#64) pkStack ∗
         receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
         senderA ↦ₛ sender.publicKey.bytes.toList ∗
         keyA ↦ₛ keyToBytes32 macKey ∗ computeMacFramePad s0.sp) Q Qp)
    (sm808 : State)
    (hinv808 :
      LsClState sm808 ∧ True ∧ sm808.pc = (blkPl_60).base + 808#64 ∧
      sm808.status = ExecStatus.Running ∧ sm808.sp = s0.sp - 496#64 ∧ sm808.trace = s0.trace ∧
      sm808.readReg64 (Reg.gpr 19#5) = ret ∧ sm808.readReg64 (Reg.gpr 27#5) = s0.sp - 352#64 ∧
      sm808.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 ∧ calleeSavedVRegs sm808 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_60).rebase (blkPl_60).base H) (s0.readReg64 Reg.lr) sm808
      (memRegion (s0.sp - 192#64) 64 ∗
       hmacStateAt (s0.sp - 496#64)
         ((mkMacEnv sender receiver macKey message).hState C.F
           (mkMacEnv sender receiver macKey message).innerB)
         (mkMacEnv sender receiver macKey message).innerB
         ((mkMacEnv sender receiver macKey message).oState1 C.F)
         (mkMacEnv sender receiver macKey message).innerTail ∗
       msgA ↦ₛ message ∗ A.pool lim (M.stepEvents computeMacEvents st) sm808 ∗
       stackAt (s0.sp - 496#64) pkStack ∗ receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
       senderA ↦ₛ sender.publicKey.bytes.toList ∗ memRegion (s0.sp - 352#64) 152 ∗
       keyA ↦ₛ keyToBytes32 macKey ∗ memRegion ret 16 ∗ computeMacFramePad s0.sp ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) Q Qp := by
  have hcompress_join952 := hcompress
  rcases hinv808 with ⟨hF808, hsym808, hpc808, hrun808, hsp808, htr808, h808_19, h808_27, h808_29, hv808⟩
  have htail_len := mkMacEnv_innerTail_length sender receiver macKey message
  have htail_lt := mkMacEnv_innerTail_length_lt sender receiver macKey message
  have hpos_lt : (mkMacEnv sender receiver macKey message).innerPos < 64 :=
    htail_len ▸ htail_lt
  have hzext_tail :
      BitVec.zeroExtend 64 (BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerPos) =
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos :=
    zext64_ofNat8_eq hpos_lt
  have hxor_tail :
      BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos ^^^ 63#64 =
        BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) :=
    ofNat64_xor_63 hpos_lt
  have hsub63_toNat :
      (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).toNat =
        63 - (mkMacEnv sender receiver macKey message).innerPos := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  conv =>
    arg 4
    rw [hmacStateAt_eq_words64_sub_aux (s0.sp - 496#64)
      ((mkMacEnv sender receiver macKey message).hState C.F
        (mkMacEnv sender receiver macKey message).innerB)
      (mkMacEnv sender receiver macKey message).innerB
      ((mkMacEnv sender receiver macKey message).oState1 C.F)
      (mkMacEnv sender receiver macKey message).innerTail htail_lt,
      memRegion_352_152_eq s0.sp, cells_352_18_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 =>
    SepWPp.exists_elim fun d6 => SepWPp.exists_elim fun d7 =>
    SepWPp.exists_elim fun d8 => SepWPp.exists_elim fun d9 =>
    SepWPp.exists_elim fun d10 => SepWPp.exists_elim fun d11 =>
    SepWPp.exists_elim fun d12 => SepWPp.exists_elim fun d13 =>
    SepWPp.exists_elim fun d14 => SepWPp.exists_elim fun d15 =>
    SepWPp.exists_elim fun d16 => SepWPp.exists_elim fun d17 =>
    SepWPp.exists_elim fun pad_tail => ?_
  conv =>
    arg 4
    simp only [hmacWords64At, arm64_norm, sepConj_assoc]
  refine of_sepWP_lscl ((blkPl_60).base + 864#64) hF808 hsym808 ?_
  wp_sync_pool ((blkPl_60).base + 864#64)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF808a hsym808a
  apply SepWPp.fold (fold_18_words_496_cells s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  · sep_focus
  conv =>
    arg 4
    rw [word7_296_eq s0.sp htail_lt pad_tail.2]
    simp only [sepConj_assoc]
  refine of_sepWP_lscl ((blkPl_60).base + 888#64) hF808a hsym808a ?_
  wp_sync_pool ((blkPl_60).base + 888#64)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF808b hsym808b
  clear d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
  apply SepWPp.fold (fold_post_copy_352 s0.sp
    ((mkMacEnv sender receiver macKey message).hState C.F
      (mkMacEnv sender receiver macKey message).innerB)
    (mkMacEnv sender receiver macKey message).innerB
    ((mkMacEnv sender receiver macKey message).oState1 C.F)
    htail_lt pad_tail.2)
  · sep_focus
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b_pad0 => ?_
  conv =>
    arg 4
    arg 2; arg 1
    rw [htail_len]
  conv =>
    arg 4
    arg 2; arg 2; arg 1
    rw [htail_len]
  refine of_sepWP_lscl ((blkPl_60).base + 896#64) hF808b hsym808b ?_
  wp_steps_lscl_pool (lsρ lsMacMemsetSym)
  wp_call hmemset
    (s0.sp - 352#64 +
      BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos + 1#64,
     0#8,
     63 - (mkMacEnv sender receiver macKey message).innerPos)
  sync_call_pool
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF808c hsym808c
  conv =>
    arg 4
    rw [← htail_len]
  apply SepWPp.fold (fold_post_memset_352 s0.sp (mkMacEnv sender receiver macKey message).innerTail)
  · sep_focus
  conv =>
    arg 4
    arg 1
    rw [htail_len]
  refine sepWPp_with_join_state
    (fun sm =>
      words7At352 s0.sp (((mkMacEnv sender receiver macKey message).innerPadded.drop
        ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).take 56) ∗
      (∃∗ w7 : BitVec 64, (s0.sp - 296#64) ↦₆₄ w7) ∗
      memRegion (s0.sp - 192#64) 64 ∗
      ((s0.sp - 288#64) ↦ₛ shaStateBytes
        ((chunks64 ((mkMacEnv sender receiver macKey message).innerPadded.take
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))).foldl C.F sha256IV)) ∗
      ((s0.sp - 256#64) ↦₆₄ BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB) ∗
      ((s0.sp - 248#64) ↦ₛ shaStateBytes ((mkMacEnv sender receiver macKey message).oState1 C.F)) ∗
      ((s0.sp - 216#64) ↦₆₄ 1#64) ∗
      memRegion (s0.sp - 208#64) 8 ∗
      cells (s0.sp - 496#64) 18 ∗
      msgA ↦ₛ message ∗
      A.pool lim (M.stepEvents computeMacEvents st) sm ∗
      stackAt (s0.sp - 496#64) pkStack ∗
      receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
      senderA ↦ₛ sender.publicKey.bytes.toList ∗
      keyA ↦ₛ keyToBytes32 macKey ∗
      memRegion ret 16 ∗
      computeMacFramePad s0.sp ∗
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
    (fun sm =>
      LsClState sm ∧ True ∧ sm.pc = (blkPl_60).base + 952#64 ∧
      sm.status = ExecStatus.Running ∧ sm.sp = s0.sp - 496#64 ∧ sm.trace = s0.trace ∧
      sm.readReg64 (Reg.gpr 19#5) = ret ∧ sm.readReg64 (Reg.gpr 20#5) = s0.sp - 352#64 ∧
      sm.readReg64 (Reg.gpr 22#5) = 0x80#64 ∧
      sm.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos ∧
      sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB ∧
      sm.readReg64 (Reg.gpr 27#5) = s0.sp - 352#64 ∧
      sm.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
    (computeMac_join952_placed_budget pkStack C M A lim H s0 hsp_align hcompress_join952
      ret senderA sender receiverA receiver keyA macKey msgA message st hret)
    (fun hjoin952 => ?_)
  by_cases hpad : (mkMacEnv sender receiver macKey message).innerPos < 56
  · have hhi_ult :
        (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hhi_ult' :
        ¬ (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64 = true := by
      rw [hhi_ult]; decide
    have hhi_ne :
        BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) ≠ 7#64 := by
      intro heq; have := congrArg BitVec.toNat heq; simp [BitVec.toNat_ofNat] at this; omega
    have hhi_beq :
        (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) == 7#64) = false :=
      beq_false_of_ne hhi_ne
    have hhi_gt :
        (7#64 : BitVec 64).ult
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hhi_ule :
        (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ule 7#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    refine of_sepWP_lscl ((blkPl_60).base + 952#64) hF808c hsym808c ?_
    wp_sync_pool ((blkPl_60).base + 952#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_pad1 hsym_pad1
    apply SepWPp.fold (fold_pad_lt_378 C.F s0.sp sender receiver macKey message hpad)
    · sep_focus
    exact hjoin952
      ⟨hF_pad1, hsym_pad1,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      (Entails.of_eq (by sep_ac_rfl))
  · have hpad_ge : 56 ≤ (mkMacEnv sender receiver macKey message).innerPos := by omega
    have hhi_le : 63 - (mkMacEnv sender receiver macKey message).innerPos ≤ 7 := by omega
    have hhi_gt :
        (7#64 : BitVec 64).ult
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hhi_ule :
        (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ule 7#64 = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hhi_cond :
        ((!(BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64) &&
         !((BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) == 7#64)) = false :=
      bhi_7_false hhi_le
    have hhi_cond' :
        ¬ ((!(BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64) &&
           !((BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) == 7#64)) = true := by
      rw [hhi_cond]; decide
    have hpadBlk_len64 :
        ((mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
          List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8).length = 64 := by
      simp [htail_len]; omega
    have hpadBlk_len :
        ((mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
          List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8).length = 64 * 1 :=
      hpadBlk_len64
    have hpadBlk_len_sub :
        (mkMacEnv sender receiver macKey message).innerPos + 1 +
          (63 - (mkMacEnv sender receiver macKey message).innerPos) = 64 := by omega
    have hpadBlk_len_sub2 :
        (mkMacEnv sender receiver macKey message).innerPos +
          (63 - (mkMacEnv sender receiver macKey message).innerPos + 1) = 64 := by omega
    conv =>
      arg 4
      rw [pointsToBytes_64_352_eq s0.sp hpadBlk_len64, cells_192_8_eq s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
      SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
      SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
      SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
    refine of_sepWP_lscl ((blkPl_60).base + 932#64) hF808c hsym808c ?_
    wp_sync_pool ((blkPl_60).base + 932#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_pad2a hsym_pad2a
    clear b0 b1 b2 b3 b4 b5 b6 b7
    have hpadBlk_len64' : ((mkMacEnv sender receiver macKey message).innerTail ++
        0x80#8 :: List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8).length = 64 := by
      simpa using hpadBlk_len64
    apply SepWPp.fold (fold_8_words_192 s0.sp hpadBlk_len64')
    · sep_focus
    conv => arg 4; pattern ((s0.sp - 192#64) ↦ₛ _); rw [show
      (mkMacEnv sender receiver macKey message).innerTail ++
        0x80#8 :: List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 =
      (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
        List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 by simp]
    refine of_sepWP_lscl ((blkPl_60).base + 952#64) hF_pad2a hsym_pad2a ?_
    wp_steps_lscl_pool (lsρ lsMacCompress256Sym)
    wp_call hcompress (s0.sp - 288#64,
      (mkMacEnv sender receiver macKey message).hState C.F
        (mkMacEnv sender receiver macKey message).innerB,
      s0.sp - 192#64,
      (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
        List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8,
      1)
    sync_call_pool
    wp_sync_pool ((blkPl_60).base + 952#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_pad2b hsym_pad2b
    conv => arg 4; pattern ((s0.sp - 192#64) ↦ₛ _); try rw [show
      (mkMacEnv sender receiver macKey message).innerTail ++
        0x80#8 :: List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 =
      (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
        List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 by simp]
    conv => arg 4; pattern ((s0.sp - 288#64) ↦ₛ _); try rw [show
      (mkMacEnv sender receiver macKey message).innerTail ++
        0x80#8 :: List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 =
      (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
        List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 by simp]
    apply SepWPp.fold (fold_pad_ge_378 C.F s0.sp sender receiver macKey message _ hpad_ge)
    · sep_focus
    exact hjoin952
      ⟨hF_pad2b, hsym_pad2b,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      (Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 1600000 in
theorem computeMac_placed_ok_of_hooks_gen [LibsignalPlacement]
    {LsClState : State → Prop} [LsClInv LsClState]
    (pkStack : Nat) (hbound : pkStack + 496 < 2 ^ 64)
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hnew_at : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114)
      ((newFromSlicePkStackBudgetSpecAt C.F pkStack).withLsClState (LsClState := LsClState)))
    (hpk_at : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205)
      ((publicKeySerializeBudgetSpecAt M A lim pkStack).withLsClState (LsClState := LsClState)))
    (hmemcpy_all : ∀ sp_cur, subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemcpySym)
      ((session2MemcpyPkStackBudgetSpecAt pkStack sp_cur).withLsClState (LsClState := LsClState)))
    (hcompress_all : ∀ sp_cur, subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacCompress256Sym)
      ((session2Compress256PkStackBudgetSpecAt C.F pkStack sp_cur).withLsClState
        (LsClState := LsClState)))
    (hdealloc : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacRustDeallocSym)
      ((rustDeallocPkStackBudgetSpecAt M A lim pkStack).withLsClState (LsClState := LsClState)))
    (hmemset_all : ∀ sp_cur, subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemsetSym)
      ((session2MemsetPkStackBudgetSpecAt pkStack sp_cur).withLsClState (LsClState := LsClState))) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (blkPl_60).base
      ((computeMacSpecAt M A lim C.F pkStack).withLsClState (LsClState := LsClState)) := by
  simp only [Spec.withLsClState, computeMacSpecAt, computeMacSpecWithStack,
    stackAt_computeMacAt_eq pkStack hbound,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x_st s0
  have hmemcpy := hmemcpy_all (s0.sp - 496#64)
  have hcompress := hcompress_all (s0.sp - 496#64)
  have hmemset := hmemset_all (s0.sp - 496#64)
  have hcompress_join808 := hcompress_all (s0.sp - 496#64)
  have hmemset_join808 := hmemset_all (s0.sp - 496#64)
  clear hmemcpy_all hcompress_all hmemset_all
  rcases x_st with ⟨⟨ret, senderA, sender, receiverA, receiver, keyA, macKey, msgA, message⟩, st⟩
  dsimp only
  have ⟨hfits_pk1, hfits_pk2, hst_final⟩ :=
    fitsComputeMac_parts ‹FitsEnv M lim st _›
  set st1 := M.stepEvents publicKeySerializeEvents st
  set st2 := M.stepEvents (rustDeallocEvents 33 1) st1
  set st3 := M.stepEvents publicKeySerializeEvents st2
  set st4 := M.stepEvents (rustDeallocEvents 33 1) st3
  have hk_len := keyToBytes32_length_aux macKey
  have hk_le : (keyToBytes32 macKey).length ≤ 64 := keyToBytes32_length_le_64 macKey
  have hlen_s : sender.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hlen_r : receiver.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hlen_r31 : (receiver.publicKey.serialize.take 31).length = 31 := by simp [PublicKey.serialize]
  have hlen_r2 : (receiver.publicKey.serialize.drop 31).length = 2 := by simp [PublicKey.serialize]
  have hblk2_len :
      (sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31).length = 64 * 1 := by
    simp [PublicKey.serialize]
  have hx6_eq : s0.readReg64 (Reg.gpr 6#5) = BitVec.ofNat 64 message.length := by
    rw [← ‹(s0.readReg64 (Reg.gpr 6#5)).toNat = message.length›]
    simp
  refine of_sepWP_lscl (lsmpl.base 114) ‹LsClState s0› trivial ?_
  wp_sync_pool (lsmpl.base 114)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF1 hsym1
  refine of_sepWP_lscl ((blkPl_60).base + 76#64) hF1 hsym1 ?_
  wp_call hnew_at ⟨s0.sp - 352#64, keyA, keyToBytes32 macKey⟩
  sync_call_pool
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF1a hsym1a
  clear hF1 hsym1
  conv =>
    arg 4
    rw [hmacCoreAt_nil_eq_words64_aux C.F (s0.sp - 344#64) (keyToBytes32 macKey),
      cells_496_18_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 =>
    SepWPp.exists_elim fun c12 => SepWPp.exists_elim fun c13 =>
    SepWPp.exists_elim fun c14 => SepWPp.exists_elim fun c15 =>
    SepWPp.exists_elim fun c16 => SepWPp.exists_elim fun c17 =>
    SepWPp.exists_elim fun pad0 => ?_
  conv =>
    arg 4
    simp only [hmacWords64At, arm64_norm, sepConj_assoc]
  refine of_sepWP_lscl (lsmpl.base 205) hF1a hsym1a ?_
  wp_sync_pool (lsmpl.base 205)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF1b hsym1b
  clear c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
  apply SepWPp.fold (fold_19_words_352 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  · sep_focus
  apply SepWPp.fold
    (fold_18_words_496 s0.sp (hmacInnerInit C.F (keyToBytes32 macKey)) 1
      (hmacOuterInit C.F (keyToBytes32 macKey)) pad0.1 pad0.2)
  · sep_focus
  apply call_pk_serialize_placed_budget_at (s0 := s0) hpk_at ((blkPl_60).base + 164#64)
    (s0.sp - 496#64) senderA sender.publicKey st hfits_pk1
  · sep_focus
  · refine ⟨hF1b, hsym1b, by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      spAligned_of_sub_496 s0.sp (by simp only [wp_norm, arm64_norm, *]) hsp_align,
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  intro sf2 hF2 hsym2 hpc2 hrun2 hsp2 hcs2 hptr1 hx1_2 htr2
  simp only [RegsSaved, wp_norm, arm64_norm, *] at hcs2
  rcases hcs2 with ⟨h2_19, h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, h2_29, h2_v⟩
  refine of_sepWP_lscl (lsmpl.base 205) hF2 hsym2 ?_
  wp_steps_lscl_pool (lsρ lsMacMemcpySym)
  refine seq_lscl_compute (lsρ lsMacRustDeallocSym) ‹_› ‹_› ?_
  wp_call hmemcpy (s0.sp - 496#64, sf2.readReg64 (Reg.gpr 0#5), sender.publicKey.serialize)
  sync_call_pool
  wp_sync_pool (lsρ lsMacRustDeallocSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF_step1 hsym_step1
  wp_call hdealloc ((sf2.readReg64 (Reg.gpr 0#5), sender.publicKey.serialize), st1)
  wp_sync_pool (lsmpl.base 205)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF2a hsym2a
  conv =>
    arg 4
    pattern (stackAt _ pkStack)
    arg 1
    simp only [wp_norm, arm64_norm, *]
  apply call_pk_serialize_placed_budget_at (s0 := s0) hpk_at ((blkPl_60).base + 400#64)
    (s0.sp - 496#64) receiverA receiver.publicKey st2 hfits_pk2
  · sep_focus
  · refine ⟨hF2a, hsym2a, by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      spAligned_of_sub_496 s0.sp (by simp only [wp_norm, arm64_norm, *]) hsp_align,
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  intro sf5 hF5 hsym5 hpc5 hrun5 hsp5 hcs5 hptr2 hx1_5 htr5
  simp only [RegsSaved, wp_norm, arm64_norm, *] at hcs5
  rcases hcs5 with ⟨h5_19, h5_20, h5_21, h5_22, h5_23, h5_24, h5_25, h5_26, h5_27, h5_28, h5_29, h5_v⟩
  refine of_sepWP_lscl ((blkPl_60).base + 544#64) hF5 hsym5 ?_
  wp_sync_pool ((blkPl_60).base + 544#64)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF5a hsym5a
  apply SepWPp.fold (fold_pre_memcpy_31 s0.sp (sf5.readReg64 (Reg.gpr 0#5))
    receiver.publicKey.serialize 33#8 hlen_r)
  · sep_focus
  refine of_sepWP_lscl ((blkPl_60).base + 548#64) hF5a hsym5a ?_
  wp_steps_lscl_pool (lsρ lsMacMemcpySym)
  wp_call hmemcpy (s0.sp - 463#64, sf5.readReg64 (Reg.gpr 0#5),
    receiver.publicKey.serialize.take 31)
  sync_call_pool
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF5b hsym5b
  apply SepWPp.fold (fold_blk2 s0.sp sender.publicKey.serialize
    (receiver.publicKey.serialize.take 31) hlen_s)
  · sep_focus
  refine of_sepWP_lscl ((blkPl_60).base + 576#64) hF5b hsym5b ?_
  wp_steps_lscl_pool (lsρ lsMacCompress256Sym)
  wp_call hcompress (s0.sp - 432#64, hmacInnerInit C.F (keyToBytes32 macKey),
    s0.sp - 496#64, sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31, 1)
  sync_call_pool
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF5c hsym5c
  apply SepWPp.fold (fold_post_blk2 s0.sp
    (sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31)
    receiver.publicKey.serialize hblk2_len hlen_r)
  · sep_focus
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b63 => ?_
  refine of_sepWP_lscl ((blkPl_60).base + 644#64) hF5c hsym5c ?_
  wp_steps_lscl_pool (lsρ lsMacMemcpySym)
  wp_call hmemcpy (s0.sp - 496#64, sf5.readReg64 (Reg.gpr 0#5) + 31#64,
    receiver.publicKey.serialize.drop 31)
  sync_call_pool
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF5d hsym5d
  apply SepWPp.fold (fold_rejoin_31 (sf5.readReg64 (Reg.gpr 0#5))
    receiver.publicKey.serialize hlen_r)
  · sep_focus
  refine of_sepWP_lscl ((blkPl_60).base + 660#64) hF5d hsym5d ?_
  wp_steps_lscl_pool (lsρ lsMacRustDeallocSym)
  wp_call hdealloc ((sf5.readReg64 (Reg.gpr 0#5), receiver.publicKey.serialize), st3)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF5e hsym5e
  have hlen_toNat : (BitVec.ofNat 64 message.length).toNat = message.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  conv =>
    arg 4
    pattern (stackAt _ pkStack)
    arg 1
    simp only [wp_norm, arm64_norm, *]
  have hst4_eq : M.stepEvents (rustDeallocEvents 33 1) st3 = M.stepEvents computeMacEvents st :=
    hst_final
  conv =>
    arg 4
    rw [hst4_eq, mkMacEnv_hState_two C.F sender receiver macKey message,
      mkMacEnv_oState1 C.F sender receiver macKey message]
  apply SepWPp.fold (fold_stk_192_64 s0.sp _ _)
  · sep_focus
  simp only [wp_norm, arm64_norm, *]
    at hsp_sf_6 h_79 h_80 h_81 h_82 h_83 h_84 h_85 h_86 h_87 h_88 hcs_sf_6 hvregs_6 hpost_6
  run_tac clearDepsTac #[`sf, `sf2, `sf_1, `sf_2, `sf5, `sf_3, `sf_4, `sf_5,
    `m, `m_1, `m_2, `m_3, `m_4, `m_5, `m_6, `m_7, `m_8, `m_9, `m_10, `m_11,
    `m_12, `m_13, `m_14, `m_15, `pad0, `b63]
  refine sepWPp_with_join_state
    (fun sm =>
      memRegion (s0.sp - 192#64) 64 ∗
      hmacStateAt (s0.sp - 496#64)
        ((mkMacEnv sender receiver macKey message).hState C.F
          (mkMacEnv sender receiver macKey message).innerB)
        (mkMacEnv sender receiver macKey message).innerB
        ((mkMacEnv sender receiver macKey message).oState1 C.F)
        (mkMacEnv sender receiver macKey message).innerTail ∗
      msgA ↦ₛ message ∗
      A.pool lim (M.stepEvents computeMacEvents st) sm ∗
      stackAt (s0.sp - 496#64) pkStack ∗
      receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
      senderA ↦ₛ sender.publicKey.bytes.toList ∗
      memRegion (s0.sp - 352#64) 152 ∗
      keyA ↦ₛ keyToBytes32 macKey ∗
      memRegion ret 16 ∗
      computeMacFramePad s0.sp ∗
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
    (fun sm =>
      LsClState sm ∧
      True ∧
      sm.pc = (blkPl_60).base + 808#64 ∧
      sm.status = ExecStatus.Running ∧
      sm.sp = s0.sp - 496#64 ∧
      sm.trace = s0.trace ∧
      sm.readReg64 (Reg.gpr 19#5) = ret ∧
      sm.readReg64 (Reg.gpr 27#5) = s0.sp - 352#64 ∧
      sm.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (computeMac_join808_placed_budget pkStack C M A lim H s0 hsp_align
      (rewrap_compress256_lscl hcompress_join808) (rewrap_memset_lscl hmemset_join808)
      ret senderA sender receiverA receiver keyA macKey msgA message st
      (fun sf hpcf hrunf hspf htrf hcsf => by
        apply SepWPp.of_sepWP_ret
        refine SepWP.done hpcf hrunf ⟨fun hm => ?_, ⟨hspf, hcsf⟩⟩
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
          sepConj_assoc] at hm ⊢
        rcases hm with ⟨v168, v136, s0', s1', s2', s3', s4', s5', s6', s7', s8', s9', s10', s11', hm⟩
        refine ⟨v168, v136, s0', s1', s2', s3', s4', s5', s6', s7', s8', s9', s10', s11', ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨htrf, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩))
    (fun hjoin808 => ?_)
  by_cases hshort : message.length < 62
  · have hult62 : (BitVec.ofNat 64 message.length).ult 62#64 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hpos_short :
        2#8 + BitVec.zeroExtend 8 (BitVec.ofNat 64 message.length) =
          BitVec.ofNat 8 (message.length + 2) := by
      bv_omega
    apply SepWPp.fold (fold_short_pre s0.sp message.length hshort)
    · sep_focus
    refine of_sepWP_lscl ((blkPl_60).base + 808#64) hF5e hsym5e ?_
    wp_steps_lscl_pool (lsρ lsMacMemcpySym)
    wp_call hmemcpy (s0.sp - 494#64, msgA, message)
    sync_call_pool
    wp_sync_pool ((blkPl_60).base + 808#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_sh hsym_sh
    apply SepWPp.fold (fold_short_post C.F s0.sp sender receiver macKey message hshort _ rfl)
    · sep_focus
    exact hjoin808
      ⟨hF_sh, hsym_sh,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      (Entails.of_eq (by sep_ac_rfl))
  · have hge62 : 62 ≤ message.length := by omega
    have hult62 : (BitVec.ofNat 64 message.length).ult 62#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hult62' : ¬ (BitVec.ofNat 64 message.length).ult 62#64 = true := by
      rw [hult62]; decide
    have hlen_m62 : (message.take 62).length = 62 := by simp; omega
    have hlen_m62_min : min 62 message.length = 62 := by omega
    have hblk3_len : (receiver.publicKey.serialize.drop 31 ++ message.take 62).length = 64 * 1 := by
      simp [PublicKey.serialize]; omega
    refine of_sepWP_lscl ((blkPl_60).base + 704#64) hF5e hsym5e ?_
    wp_sync_pool ((blkPl_60).base + 704#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_lg1 hsym_lg1
    apply SepWPp.fold (fold_long_pre_62 s0.sp msgA message 2#8 hge62)
    · sep_focus
    refine of_sepWP_lscl ((blkPl_60).base + 708#64) hF_lg1 hsym_lg1 ?_
    wp_steps_lscl_pool (lsρ lsMacMemcpySym)
    wp_call hmemcpy (s0.sp - 494#64, msgA, message.take 62)
    sync_call_pool
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_lg2 hsym_lg2
    apply SepWPp.fold (fold_blk3 s0.sp (receiver.publicKey.serialize.drop 31)
      (message.take 62) hlen_r2)
    · sep_focus
    refine of_sepWP_lscl ((blkPl_60).base + 736#64) hF_lg2 hsym_lg2 ?_
    wp_steps_lscl_pool (lsρ lsMacCompress256Sym)
    wp_call hcompress (s0.sp - 432#64, (mkMacEnv sender receiver macKey message).hState C.F 2,
      s0.sp - 496#64, receiver.publicKey.serialize.drop 31 ++ message.take 62, 1)
    sync_call_pool
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_lg3 hsym_lg3
    conv =>
      arg 4
      rw [mkMacEnv_hState_three C.F sender receiver macKey message hge62]
    have hmsg_lt : message.length < 2 ^ 63 := ‹message.length < 2 ^ 63›
    have hlsr6 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 =
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull :=
      sub62_ushiftRight_6 hge62 hmsg_lt
    have hand_mask : (BitVec.ofNat 64 message.length - 62#64) &&& 0x7fffffffffffffc0#64 =
        BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull) :=
      sub62_and_mask64 hge62 hmsg_lt
    have hand_63 : (BitVec.ofNat 64 message.length - 62#64) &&& 63#64 =
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length := by
      rw [mkMacEnv_innerTail_length, mkMacEnv_innerPos_eq sender receiver macKey message hge62]
      exact sub62_and_63 hge62 hmsg_lt
    have hpos_long :
        BitVec.zeroExtend 8
            (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length) =
          BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerTail.length := by
      bv_omega
    have htail_lt := mkMacEnv_innerTail_length_lt sender receiver macKey message
    have htail_toNat :
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length).toNat =
          (mkMacEnv sender receiver macKey message).innerTail.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hnFull_toNat :
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull).toNat =
          (mkMacEnv sender receiver macKey message).nFull := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      change (message.length - 62) / 64 < 2 ^ 64
      omega
    have hfull_len :
        ((message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)).length =
          64 * (mkMacEnv sender receiver macKey message).nFull := by
      rw [List.length_take, List.length_drop]
      exact Nat.min_eq_left (Nat.mul_div_le (message.length - 62) 64)
    have hfull_len_min :
        min (64 * (mkMacEnv sender receiver macKey message).nFull) (message.length - 62) =
          64 * (mkMacEnv sender receiver macKey message).nFull := by
      simpa only [List.length_take, List.length_drop] using hfull_len
    apply SepWPp.fold (fold_post_blk3 s0.sp msgA sender receiver macKey message
      (receiver.publicKey.serialize.drop 31 ++ message.take 62) hblk3_len hge62)
    · sep_focus
    conv =>
      arg 4
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b63' => ?_
    by_cases hnFull : (mkMacEnv sender receiver macKey message).nFull = 0
    · have hcbz1 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 = 0#64 := by
        rw [hlsr6, hnFull]
      have hinnerB_eq : (mkMacEnv sender receiver macKey message).innerB = 3 := by
        rw [mkMacEnv_innerB_eq sender receiver macKey message hge62, hnFull]
      refine of_sepWP_lscl ((blkPl_60).base + 808#64) hF_lg3 hsym_lg3 ?_
      wp_steps_lscl_pool (lsρ lsMacMemcpySym)
      wp_call hmemcpy (s0.sp - 496#64,
        msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).innerTail)
      sync_call_pool
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hF_lg4a hsym_lg4a
      conv =>
        arg 4
        rw [← hinnerB_eq]
      apply SepWPp.fold (fold_rejoin_msg_long msgA sender receiver macKey message hge62)
      · sep_focus
      apply SepWPp.fold (fold_long_post C.F s0.sp sender receiver macKey message _ _ rfl rfl)
      · sep_focus
      exact hjoin808
        ⟨hF_lg4a, hsym_lg4a,
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
        (Entails.of_eq (by sep_ac_rfl))
    · have hcbz1 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 ≠ 0#64 := by
        rw [hlsr6]
        intro heq
        apply hnFull
        have := congrArg BitVec.toNat heq
        simpa [hnFull_toNat] using this
      have hcbz1_ne : BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull ≠ 0#64 := by
        rw [← hlsr6]; exact hcbz1
      have hcbz1_beq :
          (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull == 0#64) = false :=
        beq_false_of_ne hcbz1_ne
      have hcbz1_beq' :
          ¬ (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull == 0#64) = true := by
        rw [hcbz1_beq]; decide
      have hblk_word1 :
          3#64 + BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull =
            BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB := by
        rw [mkMacEnv_innerB_eq sender receiver macKey message hge62]
        bv_omega
      refine of_sepWP_lscl ((blkPl_60).base + 808#64) hF_lg3 hsym_lg3 ?_
      wp_steps_lscl_pool (lsρ lsMacCompress256Sym)
      refine seq_lscl_compute (lsρ lsMacMemcpySym) ‹_› ‹_› ?_
      wp_call hcompress (s0.sp - 432#64, (mkMacEnv sender receiver macKey message).hState C.F 3,
        msgA + 62#64,
        (message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).nFull)
      sync_call_pool
      wp_sync_pool (lsρ lsMacMemcpySym)
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hF_step2 hsym_step2
      wp_call hmemcpy (s0.sp - 496#64,
        msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).innerTail)
      sync_call_pool
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hF_lg4b hsym_lg4b
      conv =>
        arg 4
        rw [mkMacEnv_hState_full C.F sender receiver macKey message hge62]
      apply SepWPp.fold (fold_rejoin_msg_long msgA sender receiver macKey message hge62)
      · sep_focus
      apply SepWPp.fold (fold_long_post C.F s0.sp sender receiver macKey message _ _ rfl rfl)
      · sep_focus
      exact hjoin808
        ⟨hF_lg4b, hsym_lg4b,
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
        (Entails.of_eq (by sep_ac_rfl))

/-! ## Top-Level Placed Budget Contracts (`withLsCodeLoaded` & `withLsCodeRoLoaded`) -/

theorem computeMac_placed_ok_of_contracts [LibsignalPlacement]
    (pkStack : Nat) (hbound : pkStack + 496 < 2 ^ 64 := by decide)
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      ((newFromSlicePkStackBudgetSpecAt C.F pkStack).withLsClState
        (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeBudgetSpecAt M A lim pkStack)))
    (hmemcpy : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemcpySym) framelessMemcpyBudgetSpec)
    (hcompress : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacCompress256Sym) (session2Compress256BudgetSpec C.F))
    (hdealloc : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacRustDeallocSym) (rustDeallocExternSpecWithStack M A lim pkStack))
    (hmemset : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemsetSym) sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (blkPl_60).base
      (withLsCodeLoaded lsmpl (computeMacSpecAt M A lim C.F pkStack)) := by
  have hmemset' := session2MemsetBudget_of_sessionMemsetRegionBudget hmemset
  exact subroutine_ok_lscl_of_withLsClState
    (computeMac_placed_ok_of_hooks_gen pkStack hbound C M A lim H hnew
      (subroutine_ok_withLsClState_of_lscl hpk)
      (fun sp_cur => memcpy_pkStack_placed_budget_ok sp_cur hmemcpy)
      (fun sp_cur => compress256_pkStack_placed_budget_ok sp_cur hcompress)
      (subroutine_ok_withLsClState_of_plain (dealloc_pkStack_placed_budget_ok hdealloc))
      (fun sp_cur => memset_pkStack_placed_budget_ok sp_cur hmemset'))

theorem computeMac_placed_cro_ok_of_contracts [LibsignalPlacement]
    (pkStack : Nat) (hbound : pkStack + 496 < 2 ^ 64 := by decide)
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      ((newFromSlicePkStackBudgetSpecAt C.F pkStack).withLsClState
        (LsClState := fun s => LibsignalCodeRoLoaded lsmpl s.mem)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeRoLoaded lsmpl (publicKeySerializeBudgetSpecAt M A lim pkStack)))
    (hmemcpy : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemcpySym) framelessMemcpyBudgetSpec)
    (hcompress : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacCompress256Sym) (session2Compress256BudgetSpec C.F))
    (hdealloc : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacRustDeallocSym) (rustDeallocExternSpecWithStack M A lim pkStack))
    (hmemset : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemsetSym) sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (blkPl_60).base
      (withLsCodeRoLoaded lsmpl (computeMacSpecAt M A lim C.F pkStack)) := by
  have hmemset' := session2MemsetBudget_of_sessionMemsetRegionBudget hmemset
  exact subroutine_ok_lscro_of_withLsClState
    (computeMac_placed_ok_of_hooks_gen pkStack hbound C M A lim H hnew
      (subroutine_ok_withLsClState_of_lscro hpk)
      (fun sp_cur => memcpy_pkStack_placed_budget_ok sp_cur hmemcpy)
      (fun sp_cur => compress256_pkStack_placed_budget_ok sp_cur hcompress)
      (subroutine_ok_withLsClState_of_plain (dealloc_pkStack_placed_budget_ok hdealloc))
      (fun sp_cur => memset_pkStack_placed_budget_ok sp_cur hmemset'))

theorem computeMac_placed_cro_ok [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114) (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeRoLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (blkPl_60).base
      (withLsCodeRoLoaded lsmpl (computeMacSpec M A lim C.F)) :=
  computeMac_placed_cro_ok_of_contracts publicKeySerializeStack (by decide) C M A lim H
    (newFromSlice_placed_cro_budget_ok C hnew) hpk
    (framelessMemcpyBudget_of_sessionMemcpyRegionBudget (mac_ls_hook_ok_of_mem (i := 60) hmemcpy))
    (session2Compress256Budget_of_compress256Budget (mac_ls_hook_ok_of_mem (i := 60) hcompress))
    (rustDeallocExternWithStack_of_rustDealloc (stk := publicKeySerializeStack) (by decide)
      (by decide) (mac_ls_hook_ok_of_mem (i := 60) hdealloc))
    (mac_ls_hook_ok_of_mem (i := 60) hmemset)

theorem computeMac_placed_ok [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114) (withLsCodeLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (blkPl_60).base
      (withLsCodeLoaded lsmpl (computeMacSpec M A lim C.F)) :=
  computeMac_placed_ok_of_contracts publicKeySerializeStack (by decide) C M A lim H
    (newFromSlice_placed_budget_ok C hnew) hpk
    (framelessMemcpyBudget_of_sessionMemcpyRegionBudget (mac_ls_hook_ok_of_mem (i := 60) hmemcpy))
    (session2Compress256Budget_of_compress256Budget (mac_ls_hook_ok_of_mem (i := 60) hcompress))
    (rustDeallocExternWithStack_of_rustDealloc (stk := publicKeySerializeStack) (by decide)
      (by decide) (mac_ls_hook_ok_of_mem (i := 60) hdealloc))
    (mac_ls_hook_ok_of_mem (i := 60) hmemset)

theorem computeMac_placed_ok_x [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114) (withLsCodeLoaded lsmpl (newFromSliceBudgetSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256BudgetSpec C.F))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (blkPl_60).base
      (withLsCodeLoaded lsmpl (computeMacSpecX M A lim C.F)) :=
  computeMac_placed_ok_of_contracts publicKeySerializeStackX (by decide) C M A lim H
    (newFromSlice_placed_budget_ok_x C hnew) hpk
    (framelessMemcpyBudget_of_sessionMemcpyRegionBudget (mac_ls_hook_ok_of_mem (i := 60) hmemcpy))
    (session2Compress256Budget_of_compress256Budget (mac_ls_hook_ok_of_mem (i := 60) hcompress))
    (rustDeallocExternWithStack_of_rustDealloc (stk := publicKeySerializeStackX) (by decide)
      (by decide) (mac_ls_hook_ok_of_mem (i := 60) hdealloc))
    (mac_ls_hook_ok_of_mem (i := 60) hmemset)

end LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget
