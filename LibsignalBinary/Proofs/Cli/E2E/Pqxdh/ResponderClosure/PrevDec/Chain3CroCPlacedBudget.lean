/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainMessageKeysGExt
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `VerNe.Chain3` (Block `516`) Part C (`MessageKeys` Push and Top-Level Closure)

Total-correctness (`RustCliAllocBudget M`) verification of the `Vec<MessageKey>` `grow_one` / push
step and full `MessageKeys` (`tag = 4`) slice (`chain3MessageKeys_cro_placed_ok`), closing
`message::merge<Chain> [local#4]` (Block `516`) under `StoreKit.withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (MessageKeyGenerator maxMessageKeys)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  lsmpl withLsCl
)
open CryptoVerification.RustHeap (RustAlloc arrayAt arrayAt_concat arrayAt_nil vecAt vecBuf vecHeader vecOf vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced
  lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns cliGhostExterns_shim
)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
)
open CryptoVerification.E2E.Record (pbBytes pbVarint)
open CryptoVerification.E2E.Record.DeserializeSeed (
  chunks104_6QWAt_dst_eq_receiverChains chunks104_6QWAt_entails_memRegion104_receiverChains
  chunks104_6QWAt_stack_eq_receiverChains memRegion104_eq_exists_chunks104_6QWAt_receiverChains
  sep_ac_seedChain sliceCursorAfter_append_eq_seedChain
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainField ChainG ChainMergeGenGhost chainGAfter prostMsgKeyAt
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG (
  arrayAt_prostMsgKeyAt_move_bytes beq_ofNat_cap_false chainField_eq_key_of_tag4
  chainGAfter_keys_length_le chainGAfter_succ_of_key chainG_payload_split
  drop_fields_flatMap_enc_of_key encMessageKey_eq_pb encMessageKey_length_lt128
  lenField_4_encMessageKey_eq memRegion_spare_split_of_lt mem_keys_of_key_mem_fields
  ofNat_add_one_eq prostMsgKeyAt_move_chunks104 ptr_madd_104_eq
  sliceCursorAfter_tag4_combine spAligned_of_sp_eq
)
open CryptoVerification.CliHandshake.Placed (blkLib_eq_516 blkPl_516 lsProg_516)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  Chain3MkRegs SepWPp.of_sepWP_lscl_c3
  c3mkChainNoKeys c3mk_prostMsgKeyAt_fold c3mk_push_spAligned c3mk_sp0_aligned_of_sub_240
  chain3GAt chain3GAt_keys_split chain3GAt_push_key chain3PCPlacedAtW
  chain3SavedRegs chain3SavedRegs_c3mk_split chainMerge3SubStackX
  extract_withLsCl_post_c3 intro_withLsCl_c3 libsignalCodeLoaded_preserve_c3
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  finishGrowStackX framelessMemcpyBudgetSpec framelessMemcpy_hookOk
  noAllocShimBudgetSpec noAllocShim_hookOk
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  GrowOne104Env growOne104Events growOne104SpecX growOneChainSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (
  ChainPrefixEnv boundedRustEvs_growOne104Env fitsEnv_step_boundedRustEvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget (CliAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks bumpGhost
  cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemmove_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget (
  cliAllocHooks_to_bumpGhost
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudgetAux (
  sepWPp_mono_pre_c3
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudget (
  Chain3CalleesCroPlacedW Chain3MessageKeysCroStmt SepWPp.bind_lscro
  chain3CalleesCro_of_hooks chain3Entry_cro_placed_ok chainMerge3W_cro_placed_ok
  chainMerge5_cro_of_block segStepG_keep_cro
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudget (
  chain3ChainKey_cro_placed_ok chain3Srk_cro_placed_ok
  chainPrefixEnv_step_field fitsEnv_rem_at_field pool_eq_of_vm_c3
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudgetAux (
  c3_bm_call_vec1_cro chainFieldKeys_length_le_enc chainGAfter_keys_length_le_payload
  flatMap_chainFieldKeys_length_le_enc growOne104_req_le_mallocMax growOne104_req_le_payload
  step_c3cnt_key_placed_vm step_c3cnt_store_placed_vm step_c3hd_head_placed_vm
  step_c3hd_key4_placed_vm step_c3hd_len_placed_vm step_c3ihead_placed_vm
  step_c3seed_icont_placed_vm step_c3seed_key_placed_vm
  step_mkCnt_cro step_mkHead_cro step_mkSeed_cro tag4_field_enc_length_ge
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverPrevDecodeCroPlacedAt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux (
  ChainMerge5CroPlacedOkExt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudget (
  overPrevDecode_cro_placed_of_hooks_chain5
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudgetAux (
  c3_bm_call_vec1_cro chainFieldKeys_length_le_enc chainGAfter_keys_length_le_payload
  flatMap_chainFieldKeys_length_le_enc growOne104_req_le_mallocMax growOne104_req_le_payload
  step_mkCnt_cro step_mkHead_cro step_mkSeed_cro tag4_field_enc_length_ge
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## `Vec<MessageKey>` Representation and Stack Split Helpers -/

private theorem stackAt_c3Sub_to_growOneB (sp : BitVec 64) :
    stackAt sp chainMerge3SubStackX =
      stackAt sp (464 + finishGrowStackX) ∗
        memRegion (sp - BitVec.ofNat 64 chainMerge3SubStackX)
          (chainMerge3SubStackX - (464 + finishGrowStackX)) := by
  unfold stackAt
  have hle : (chainMerge3SubStackX - (464 + finishGrowStackX)) + (464 + finishGrowStackX) =
      chainMerge3SubStackX := by decide
  have hsplit := ProofLib.memRegion_split
    (sp - BitVec.ofNat 64 chainMerge3SubStackX)
    (chainMerge3SubStackX - (464 + finishGrowStackX))
    (464 + finishGrowStackX) (by decide)
  have hadj : sp - BitVec.ofNat 64 chainMerge3SubStackX +
      BitVec.ofNat 64 (chainMerge3SubStackX - (464 + finishGrowStackX)) =
      sp - BitVec.ofNat 64 (464 + finishGrowStackX) := by
    have hsub : BitVec.ofNat 64 (chainMerge3SubStackX - (464 + finishGrowStackX)) =
        BitVec.ofNat 64 chainMerge3SubStackX - BitVec.ofNat 64 (464 + finishGrowStackX) := by decide
    rw [hsub]; bv_omega
  rw [hle, hadj] at hsplit
  rw [hsplit, sepConj_comm]

private theorem c3mk_vecOf_keys_openA (A_rep : RustAlloc) (a : BitVec 64)
    (keys : List MessageKeyGenerator) :
    vecOf A_rep 104 8 (fun mk b => prostMsgKeyAt A_rep mk b) (a + 0x30#64) keys ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        (if cap = 0#64 then emp
         else A_rep.live ptr (cap.toNat * 104) 8 ∗
           arrayAt (fun mk b => prostMsgKeyAt A_rep mk b) 104 ptr keys ∗
           memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) := by
  unfold vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e38, e40, h0]
  by_cases hcap : cap = 0#64 <;> simp only [hcap, ↓reduceIte] <;> exact Entails.of_eq (by ac_rfl)

private theorem c3mk_vecBuf_keys_full_openA (A_rep : RustAlloc) (cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (hfull : keys.length = cap.toNat) :
    (if cap = 0#64 then emp
     else A_rep.live ptr (cap.toNat * 104) 8 ∗
       arrayAt (fun mk b => prostMsgKeyAt A_rep mk b) 104 ptr keys ∗
       memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun mk b' => prostMsgKeyAt A_rep mk b') 104 b keys⌝ ∗
        (if cap = 0#64 then emp else A_rep.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H := by
  by_cases hcap0 : cap = 0#64
  · subst hcap0; have hks : keys = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hks; simp only [↓reduceIte, BitVec.toNat_ofNat]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_); rw [emp_sepConj]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp, arrayAt_nil]; exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hrem : (cap.toNat - keys.length) * 104 = 0 := by omega
    rw [hrem, ProofLib.memRegion_zero, sepConj_emp]
    refine Entails.trans (sepConj_mono_right (arrayAt_prostMsgKeyAt_move_bytes A_rep keys ptr)) ?_
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro H
    rw [← sepConj_assoc, sepConj_comm (A_rep.live _ _ _), sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    refine Entails.sepExists_right bs (Entails.sepExists_right H ?_)
    rw [← hbs_cap]; exact Entails.pure_right ⟨rfl, hmov⟩ (Entails.of_eq (by ac_rfl))

private theorem c3mk_vecBuf_keys_not_full_openA (A_rep : RustAlloc) (cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (hlt : keys.length + 1 ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else A_rep.live ptr (cap.toNat * 104) 8 ∗
       arrayAt (fun mk b => prostMsgKeyAt A_rep mk b) 104 ptr keys ∗
       memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) =
      (A_rep.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun mk b => prostMsgKeyAt A_rep mk b) 104 ptr keys ∗
        memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
          ((cap.toNat - (keys.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hlt
  have hmr := memRegion_spare_split_of_lt cap ptr keys.length hlt hcap_lt
  simp only [hcap0, ↓reduceIte] at hmr ⊢
  rw [hmr]

private theorem c3mk_vecOf_keys_push_foldA (A_rep : RustAlloc) (a cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) :
    ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
      A_rep.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr keys ∗
      prostMsgKeyAt A_rep mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
        ((cap.toNat - (keys.length + 1)) * 104) ⊢
    vecOf A_rep 104 8 (fun m b => prostMsgKeyAt A_rep m b) (a + 0x30#64) (keys ++ [mk]) := by
  have hne0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hcap_le
  have hlen : (keys ++ [mk]).length = keys.length + 1 := by simp
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hif : (if cap = 0 then emp else A_rep.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr (keys ++ [mk]) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys ++ [mk]).length * 104))
          ((cap.toNat - (keys ++ [mk]).length) * 104)) =
      A_rep.live ptr (cap.toNat * 104) 8 ∗
      (arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr keys ∗
        prostMsgKeyAt A_rep mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
        ((cap.toNat - (keys.length + 1)) * 104) := by
    rw [hlen, arrayAt_concat]; change (if cap = 0#64 then emp else _) = _; simp [hne0]
  rw [e38, e40, hif, hlen]
  have hgrp :
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1))) ∗
      (⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A_rep.live ptr (cap.toNat * 104) 8 ∗
          (arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr keys ∗
            prostMsgKeyAt A_rep mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
          memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap.toNat - (keys.length + 1)) * 104))) =
      ⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
        A_rep.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr keys ∗
        prostMsgKeyAt A_rep mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
          ((cap.toNat - (keys.length + 1)) * 104)) := by ac_rfl
  rw [hgrp]; exact Entails.pure_right ⟨hcap_le, hcap_lt, hptr⟩ (Entails.refl _)

/-! ## Budget-Threaded `grow_one` Call and VM-Preserving Push Steppers -/

private theorem c3_grow_call_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a cap ptr sp0 ret_pc : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hfull : n = cap.toNat) (hbs : bs.length = n * 104) (hptr : ptr ≠ 0#64)
    (hbound : n ≤ maxMessageKeys)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st_cur (GrowOne104Env cap))
    (hpc : s.pc = lsmpl.base 43) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = a + 0x30#64)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      n + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          (A.repAlloc).live ptr' (cap'.toNat * 104) 8 ∗ (ptr' ↦ₛ bs) ∗
          memRegion (ptr' + BitVec.ofNat 64 (n * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗
          A.pool lim (M.stepEvents (growOne104Events cap) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp else (A.repAlloc).live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs, hfull]
  have hmax_le : max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by
    unfold maxMessageKeys at hbound; omega
  have hmax_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63 := by
    unfold maxMessageKeys at hbound; omega
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  let F_grow : SepProp :=
    memRegion (sp0 - 240#64 - BitVec.ofNat 64 chainMerge3SubStackX)
      (chainMerge3SubStackX - (464 + finishGrowStackX)) ∗ F
  intro R' hm hL
  have hm_call : s.mem ⊨
      (withLsCl lsmpl (growOneChainSpecX M A lim)).pre
        ((a + 0x30#64, cap, ptr, bs), st_cur) s ∗ (F_grow ∗ R') := by
    refine intro_withLsCl_c3 hcl ?_
    rw [stackAt_c3Sub_to_growOneB (sp0 - 240#64)] at hm
    unfold growOneChainSpecX growOne104SpecX
    dsimp only
    have h0 : (0 : BitVec 64) = 0#64 := rfl
    rw [e38, h0, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hbs_cap, hptr, hmax_le, hfit⟩, ?_⟩
    dsimp only [F_grow]
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm
  obtain ⟨sm, hst1,
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hm_post⟩ | ⟨_, hm_pan⟩ | ⟨_, _, hm_ex⟩ | ⟨_, hm_oom⟩, _⟩ :=
    (hC.grow).no_fault_before_outcome ((a + 0x30#64, cap, ptr, bs), st_cur)
      (F_grow ∗ R') s hpc hrun hm_call hsp_align hL
  · rw [hlr] at hpcm
    rw [hsp] at hspm
    obtain ⟨hclm, hm_post⟩ := extract_withLsCl_post_c3 hm_post
    unfold growOneChainSpecX growOne104SpecX at hm_post
    dsimp only at hm_post
    rw [e38, hsp] at hm_post
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post
    rcases hm_post with ⟨ptr', hm_post⟩
    have hm_pure : sm.mem ⊨
        ⌜sm.trace = s.trace⌝ ∗
        (⌜ptr' ≠ 0⌝ ∗
          (((a + 0x30#64) ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗
            ((a + 0x38#64) ↦₆₄ ptr') ∗
            A.live ptr' (max (2 * cap.toNat) 4 * 104) 8 ∗ (ptr' ↦ₛ bs) ∗
            memRegion (ptr' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) ∗
            A.pool lim (M.stepEvents (growOne104Events cap) st_cur) sm ∗
            stackAt (sp0 - 240#64) (464 + finishGrowStackX) ∗ F_grow ∗ R')) :=
      Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm_post
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_pure
    rcases hm_pure with ⟨htrm, hptr', hm_rest⟩
    let cap' : BitVec 64 := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    have hcap'_toNat : cap'.toNat = max (2 * cap.toNat) 4 := by
      simp only [cap', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : max (2 * cap.toNat) 4 < 2 ^ 64)]
    have hcap'_le : n + 1 ≤ cap'.toNat := by omega
    have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
    have hcap'_ne0 : cap' ≠ 0#64 := by intro h0; rw [h0] at hcap'_le; simp at hcap'_le
    have hmr_split :
        memRegion (ptr' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) =
          memRegion (ptr' + BitVec.ofNat 64 (n * 104)) 104 ∗
            memRegion (ptr' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) := by
      have hmr := memRegion_spare_split_of_lt cap' ptr' n hcap'_le hcap'_lt
      simp only [hcap'_ne0, ↓reduceIte] at hmr
      rw [hbs, ← hcap'_toNat, ← hfull]
      exact hmr
    have hm_next : sm.mem ⊨
        ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          (A.repAlloc).live ptr' (cap'.toNat * 104) 8 ∗ (ptr' ↦ₛ bs) ∗
          memRegion (ptr' + BitVec.ofNat 64 (n * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗
          A.pool lim (M.stepEvents (growOne104Events cap) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F) ∗ R' := by
      have hlive_eq : A.live ptr' (max (2 * cap.toNat) 4 * 104) 8 =
          (A.repAlloc).live ptr' (cap'.toNat * 104) 8 := by rw [hcap'_toNat]; rfl
      rw [hmr_split, hlive_eq] at hm_rest
      dsimp only [F_grow, cap', RustCliAllocBudget.repAlloc] at hm_rest ⊢
      rw [stackAt_c3Sub_to_growOneB (sp0 - 240#64)]
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm_rest
    obtain ⟨sf, hst2, hout2⟩ :=
      hnext sm cap' ptr' hcap'_le hcap'_lt hptr' hpcm hrunm hspm hclm
        (htrm.trans htr) hcsm R' hm_next (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout2⟩
  · dsimp only [withLsCl, growOneChainSpecX, growOne104SpecX] at hm_pan
    exact False.elim (not_satisfies_false_sepConj hm_pan)
  · exact False.elim (not_satisfies_false_sepConj hm_ex)
  · exact False.elim (not_satisfies_false_sepConj hm_oom)

private theorem step_c3mk_push4d_full_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (a bufRef slot ptr_rest cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hfull : keys.length = cap.toNat)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x244#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 43 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0x178#64 →
      s1.readReg64 .x0 = a + 0x30#64 → s1.readReg64 .x25 = cap →
      Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗ F) Q Qp := by
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by
    simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false :=
    bne_self_eq_false _
  have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = true := by rw [hfull]; simp
  change s.pc = (blkPl_516).base + 0x244#64 at hpc
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 rest.length := hx25
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 43) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 43)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 11 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [h20, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

private theorem step_c3mk_push4d_notfull_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (a bufRef slot ptr_rest cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hcap_le : keys.length ≤ cap.toNat) (hfull : keys.length ≠ cap.toNat)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x244#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0x178#64 →
      s1.status = .Running → s1.sp = s.sp → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s.trace →
      s1.readReg64 .x20 = a → s1.readReg64 .x24 = 104#64 →
      s1.readReg64 .x25 = BitVec.ofNat 64 keys.length →
      Chain3MkRegs s s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗ F) Q Qp := by
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by
    simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false :=
    bne_self_eq_false _
  have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = false := beq_ofNat_cap_false hcap_le hfull
  have hbne_cap : (BitVec.ofNat 64 keys.length != cap) = true := by
    rw [bne_iff_ne, ne_eq, ← beq_iff_eq, hbeq_cap]; decide
  change s.pc = (blkPl_516).base + 0x244#64 at hpc
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 rest.length := hx25
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x178#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0x178#64)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 9 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [wp_norm, arm64_norm]) (by simp only [h20, wp_norm, arm64_norm])
    (by simp only [h24, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

private theorem step_c3mk_push4d_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64)
    (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (c_pay_len : Nat) (hle_pay : keys.length ≤ c_pay_len) (hbound : keys.length ≤ maxMessageKeys)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hfit : FitsEnv M lim st_cur (BoundedRustEvs 1 (256 * (c_pay_len + 16))))
    (hpc : s.pc = lsmpl.base 516 + 0x244#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 240#64) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs_grow : List AllocEvent),
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      BoundedRustEvs 1 (256 * (c_pay_len + 16)) evs_grow →
      sm.pc = lsmpl.base 516 + 0x178#64 →
      sm.status = .Running → sm.sp = sp0 - 240#64 → sm.spAligned = true →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace → Chain3MkRegs s sm →
      sm.readReg64 .x20 = a → sm.readReg64 .x24 = 104#64 →
      sm.readReg64 .x25 = BitVec.ofNat 64 keys.length →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          (A.repAlloc).live ptr' (cap'.toNat * 104) 8 ∗
          arrayAt (fun m b => prostMsgKeyAt A.repAlloc m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap'.toNat - (keys.length + 1)) * 104) ∗
          A.pool lim (M.stepEvents evs_grow st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        vecOf A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b) (a + 0x30#64) keys ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun _ _ => False) := by
  apply SepWPp.fold (c3mk_vecOf_keys_openA A.repAlloc a keys) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_le, hcap_lt, hptr⟩
  by_cases hfull : keys.length = cap.toNat
  · apply SepWPp.fold (c3mk_vecBuf_keys_full_openA A.repAlloc cap ptr keys hfull) (by sep_frame)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_cap, hmov⟩
    have hbs_len : bs.length = keys.length * 104 := by rw [hbs_cap, hfull]
    have hreq_le : max (2 * cap.toNat) 4 * 104 ≤ 256 * (c_pay_len + 16) := by omega
    have hmax_mal : max (2 * cap.toNat) 4 * 104 ≤ MallocngMaxAllocSize :=
      growOne104_req_le_mallocMax (hfull ▸ hbound)
    have hfit_grow : FitsEnv M lim st_cur (GrowOne104Env cap) := fun e he =>
      hfit e (BoundedRustEvs.mono (Nat.le_refl 1) hreq_le (boundedRustEvs_growOne104Env hmax_mal he))
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗
        ((if cap = 0#64 then emp else (A.repAlloc).live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H ∗
          A.pool lim st_cur s ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine step_c3mk_push4d_full_placed_vm a bufRef slot ptr_rest cap ptr keys rest hfull
      hpc hrun hcl hx19 hx20 hx24 hx25 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hx25_1 hregs1
    have hsp_align1 : s1.spAligned = true := spAligned_of_sp_eq hsp1 hsp_align
    refine sepWPp_mono_pre_c3
      (P' := (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp else (A.repAlloc).live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗ H ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_grow_call_cro hC a cap ptr sp0 (lsmpl.base 516 + 0x178#64) bs keys.length
      hfull hbs_len hptr hbound hfit_grow hpc1 hrun1 (hsp1.trans hsp) hsp_align1 hcl1
      (htr1.trans htr) hlr1 hx0_1 ?_
    intro sm cap' ptr' hcap'_le hcap'_lt hptr' hpcm hrunm hspm hclm htrm hcsm
    have hregs_m : Chain3MkRegs s sm := hregs1.trans (.of_calleeSaved hcsm)
    have hx25_m : sm.readReg64 .x25 = BitVec.ofNat 64 keys.length := by
      rw [hcsm.2.2.2.2.2.2.1, hx25_1, hfull, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hsp_align_m : sm.spAligned = true := spAligned_of_sp_eq (hspm.trans hsp.symm) hsp_align
    have hevs_grow : BoundedRustEvs 1 (256 * (c_pay_len + 16)) (growOne104Events cap) :=
      BoundedRustEvs.mono (Nat.le_refl 1) hreq_le (boundedRustEvs_growOne104Env hmax_mal rfl)
    apply SepWPp.fold (hmov ptr') (by sep_frame)
    refine sepWPp_mono_pre_c3 ?_ (hnext sm cap' ptr' (growOne104Events cap)
      hcap'_le hcap'_lt hptr' hevs_grow hpcm hrunm hspm hsp_align_m hclm htrm hregs_m
      (hregs_m.2.1.trans hx20) (hregs_m.2.2.2.2.2.1.trans hx24) hx25_m)
    dsimp only [RustCliAllocBudget.repAlloc]; exact sep_ac_seedChain (by ac_rfl)
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    rw [c3mk_vecBuf_keys_not_full_openA A.repAlloc cap ptr keys hcap_le' hcap_lt]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗
        ((A.repAlloc).live ptr (cap.toNat * 104) 8 ∗
          arrayAt (fun m b => prostMsgKeyAt A.repAlloc m b) 104 ptr keys ∗
          memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap.toNat - (keys.length + 1)) * 104) ∗
          A.pool lim st_cur s ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine step_c3mk_push4d_notfull_placed_vm a bufRef slot ptr_rest cap ptr keys rest
      hcap_le hfull hpc hrun hcl hx19 hx20 hx24 hx25 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hx20_1 hx24_1 hx25_1 hregs1
    have hsp_align1 : s1.spAligned = true := spAligned_of_sp_eq hsp1 hsp_align
    refine sepWPp_mono_pre_c3 ?_ (hnext s1 cap ptr [] hcap_le' hcap_lt hptr
      (BoundedRustEvs.nil _ _) hpc1 hrun1 (hsp1.trans hsp) hsp_align1 hcl1 (htr1.trans htr)
      hregs1 hx20_1 hx24_1 hx25_1)
    rw [pool_eq_of_vm_c3 A lim st_cur hvm1]
    change _ ⊢ (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
      ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
      (A.repAlloc).live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAt A.repAlloc m b) 104 ptr keys ∗
      memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
        ((cap.toNat - (keys.length + 1)) * 104) ∗
      A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
    exact sep_ac_seedChain (by ac_rfl)

private theorem step_c3mk_push4e_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (A_rep : RustAlloc) (a cap' ptr' sp0 : BitVec 64)
    (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63)
    (hptr : ptr' ≠ 0#64)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x178#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 keys.length)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 0xa8#64 →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → sm.trace = s0.trace →
      Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecOf A_rep 104 8 (fun m b => prostMsgKeyAt A_rep m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 0xe8#64) 104) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        A_rep.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
          ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAt A_rep mk (sp0 - 0xe8#64)) ∗ F) Q Qp := by
  have hsp_align_bv : s.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hmadd := ptr_madd_104_eq ptr' keys.length
  have hadd1 := ofNat_add_one_eq keys.length
  change s.pc = (blkPl_516).base + 0x178#64 at hpc
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 keys.length := hx25
  apply SepWPp.fold (prostMsgKeyAt_move_chunks104 A_rep (sp0 - 0xe8#64) mk) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro q0; apply SepWPp.exists_elim; intro q1
  apply SepWPp.exists_elim; intro q2; apply SepWPp.exists_elim; intro q3
  apply SepWPp.exists_elim; intro q4; apply SepWPp.exists_elim; intro q5
  apply SepWPp.exists_elim; intro w6; apply SepWPp.exists_elim; intro H
  apply SepWPp.pure_left; intro hmov
  apply SepWPp.fold
    (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains
      (ptr' + BitVec.ofNat 64 (keys.length * 104)))) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWPp.exists_elim; intro d0; apply SepWPp.exists_elim; intro d1
  apply SepWPp.exists_elim; intro d2; apply SepWPp.exists_elim; intro d3
  apply SepWPp.exists_elim; intro d4; apply SepWPp.exists_elim; intro d5
  apply SepWPp.exists_elim; intro dw6
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0xa8#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0xa8#64)
  intro m_strip
  conv => arg 4; rw [chunks104_6QWAt_stack_eq_receiverChains sp0 q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104))
      d0 d1 d2 d3 d4 d5 dw6]
  iterate 21 wp_step
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains
      (ptr' + BitVec.ofNat 64 (keys.length * 104)) q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_stack_eq_receiverChains sp0 q0 q1 q2 q3 q4 q5 w6]
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  apply SepWPp.fold (hmov (ptr' + BitVec.ofNat 64 (keys.length * 104))) (by sep_frame)
  apply SepWPp.fold
    (chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 0xe8#64) q0 q1 q2 q3 q4 q5 w6)
    (by sep_frame)
  apply SepWPp.fold
    (c3mk_vecOf_keys_push_foldA A_rep a cap' ptr' keys mk hcap_le hcap_lt hptr)
    (by sep_frame)
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm])
    hcl1 hvm (by simp only [htr, wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  exact sep_ac_seedChain (by ac_rfl)

theorem step_mkPush_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator)
    (mk : MessageKeyGenerator) (rest : List (BitVec 8))
    (c_pay_len : Nat) (hle_pay : keys.length ≤ c_pay_len) (hbound : keys.length ≤ maxMessageKeys)
    {st_cur : M.σ} {s0 s : State} {F : SepProp}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hfit : FitsEnv M lim st_cur (BoundedRustEvs 1 (256 * (c_pay_len + 16))))
    (hpc : s.pc = chain3PCPlacedAtW ext 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State) (evs_grow : List AllocEvent),
      sm.pc = chain3PCPlacedAtW ext 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace → Chain3MkRegs s sm →
      BoundedRustEvs 1 (256 * (c_pay_len + 16)) evs_grow →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          vecOf A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b) (a + 48#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 232#64) 104 ∗
          A.pool lim (M.stepEvents evs_grow st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        vecOf A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b) (a + 48#64) keys ∗
        prostMsgKeyAt A.repAlloc mk (sp0 - 232#64) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun _ _ => False) := by
  have hsp_align : s.spAligned = true := c3mk_push_spAligned hsp halign
  dsimp only [chain3PCPlacedAtW] at hpc hnext
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
      vecOf A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b) (a + 0x30#64) keys ∗
      A.pool lim st_cur s ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      (prostMsgKeyAt A.repAlloc mk (sp0 - 0xe8#64) ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3mk_push4d_cro hC a bufRef slot ptr_rest sp0 keys rest c_pay_len hle_pay hbound
    hfit hpc hrun hsp hsp_align hcl htr hx19 hx20 hx24 hx25 ?_
  intro s4 cap' ptr' evs_grow hcap'_le hcap'_lt hptr' hevs_grow
    hpc4 hrun4 hsp4 hsp_align4 hcl4 htr4 hregs4 hx20_4 hx24_4 hx25_4
  refine sepWPp_mono_pre_c3
    (P' := (((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
      (A.repAlloc).live ptr' (cap'.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAt A.repAlloc m b) 104 ptr' keys ∗
      memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
      memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
        ((cap'.toNat - (keys.length + 1)) * 104) ∗
      prostMsgKeyAt A.repAlloc mk (sp0 - 0xe8#64)) ∗
      ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        A.pool lim (M.stepEvents evs_grow st_cur) s4 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3mk_push4e_placed_vm A.repAlloc a cap' ptr' sp0 keys mk hcap'_le hcap'_lt hptr'
    hpc4 hrun4 hsp4 hsp_align4 hcl4 htr4 hx20_4 hx24_4 hx25_4 ?_
  intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hregs5
  refine sepWPp_mono_pre_c3 ?_
    (hnext s5 evs_grow hpc5 hrun5 hsp5 hcl5 htr5 (hregs4.trans hregs5) hevs_grow)
  rw [pool_eq_of_vm_c3 A lim (M.stepEvents evs_grow st_cur) hvm5]
  exact sep_ac_seedChain (by ac_rfl)

/-! ## `chain3MessageKeys_cro_placed_ok` (`Chain3MessageKeysCroStmt`) -/

theorem chain3MessageKeys_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks) :
    Chain3MessageKeysCroStmt M A lim ext := by
  intro hC x st R s0 k s hk htag ⟨hcro, hs⟩
  refine segStepG_keep_cro hcro ?_
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hOk, hlen_pay, hfit, evs, hevs_pfx, hmem⟩
  obtain ⟨mk, hfl⟩ := chainField_eq_key_of_tag4 htag
  have hmk_mem : mk ∈ x.c.keys := mem_keys_of_key_mem_fields (hfl ▸ List.getElem_mem hk)
  have hseed : mk.seed.length = 32 := hOk.2.2.2.1 mk hmk_mem
  have hbound : (chainGAfter x.c k).keys.length ≤ maxMessageKeys :=
    le_trans (chainGAfter_keys_length_le x.c k) hOk.2.2.2.2
  have hkeys_le_pay : (chainGAfter x.c k).keys.length ≤ x.c.payload.length :=
    chainGAfter_keys_length_le_payload x.c k
  have henc_ge36 : 36 ≤ (x.c.fields[k]'hk).enc.length :=
    tag4_field_enc_length_ge hk hfl hseed
  have hFitRem : FitsEnv M lim (M.stepEvents evs st)
      (BoundedRustEvs (8 * (x.c.fields[k]'hk).enc.length) (256 * (x.c.payload.length + 16))) :=
    fitsEnv_rem_at_field hk hevs_pfx hfit
  have hfit_seed : FitsEnv M lim (M.stepEvents evs st)
      (BoundedRustEvs 3 (2 * mk.seed.length + 8)) := fun e he =>
    hFitRem e (BoundedRustEvs.mono (by omega) (by omega) he)
  have halign : s0.sp &&& 15#64 = 0#64 := c3mk_sp0_aligned_of_sub_240
    (by
      have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
      rwa [hsp] at h1)
  let pfx : List (BitVec 8) :=
    encodeVarint (BitVec.ofNat 64 x.c.enc.length) ++ (x.c.fields.take k).flatMap ChainField.enc
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail
  let body : List (BitVec 8) := pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed
  have hpay_eq : x.c.payload ++ x.tail =
      pfx ++ (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) := by
    dsimp only [body]
    rw [chainG_payload_split x.c k x.tail, drop_fields_flatMap_enc_of_key hk hfl x.tail,
      lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]; rfl
  have hcur_open : sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
      ((x.c.fields.drop k).flatMap ChainField.enc ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗ sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
        (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) := by
    have hrem : (x.c.fields.drop k).flatMap ChainField.enc ++ x.tail =
        0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest) := by
      dsimp only [body]
      rw [drop_fields_flatMap_enc_of_key hk hfl x.tail,
        lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]; rfl
    rw [hrem, hpay_eq, sliceCursorAfter_append_eq_seedChain]
  have hmk_lt : body.length < 128 := by
    dsimp only [body]; rw [← encMessageKey_eq_pb hseed]; exact encMessageKey_length_lt128 hseed
  have htail_le : x.tail.length ≤ rest.length := by simp [rest]
  have hlen_a : 2 + (body.length + rest.length) < 2 ^ 62 := by
    have h := hlen_pay; rw [hpay_eq] at h
    simp only [List.length_append, List.length_cons] at h ⊢; omega
  have hlen_b : (pbVarint 1 mk.counter.toNat ++ (pbBytes 5 mk.seed ++ rest)).length < 2 ^ 62 := by
    dsimp only [body] at hlen_a; simp only [List.length_append] at hlen_a ⊢; omega
  have hlen_c : (pbBytes 5 mk.seed ++ rest).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_b ⊢; omega
  have hk_lt : mk.seed.length < 128 := by omega
  let savedRest : SepProp :=
    memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 128#64) 48 ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ memRegion (s0.sp - 56#64) 8 ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hmem_init : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗ memRegion (s0.sp - 232#64) 104 ∗
        sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        A.pool lim (M.stepEvents evs st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64)
          (chainGAfter x.c k).keys ∗
          c3mkChainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
          (x.ptr ↦ₛ pfx) ∗ savedRest)) ∗ R := by
    rw [chain3GAt_keys_split, hcur_open, chain3SavedRegs_c3mk_split] at hmem
    dsimp only [savedRest]; exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  intro hL
  have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗ memRegion (s0.sp - 232#64) 104 ∗
        sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        A.pool lim (M.stepEvents evs st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64)
          (chainGAfter x.c k).keys ∗
          c3mkChainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
          (x.ptr ↦ₛ pfx) ∗ savedRest))
      (fun s4 P4 => ∃ evs_step : List AllocEvent,
        ChainPrefixEnv x.c (k + 1) (evs ++ evs_step) ∧
        s4.sp = s0.sp - 240#64 ∧ LibsignalCodeLoaded lsmpl s4.mem ∧
        s4.trace = s0.trace ∧ Chain3MkRegs s s4 ∧
        (P4 ⊢ chain3GAt A.repAlloc x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            ((x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail) ∗
          A.pool lim (M.stepEvents (evs ++ evs_step) st) s4 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      (fun _ _ => False) := by
    refine SepWPp.bind_lscro (mid := chain3PCPlacedAtW ext 580#64)
      (Q1 := fun s2 P2 => s2.sp = s0.sp - 240#64 ∧ LibsignalCodeLoaded lsmpl s2.mem ∧
        s2.trace = s0.trace ∧ s2.readReg64 .x25 = BitVec.ofNat 64 rest.length ∧
        Chain3MkRegs s s2 ∧
        (P2 ⊢ ((x.bufRef ↦₆₄ x.slot) ∗ vecU8At A.repAlloc (s0.sp - 160#64) 0#64 1#64 [] ∗
          sliceCursorAt x.slot
            (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
              BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length)
            (pbBytes 5 mk.seed ++ rest) ∗
          A.pool lim (M.stepEvents evs st) s2 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          (vecU8 A.repAlloc (s0.sp - 232#64) [] ∗ vecU8 A.repAlloc (s0.sp - 208#64) [] ∗
            vecU8 A.repAlloc (s0.sp - 184#64) [] ∗
            ((s0.sp - 136#64) ↦₃₂ mk.counter) ∗ memRegion (s0.sp - 132#64) 4 ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ pbVarint 1 mk.counter.toNat) ∗
            vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64)
              (chainGAfter x.c k).keys ∗
            c3mkChainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
            (x.ptr ↦ₛ pfx) ∗ savedRest))) hcro ?_ ?_
    · refine step_mkHead_cro hC x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
        s0.sp body rest x.tail hmk_lt htail_le hlen_a hpc hrun hsp halign hcl htr
        hx19 hx21 hx22 hx23 ?_
      intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hx25_1 hregs1
      dsimp only [body]
      rw [List.append_assoc (pbVarint 1 mk.counter.toNat) (pbBytes 5 mk.seed) rest]
      refine sepWPp_mono_pre_c3
        (P' := ((x.bufRef ↦₆₄ x.slot) ∗ ((s0.sp - 136#64) ↦₃₂ 0#32) ∗
          sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length + 2#64)
            (pbVarint 1 mk.counter.toNat ++ (pbBytes 5 mk.seed ++ rest)) ∗
          A.pool lim (M.stepEvents evs st) s1 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          (vecU8 A.repAlloc (s0.sp - 232#64) [] ∗ vecU8 A.repAlloc (s0.sp - 208#64) [] ∗
            vecU8 A.repAlloc (s0.sp - 184#64) [] ∗
            vecU8At A.repAlloc (s0.sp - 160#64) 0#64 1#64 [] ∗
            memRegion (s0.sp - 132#64) 4 ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
            vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64)
              (chainGAfter x.c k).keys ∗
            c3mkChainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
            (x.ptr ↦ₛ pfx) ∗ savedRest))
        (by dsimp only [body]; exact sep_ac_seedChain (by ac_rfl)) ?_
      refine step_mkCnt_cro hC x.bufRef x.slot
        (x.ptr + BitVec.ofNat 64 pfx.length + 2#64) s0.sp mk.counter (pbBytes 5 mk.seed) rest
        hlen_b hpc1 hrun1 hsp1 halign hcl1 htr1 (hregs1.1.trans hx19) hx25_1 ?_
      intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hx25_2 hregs2
      refine SepWPp.done hpc2 hrun2 ⟨hsp2, hcl2, htr2, hx25_2, hregs1.trans hregs2, ?_⟩
      exact sep_ac_seedChain (by ac_rfl)
    · intro s2 P2 hpc2 hrun2 hcro2 ⟨hsp2, hcl2, htr2, hx25_2, hregs12, hent2⟩
      refine sepWPp_mono_pre_c3 hent2 ?_
      refine step_mkSeed_cro hC x.bufRef x.slot
        (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
          BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length)
        s0.sp mk.seed rest hk_lt hlen_c hfit_seed hcro2 hpc2 hrun2 hsp2 halign hcl2 htr2
        (hregs12.1.trans hx19) (hregs12.2.2.2.1.trans hx22) hx25_2 ?_
      intro s3 evs_bm hpc3 hrun3 hsp3 hcl3 htr3 hx25_3 hregs3 hevs_bm
      have hregs13 : Chain3MkRegs s s3 := hregs12.trans hregs3
      have hevs_bm' : BoundedRustEvs 3 (256 * (x.c.payload.length + 16)) evs_bm :=
        BoundedRustEvs.mono (Nat.le_refl 3) (by omega) hevs_bm
      have hfit_push : FitsEnv M lim (M.stepEvents evs_bm (M.stepEvents evs st))
          (BoundedRustEvs 1 (256 * (x.c.payload.length + 16))) :=
        fitsEnv_step_boundedRustEvs hevs_bm' (by omega) (Nat.le_refl _) (Nat.le_refl _) hFitRem
      let ptrAfterSeed : BitVec 64 :=
        x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
          BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length +
          BitVec.ofNat 64 (pbBytes 5 mk.seed).length
      refine sepWPp_mono_pre_c3
        (P' := ((x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot ptrAfterSeed rest ∗
          vecOf A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b) (x.a + 48#64)
            (chainGAfter x.c k).keys ∗
          prostMsgKeyAt A.repAlloc mk (s0.sp - 232#64) ∗
          A.pool lim (M.stepEvents evs_bm (M.stepEvents evs st)) s3 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          (((x.ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ pbVarint 1 mk.counter.toNat) ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
              BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length) ↦ₛ pbBytes 5 mk.seed) ∗
            c3mkChainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
            (x.ptr ↦ₛ pfx) ∗ savedRest))
        (by
          rw [← @c3mk_prostMsgKeyAt_fold A.repAlloc s0.sp mk]
          dsimp only [ptrAfterSeed]
          exact sep_ac_seedChain (by ac_rfl)) ?_
      refine step_mkPush_cro hC x.a x.bufRef x.slot ptrAfterSeed s0.sp
        (chainGAfter x.c k).keys mk rest x.c.payload.length hkeys_le_pay hbound hfit_push
        hpc3 hrun3 hsp3 halign hcl3 htr3
        (hregs13.1.trans hx19) (hregs13.2.1.trans hx20) (hregs13.2.2.2.2.2.1.trans hx24) hx25_3 ?_
      intro s4 evs_grow hpc4 hrun4 hsp4 hcl4 htr4 hregs4 hevs_grow
      have hregs : Chain3MkRegs s s4 := hregs13.trans hregs4
      have hstep_evs : BoundedRustEvs (8 * (x.c.fields[k]'hk).enc.length)
          (256 * (x.c.payload.length + 16)) (evs_bm ++ evs_grow) := by
        have happ := BoundedRustEvs.append hevs_bm' hevs_grow
        rw [Nat.max_self] at happ
        exact BoundedRustEvs.mono (by omega) (Nat.le_refl _) happ
      have hevs_next : ChainPrefixEnv x.c (k + 1) (evs ++ (evs_bm ++ evs_grow)) :=
        chainPrefixEnv_step_field hk hevs_pfx hstep_evs
      refine SepWPp.done hpc4 hrun4
        ⟨evs_bm ++ evs_grow, hevs_next, hsp4, hcl4, htr4, hregs, ?_⟩
      rw [chainGAfter_succ_of_key hk hfl, chain3GAt_push_key, chain3SavedRegs_c3mk_split,
        ← sliceCursorAfter_tag4_combine x.slot x.ptr (x.c.payload ++ x.tail) pfx
          (pbVarint 1 mk.counter.toNat) (pbBytes 5 mk.seed) rest hpay_eq,
        ← M.stepEvents_append evs_bm evs_grow (M.stepEvents evs st),
        ← M.stepEvents_append evs (evs_bm ++ evs_grow) st]
      dsimp only [body, savedRest, ptrAfterSeed, rest]
      exact sep_ac_seedChain (by ac_rfl)
  obtain ⟨s4, hsteps, hex⟩ := hwp R hmem_init hL
  rcases hex with ⟨hpc4, hrun4, P4, hm4, evs_step, hevs_next, hsp4, hcl4, htr4, hregs, hent4⟩ |
    ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · have hal4 : s4.spAligned = true := by simp only [State.spAligned, hsp4, ← hsp]; exact hal
    have hmem4 := Satisfies.mono (sepConj_mono_left hent4) hm4
    simp only [sepConj_assoc] at hmem4
    exact ⟨s4, hsteps, Or.inl ⟨hpc4, hrun4, htr4, hregs.2.2.2.2.2.2.2.2.2.2.trans hvregs,
      hcl4, hsp4, hal4, hregs.2.2.2.2.2.2.2.2.2.1.trans hx29, hregs.1.trans hx19,
      hregs.2.1.trans hx20, hregs.2.2.1.trans hx21, hregs.2.2.2.1.trans hx22,
      hregs.2.2.2.2.1.trans hx23, hregs.2.2.2.2.2.1.trans hx24,
      hregs.2.2.2.2.2.2.1.trans hx26, hregs.2.2.2.2.2.2.2.1.trans hx27,
      hregs.2.2.2.2.2.2.2.2.1.trans hx28, hOk, hlen_pay, hfit,
      evs ++ evs_step, hevs_next, hmem4⟩⟩
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Top-Level Block-`516` Closure and `ChainMerge5CroPlacedOkExt` -/

private theorem chainMerge3RawSpecW_eq_top {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Chain3CroAPlacedBudgetAux.chainMerge3RawSpecW M A lim =
      TopPlacedBudgetAux.chainMerge3RawSpecW A lim := by
  unfold Chain3CroAPlacedBudgetAux.chainMerge3RawSpecW TopPlacedBudgetAux.chainMerge3RawSpecW
  rfl

/-- `message::merge<Chain> [local#4]` (Block `516`) on `lsProg_516 (Rust.withPanics ext)` under `StoreKit.withLsCodeRoLoaded`, discharged from the 6 budget hooks on `ext`. -/
theorem chainMerge3W_cro_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (Chain3CroAPlacedBudgetAux.chainMerge3RawSpecW M A lim)) :=
  chainMerge3W_cro_placed_ok ext
    (chain3CalleesCro_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_raw)
    (chain3Entry_cro_placed_ok ext)
    (chain3Srk_cro_placed_ok ext)
    (chain3ChainKey_cro_placed_ok ext)
    (chain3MessageKeys_cro_placed_ok ext)

/-- Cross-block `message::merge<Chain> [local#4]` (Block `516`) under `StoreKit.withLsCodeRoLoaded` on any `callerProg` over `ext`, discharged from the 6 budget hooks on `ext`. -/
theorem chainMerge5_cro_of_block_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk ext]
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok callerProg (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (Chain3CroAPlacedBudgetAux.chainMerge3RawSpecW M A lim)) :=
  chainMerge5_cro_of_block
    (chainMerge3W_cro_placed_ok_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem chainMerge5CroPlacedOkExt_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    ChainMerge5CroPlacedOkExt A lim ext := by
  unfold ChainMerge5CroPlacedOkExt
  rw [← chainMerge3RawSpecW_eq_top A lim]
  exact chainMerge5_cro_of_block_hooks (callerProg := lsProg_518 ext)
    hshim halloc hrealloc hdealloc hmc hpanic_raw

private theorem cli_noAllocShim_sat (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (hShim : gh.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec :=
  (show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
    ⟨hookNoop, (cliGhostExterns_shim gh (cliExternsPlaced mmpl W)).trans (congrArg some hShim),
      noAllocShim_hookOk⟩

private theorem cli_framelessMemcpy_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMemcpySym
      framelessMemcpyBudgetSpec := by
  have h : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMemcpySym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec) :=
    (show ("memcpy" : String) = lsMemcpySym by decide) ▸
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_framelessMemcpy_budget_sat
        mmpl gh W hA
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

theorem chainMerge5_cro_cli_of_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok callerProg (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (TopPlacedBudgetAux.chainMerge3RawSpecW A lim)) := by
  rw [← chainMerge3RawSpecW_eq_top A lim]
  exact chainMerge5_cro_of_block_hooks (cli_noAllocShim_sat mmpl gh W hA.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hA)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hA)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hA)
    (cli_framelessMemcpy_sat mmpl gh W hA)
    (cliGhostExterns_panic_handle_error mmpl gh W)

theorem chainMerge5_cro_of_block_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W))]
    (hA : CliAllocHooks A lim) :
    subroutine_ok callerProg (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (TopPlacedBudgetAux.chainMerge3RawSpecW A lim)) :=
  chainMerge5_cro_cli_of_block mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem chainMerge5CroPlacedOkExt_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    ChainMerge5CroPlacedOkExt A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  chainMerge5CroPlacedOkExt_of_hooks (cli_noAllocShim_sat mmpl gh W hA.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hA)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hA)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hA)
    (cli_framelessMemcpy_sat mmpl gh W hA)
    (cliGhostExterns_panic_handle_error mmpl gh W)

theorem chainMerge5CroPlacedOkExt_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim) :
    ChainMerge5CroPlacedOkExt A lim (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W)) :=
  chainMerge5CroPlacedOkExt_cli mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem overPrevDecode_cro_placed_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hmemmove : HookSat ext "memmove" (sessionMemmoveBudgetSpec extHookStack))
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    OverPrevDecodeCroPlacedAt A lim ext :=
  overPrevDecode_cro_placed_of_hooks_chain5
    hshim halloc hrealloc hdealloc hmc hmemmove hpanic_raw
    (chainMerge5CroPlacedOkExt_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem overPrevDecode_cro_placed_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    OverPrevDecodeCroPlacedAt A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  overPrevDecode_cro_placed_of_hooks (cli_noAllocShim_sat mmpl gh W hA.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hA)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hA)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hA)
    (cli_framelessMemcpy_sat mmpl gh W hA)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack))
    (cliGhostExterns_panic_handle_error mmpl gh W)

theorem overPrevDecode_cro_placed_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim) :
    OverPrevDecodeCroPlacedAt A lim (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W)) :=
  overPrevDecode_cro_placed_cli mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudget
